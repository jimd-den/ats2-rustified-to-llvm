//! # The dependent type checker
//!
//! *Literate note.*  ATS2 is two languages in one file: the dynamic one
//! that runs, and the static one that reasons about what the dynamic one
//! will do.  This module is where the second is taken seriously.  It is
//! composed of four parts that do not know about each other, and the
//! order of that list is the design:
//!
//! 1. [`walk`] reads the program once and writes down every claim it
//!    would have to satisfy — knowing why each claim exists, and nothing
//!    about arithmetic;
//! 2. [`crate::constraints`] decides claims — knowing arithmetic, and
//!    nothing about why;
//! 3. [`policy`] decides what a failure *means* — the one thing a project
//!    changes its mind about;
//! 4. [`signatures`], [`unify`], [`prop`] and [`index_env`] are the
//!    vocabulary the walk is written in.
//!
//! Nothing here is a god object, and that is load-bearing rather than
//! decorative: the solver has been replaced once already and the walk did
//! not notice, and the strictness policy is a two-line module precisely
//! because no rule was allowed to decide for itself what counts as an
//! error.
//!
//! The checker runs between parsing and emission, which is the last
//! moment the static language still exists — emission erases it, by
//! design.

pub mod index_env;
pub mod policy;
pub mod prop;
pub mod signatures;
pub mod unify;
pub mod walk;

use ats2_domain::ast::Program;
use ats2_domain::errors::CompileError;

pub use policy::Strictness;

/// Check a program's static language, and report what it does not
/// justify.
///
/// `ambient` supplies the signatures the program did not write down —
/// the prelude's.  Nearly every claim a real ATS program makes rests on
/// one of them, and a checker that cannot see them can check nothing but
/// toy code.  They contribute *signatures only*: what the prelude does
/// is the prelude's business and is checked when the prelude is.
pub fn check_program(
    program: &Program,
    ambient: &Program,
    policy: Strictness,
) -> Vec<CompileError> {
    policy::discharge(&walk::obligations(program, ambient), policy)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ats2_domain::ast::{BinOp, Def, Expr, FunDef, ImplementDef, Param, Ty};
    use ats2_domain::statics::{Quant, SExp, Sort};

    fn v(n: &str) -> SExp { SExp::Var(n.into()) }
    fn int_of(idx: SExp) -> Ty { Ty::Index(Box::new(Ty::Name("int".into())), vec![idx]) }

    /// `fun name {n:nat} (x: int n): int = 0`, and a `main0` calling it
    /// with `arg`.
    fn program_calling(arg: Expr) -> Program {
        Program::new(vec![
            Def::Fun(FunDef {
                metric: vec![],
                ty_params: vec![],
                universals: vec![Quant { vars: vec![("n".into(), Sort::Nat)], guard: None }],
                existentials: vec![],
                name: "fact".into(),
                params: vec![Param { borrowed: false, name: "x".into(), ty: int_of(v("n")) }],
                ret: Ty::Name("int".into()),
                body: Expr::IntLit(0),
            }),
            Def::Implement(ImplementDef {
                ty_params: vec![],
                instance: vec![],
                name: "main0".into(),
                params: vec![],
                ret: None,
                body: Expr::Call(Box::new(Expr::Var("fact".into())), vec![arg]),
            }),
        ])
    }

    fn messages(program: &Program, policy: Strictness) -> Vec<String> {
        check_program(program, &Program::new(vec![]), policy)
            .into_iter()
            .map(|e| e.message)
            .collect()
    }

    #[test]
    fn calling_a_nat_indexed_function_with_a_negative_literal_is_refused() {
        let program = program_calling(Expr::UnaryNeg(Box::new(Expr::IntLit(1))));
        for policy in [Strictness::Strict, Strictness::Permissive] {
            let errs = messages(&program, policy);
            assert_eq!(errs.len(), 1, "{policy:?}: {errs:?}");
            assert!(errs[0].contains("the call to `fact`"), "{}", errs[0]);
            assert!(errs[0].contains("is false"), "{}", errs[0]);
        }
    }

    #[test]
    fn a_call_that_honours_the_promise_is_accepted() {
        let program = program_calling(Expr::IntLit(5));
        for policy in [Strictness::Strict, Strictness::Permissive] {
            assert!(messages(&program, policy).is_empty(), "{policy:?}");
        }
    }

    #[test]
    fn a_call_whose_index_is_unknown_divides_the_two_policies() {
        // This is the whole reason both policies exist.  `argc` is an
        // integer nobody can bound, so `fact(argc)` is *not* provable —
        // and whether that is an error is a decision, not a fact.
        let program = program_calling(Expr::Call(Box::new(Expr::Var("argc".into())), vec![]));
        assert_eq!(messages(&program, Strictness::Strict).len(), 1);
        assert!(messages(&program, Strictness::Permissive).is_empty());
    }

    #[test]
    fn a_call_proved_from_the_callers_own_promise_is_accepted() {
        // `fun g {m:nat} (y: int m) = fact(y)` — the caller's quantifier
        // is exactly what discharges the callee's.
        let mut defs = program_calling(Expr::IntLit(0)).defs().to_vec();
        defs.push(Def::Fun(FunDef {
            metric: vec![],
            ty_params: vec![],
            universals: vec![Quant { vars: vec![("m".into(), Sort::Nat)], guard: None }],
            existentials: vec![],
            name: "g".into(),
            params: vec![Param { borrowed: false, name: "y".into(), ty: int_of(v("m")) }],
            ret: Ty::Name("int".into()),
            body: Expr::Call(Box::new(Expr::Var("fact".into())), vec![Expr::Var("y".into())]),
        }));
        assert!(messages(&Program::new(defs), Strictness::Strict).is_empty());
    }

    #[test]
    fn a_guard_a_branch_established_discharges_the_call_inside_it() {
        // `if x > 0 then fact(x-1) else 0` is the shape of every
        // recursion over `nat`, and it must go through without help.
        let x = Expr::Var("x".into());
        let body = Expr::IfThenElse(
            Box::new(Expr::BinOp(BinOp::Gt, Box::new(x.clone()), Box::new(Expr::IntLit(0)))),
            Box::new(Expr::Call(
                Box::new(Expr::Var("fact".into())),
                vec![Expr::BinOp(BinOp::Sub, Box::new(x), Box::new(Expr::IntLit(1)))],
            )),
            Box::new(Expr::IntLit(0)),
        );
        let mut defs = program_calling(Expr::IntLit(0)).defs().to_vec();
        defs.push(Def::Fun(FunDef {
            metric: vec![],
            ty_params: vec![],
            universals: vec![Quant { vars: vec![("k".into(), Sort::Nat)], guard: None }],
            existentials: vec![],
            name: "rec".into(),
            params: vec![Param { borrowed: false, name: "x".into(), ty: int_of(v("k")) }],
            ret: Ty::Name("int".into()),
            body,
        }));
        assert!(messages(&Program::new(defs), Strictness::Strict).is_empty());
    }

    #[test]
    fn an_existential_result_is_witnessed_differently_in_each_branch() {
        // `fun abs {n:int} (x: int n): [r:nat] int r = if x >= 0 then x
        // else ~x` is the smallest program that needs everything at once:
        // the promise pushed into both arms, each arm's guard in force,
        // and the existential witnessed by a *different* term in each.
        // Joining the arms first makes it unprovable; so does forgetting
        // the guard; so does demanding one witness for both.
        let x = Expr::Var("x".into());
        let body = Expr::IfThenElse(
            Box::new(Expr::BinOp(BinOp::Ge, Box::new(x.clone()), Box::new(Expr::IntLit(0)))),
            Box::new(x.clone()),
            Box::new(Expr::UnaryNeg(Box::new(x))),
        );
        let program = Program::new(vec![Def::Fun(FunDef {
            metric: vec![],
            ty_params: vec![],
            universals: vec![Quant { vars: vec![("n".into(), Sort::Int)], guard: None }],
            existentials: vec![Quant { vars: vec![("r".into(), Sort::Nat)], guard: None }],
            name: "abs".into(),
            params: vec![Param { borrowed: false, name: "x".into(), ty: int_of(v("n")) }],
            ret: int_of(v("r")),
            body,
        })]);
        assert!(messages(&program, Strictness::Strict).is_empty(), "{:?}", messages(&program, Strictness::Strict));
    }

    #[test]
    fn an_existential_a_branch_does_not_honour_is_still_caught() {
        // The same shape, with the negation dropped: the else-branch
        // returns a negative number and promises a `nat`.
        let x = Expr::Var("x".into());
        let body = Expr::IfThenElse(
            Box::new(Expr::BinOp(BinOp::Ge, Box::new(x.clone()), Box::new(Expr::IntLit(0)))),
            Box::new(x.clone()),
            Box::new(x),
        );
        let program = Program::new(vec![Def::Fun(FunDef {
            metric: vec![],
            ty_params: vec![],
            universals: vec![Quant { vars: vec![("n".into(), Sort::Int)], guard: None }],
            existentials: vec![Quant { vars: vec![("r".into(), Sort::Nat)], guard: None }],
            name: "bad_abs".into(),
            params: vec![Param { borrowed: false, name: "x".into(), ty: int_of(v("n")) }],
            ret: int_of(v("r")),
            body,
        })]);
        let errs = messages(&program, Strictness::Strict);
        assert_eq!(errs.len(), 1, "{errs:?}");
        assert!(errs[0].contains("the result of `bad_abs`"), "{}", errs[0]);
        assert!(errs[0].contains("is false"), "{}", errs[0]);
    }

    #[test]
    fn contradictory_hypotheses_are_reported_rather_than_proving_everything() {
        // `fun f {n:int | n > 5 && n < 2}` describes no integer at all.
        // Every call into it would "succeed", which is worse than useless.
        let guard = SExp::App(
            "&&".into(),
            vec![
                SExp::App(">".into(), vec![v("n"), SExp::IntLit(5)]),
                SExp::App("<".into(), vec![v("n"), SExp::IntLit(2)]),
            ],
        );
        let program = Program::new(vec![Def::Fun(FunDef {
            metric: vec![],
            ty_params: vec![],
            universals: vec![Quant { vars: vec![("n".into(), Sort::Int)], guard: Some(guard) }],
            existentials: vec![],
            name: "impossible".into(),
            params: vec![Param { borrowed: false, name: "x".into(), ty: int_of(v("n")) }],
            ret: int_of(v("n")),
            body: Expr::Var("x".into()),
        })]);
        let errs = messages(&program, Strictness::Strict);
        assert!(errs.iter().any(|e| e.contains("cannot be reached")), "{errs:?}");
    }

    #[test]
    fn the_default_policy_is_the_one_that_actually_checks() {
        assert_eq!(Strictness::default(), Strictness::Strict);
    }
}
