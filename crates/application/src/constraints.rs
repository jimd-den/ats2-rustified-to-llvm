//! # The constraint checker — the half of ATS that is not code
//!
//! *Literate note.*  A dependent type is a claim, and a claim nobody
//! checks is a comment.  `fun fact {n:nat} (x: int n): int` promises that
//! `fact` is never called on a negative number; this module is what
//! turns that promise into something the compiler can refuse to believe.
//!
//! The language of claims here is linear arithmetic over the integers,
//! which is what the corpus actually indexes with: sizes, lengths,
//! bounds, and the occasional product.  Three deliberate choices keep it
//! honest:
//!
//! * **Rational refutation, integer strengthening.**  A goal is proved by
//!   showing its negation unsatisfiable, using Fourier–Motzkin
//!   elimination over the rationals.  Rational unsatisfiability implies
//!   integer unsatisfiability, so every proof is sound.  Strict
//!   inequalities are tightened first (`n > 0` becomes `n >= 1`), which
//!   recovers most of what integrality buys.
//! * **Nonlinearity is abstracted, never guessed.**  `m*n` becomes an
//!   opaque variable — the same one every time it appears — so a claim
//!   that only needs it to be itself still goes through, and one that
//!   needs to know its value does not.
//! * **Three verdicts, not two.**  Anything outside the fragment is
//!   `Unknown`, never a failure.  A checker that rejects what it merely
//!   fails to understand is a checker people turn off.

use std::collections::{BTreeMap, HashMap};

use ats2_domain::ast::{BinOp, Def, Expr, FunDef, Program};
use ats2_domain::errors::CompileError;
use ats2_domain::statics::{Quant, SExp};

/// What the checker was able to establish.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// The hypotheses entail the goal.
    Proved,
    /// The hypotheses entail its *negation*: the claim is definitely false.
    Refuted,
    /// Outside the fragment, or simply undecided.  Not an error.
    Unknown,
}

/// A linear form `sum(coeff * var) + constant`, read as `>= 0`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Linear {
    terms: BTreeMap<String, i64>,
    konst: i64,
}

impl Linear {
    fn constant(k: i64) -> Linear {
        Linear { terms: BTreeMap::new(), konst: k }
    }

    fn var(name: String) -> Linear {
        let mut terms = BTreeMap::new();
        terms.insert(name, 1);
        Linear { terms, konst: 0 }
    }

    fn scale(&self, k: i64) -> Linear {
        Linear {
            terms: self.terms.iter().map(|(v, c)| (v.clone(), c * k)).collect(),
            konst: self.konst * k,
        }
    }

    fn add(&self, other: &Linear) -> Linear {
        let mut terms = self.terms.clone();
        for (v, c) in &other.terms {
            let e = terms.entry(v.clone()).or_insert(0);
            *e += c;
            if *e == 0 {
                terms.remove(v);
            }
        }
        Linear { terms, konst: self.konst + other.konst }
    }

    fn sub(&self, other: &Linear) -> Linear {
        self.add(&other.scale(-1))
    }

    fn coeff(&self, var: &str) -> i64 {
        self.terms.get(var).copied().unwrap_or(0)
    }

    /// `>= 0` with no variables left: either trivially true or false.
    fn is_false_constant(&self) -> bool {
        self.terms.is_empty() && self.konst < 0
    }
}

/// Read a static term as a linear form, abstracting what it cannot read.
///
/// `abstracted` is shared across every term in one query so that the
/// same opaque subterm gets the same variable — that consistency is the
/// whole value of the abstraction.
fn linearize(e: &SExp) -> Option<Linear> {
    match e {
        SExp::IntLit(n) => Some(Linear::constant(*n)),
        SExp::Var(n) => Some(Linear::var(n.clone())),
        SExp::BoolLit(_) => None,
        SExp::App(op, args) => match (op.as_str(), args.len()) {
            ("+", 2) => Some(linearize(&args[0])?.add(&linearize(&args[1])?)),
            ("-", 2) => Some(linearize(&args[0])?.sub(&linearize(&args[1])?)),
            ("~", 1) => Some(linearize(&args[0])?.scale(-1)),
            ("*", 2) => {
                let l = linearize(&args[0]);
                let r = linearize(&args[1]);
                match (l, r) {
                    // A product with a constant side stays linear.
                    (Some(a), Some(b)) if a.terms.is_empty() => Some(b.scale(a.konst)),
                    (Some(a), Some(b)) if b.terms.is_empty() => Some(a.scale(b.konst)),
                    // Anything else is opaque, but *stably* opaque.
                    _ => Some(Linear::var(opaque_name(e))),
                }
            }
            _ => Some(Linear::var(opaque_name(e))),
        },
    }
}

/// The name an unreadable subterm is abstracted to.
///
/// Derived from the term's own printed form, so two occurrences of
/// `m*n` abstract to one variable and `m*n` and `n*m` do not — which is
/// a loss of strength, never of soundness.
fn opaque_name(e: &SExp) -> String {
    format!("#{e}")
}

/// A conjunction of `Linear >= 0` atoms, or `None` if the proposition
/// falls outside the fragment.
fn atoms(e: &SExp) -> Option<Vec<Linear>> {
    let SExp::App(op, args) = e else { return None };
    match (op.as_str(), args.len()) {
        ("&&", 2) => {
            let mut out = atoms(&args[0])?;
            out.extend(atoms(&args[1])?);
            Some(out)
        }
        (">=", 2) => Some(vec![linearize(&args[0])?.sub(&linearize(&args[1])?)]),
        // Over the integers `a > b` is `a - b - 1 >= 0`.  Tightening
        // here is what lets the rational elimination below decide goals
        // that are only true because the variables are whole numbers.
        (">", 2) => {
            Some(vec![linearize(&args[0])?.sub(&linearize(&args[1])?).add(&Linear::constant(-1))])
        }
        ("<=", 2) => Some(vec![linearize(&args[1])?.sub(&linearize(&args[0])?)]),
        ("<", 2) => {
            Some(vec![linearize(&args[1])?.sub(&linearize(&args[0])?).add(&Linear::constant(-1))])
        }
        ("==", 2) | ("=", 2) => {
            let d = linearize(&args[0])?.sub(&linearize(&args[1])?);
            Some(vec![d.clone(), d.scale(-1)])
        }
        // `!=` and `||` are disjunctions, which a conjunctive system
        // cannot hold.  Dropping them costs strength, not soundness.
        _ => None,
    }
}

/// The negations of a proposition, as alternatives.
///
/// `¬(A ∧ B)` is `¬A ∨ ¬B`, so a conjunction negates to several
/// single-atom systems, each of which must be refuted separately.
fn negations(e: &SExp) -> Option<Vec<Linear>> {
    // `¬(L >= 0)` is `L <= -1`, i.e. `-L - 1 >= 0`.
    Some(atoms(e)?.into_iter().map(|l| l.scale(-1).add(&Linear::constant(-1))).collect())
}

/// Whether a system of `>= 0` constraints has no rational solution.
///
/// Fourier–Motzkin: eliminate one variable at a time by combining every
/// lower bound with every upper bound.  The combination count can grow
/// quadratically per variable, so it is capped — an exhausted budget
/// reports "satisfiable as far as we know", which keeps the caller's
/// verdict `Unknown` rather than inventing a proof.
fn is_unsatisfiable(system: &[Linear]) -> bool {
    const BUDGET: usize = 4000;
    let mut system: Vec<Linear> = system.to_vec();
    loop {
        if system.iter().any(Linear::is_false_constant) {
            return true;
        }
        let Some(var) = system.iter().flat_map(|l| l.terms.keys()).next().cloned() else {
            return false;
        };
        let mut zero = Vec::new();
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for l in &system {
            match l.coeff(&var) {
                0 => zero.push(l.clone()),
                c if c > 0 => pos.push(l.clone()),
                _ => neg.push(l.clone()),
            }
        }
        if pos.len() * neg.len() > BUDGET {
            return false;
        }
        let mut next = zero;
        for p in &pos {
            for n in &neg {
                // Scale both so the variable cancels exactly.
                let a = p.coeff(&var);
                let b = -n.coeff(&var);
                next.push(p.scale(b).add(&n.scale(a)));
            }
        }
        if next.len() > BUDGET {
            return false;
        }
        system = next;
    }
}

/// Whether the hypotheses are jointly impossible.
///
/// Worth asking on its own: a branch whose hypotheses contradict is a
/// branch that cannot run, and reporting that is more useful than
/// silently proving every claim inside it.
pub fn is_contradictory(hyps: &[SExp]) -> bool {
    let mut system = Vec::new();
    for h in hyps {
        match atoms(h) {
            Some(a) => system.extend(a),
            None => continue,
        }
    }
    is_unsatisfiable(&system)
}

/// Does `hyps` entail `goal`?
pub fn entails(hyps: &[SExp], goal: &SExp) -> Verdict {
    let mut base = Vec::new();
    for h in hyps {
        if let Some(a) = atoms(h) {
            base.extend(a);
        }
    }
    let Some(goal_atoms) = atoms(goal) else { return Verdict::Unknown };
    let Some(negated) = negations(goal) else { return Verdict::Unknown };

    // Proved when every way of denying the goal is impossible.
    let proved = negated.iter().all(|n| {
        let mut sys = base.clone();
        sys.push(n.clone());
        is_unsatisfiable(&sys)
    });
    if proved {
        return Verdict::Proved;
    }
    // Refuted when asserting the goal is itself impossible.
    let mut with_goal = base;
    with_goal.extend(goal_atoms);
    if is_unsatisfiable(&with_goal) {
        return Verdict::Refuted;
    }
    Verdict::Unknown
}

/// Check every call in a program against the promises its callee's
/// signature makes.
///
/// The walk is deliberately one-sided.  An index it cannot infer is not
/// an error — most arguments in real code have indices that depend on
/// facts a branch established, and this checker does not yet read
/// branches.  Only a call whose violation is *provable* is reported, so
/// turning the checker on cannot reject a program that was correct.
pub fn check_program(program: &Program) -> Vec<CompileError> {
    let mut sigs: HashMap<&str, &FunDef> = HashMap::new();
    for def in program.defs() {
        if let Def::Fun(f) = def {
            sigs.insert(f.name.as_str(), f);
        }
    }
    let mut out = Vec::new();
    for def in program.defs() {
        // `implement main0 () = ...` is a body like any other, and it is
        // where a program's outermost calls are written, so leaving it
        // unchecked would leave the common case unchecked.
        let (universals, params, body) = match def {
            Def::Fun(f) => (f.universals.as_slice(), f.params.as_slice(), &f.body),
            Def::Implement(im) => (&[][..], im.params.as_slice(), &im.body),
            _ => continue,
        };
        // What this body may assume: whatever its own signature demands
        // of its callers.
        let hyps: Vec<SExp> = universals.iter().flat_map(Quant::hypotheses).collect();
        // What each parameter's index is called.
        let mut env: HashMap<String, SExp> = HashMap::new();
        for p in params {
            if let [idx] = p.ty.indices() {
                env.insert(p.name.clone(), idx.clone());
            }
        }
        check_expr(body, &env, &hyps, &sigs, &mut out);
    }
    out
}

/// The static term an expression's value is known to equal, if any.
fn index_of(e: &Expr, env: &HashMap<String, SExp>) -> Option<SExp> {
    Some(match e {
        Expr::IntLit(n) => SExp::IntLit(*n),
        Expr::Var(n) => env.get(n)?.clone(),
        Expr::UnaryNeg(x) => SExp::App("~".into(), vec![index_of(x, env)?]),
        Expr::BinOp(op, l, r) => SExp::App(
            match op {
                BinOp::Add => "+",
                BinOp::Sub => "-",
                BinOp::Mul => "*",
                BinOp::Div => "/",
                BinOp::Mod => "%",
                _ => return None,
            }
            .into(),
            vec![index_of(l, env)?, index_of(r, env)?],
        ),
        _ => return None,
    })
}

fn check_expr(
    e: &Expr,
    env: &HashMap<String, SExp>,
    hyps: &[SExp],
    sigs: &HashMap<&str, &FunDef>,
    out: &mut Vec<CompileError>,
) {
    if let Expr::Call(callee, args) = e {
        if let Expr::Var(name) = &**callee {
            if let Some(target) = sigs.get(name.as_str()) {
                check_call(name, target, args, env, hyps, out);
            }
        }
    }
    e.each_subexpr(&mut |sub| check_expr(sub, env, hyps, sigs, out));
}

/// One call, against one signature.
fn check_call(
    name: &str,
    target: &FunDef,
    args: &[Expr],
    env: &HashMap<String, SExp>,
    hyps: &[SExp],
    out: &mut Vec<CompileError>,
) {
    // Instantiate the callee's static variables from the arguments.  A
    // parameter indexed by a bare variable pins that variable to the
    // argument's index; a more elaborate index would need unification,
    // which this checker does not attempt.
    let mut subst: Vec<(String, SExp)> = Vec::new();
    for (p, a) in target.params.iter().zip(args) {
        let [SExp::Var(sv)] = p.ty.indices() else { continue };
        let Some(idx) = index_of(a, env) else { continue };
        subst.push((sv.clone(), idx));
    }
    if subst.is_empty() {
        return;
    }
    for q in &target.universals {
        for h in q.hypotheses() {
            // Only obligations whose variables the call actually pinned
            // down can be judged.
            if h.vars().iter().any(|v| !subst.iter().any(|(k, _)| k == v)) {
                continue;
            }
            let goal = h.substitute(&subst);
            if entails(hyps, &goal) == Verdict::Refuted {
                out.push(CompileError::check(format!(
                    "`{name}` accepts only arguments for which `{h}` holds, and this call needs `{goal}`, which is false"
                )));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ats2_domain::ast::{BinOp, Def, Expr, FunDef, Param, Ty};
    use ats2_domain::statics::{Quant, SExp, Sort};

    fn v(n: &str) -> SExp { SExp::Var(n.into()) }
    fn i(n: i64) -> SExp { SExp::IntLit(n) }
    fn app(op: &str, a: SExp, b: SExp) -> SExp { SExp::App(op.into(), vec![a, b]) }

    #[test]
    fn a_goal_that_follows_from_the_hypotheses_is_proved() {
        // n >= 0  ⊢  n + 1 > 0
        let hyps = vec![app(">=", v("n"), i(0))];
        let goal = app(">", app("+", v("n"), i(1)), i(0));
        assert_eq!(entails(&hyps, &goal), Verdict::Proved);
    }

    #[test]
    fn a_goal_the_hypotheses_contradict_is_refuted() {
        // n > 0  ⊢  n - 1 < 0   is false for every n
        let hyps = vec![app(">", v("n"), i(0))];
        let goal = app("<", app("-", v("n"), i(1)), i(0));
        assert_eq!(entails(&hyps, &goal), Verdict::Refuted);
    }

    #[test]
    fn integrality_is_used_not_just_rational_bounds() {
        // n > 0 means n >= 1 over the integers, so n >= 1 follows.
        let hyps = vec![app(">", v("n"), i(0))];
        assert_eq!(entails(&hyps, &app(">=", v("n"), i(1))), Verdict::Proved);
    }

    #[test]
    fn an_undecided_goal_is_reported_as_unknown_rather_than_guessed() {
        let hyps = vec![app(">=", v("n"), i(0))];
        assert_eq!(entails(&hyps, &app(">", v("n"), i(3))), Verdict::Unknown);
    }

    #[test]
    fn a_conjunction_is_proved_only_when_both_halves_are() {
        let hyps = vec![app(">", v("n"), i(2))];
        let both = app("&&", app(">", v("n"), i(0)), app(">", v("n"), i(1)));
        assert_eq!(entails(&hyps, &both), Verdict::Proved);
        let mixed = app("&&", app(">", v("n"), i(0)), app(">", v("n"), i(9)));
        assert_eq!(entails(&hyps, &mixed), Verdict::Unknown);
    }

    #[test]
    fn a_nonlinear_term_is_abstracted_rather_than_misread() {
        // m*n is opaque, but it is *consistently* opaque, so a goal that
        // only needs it to equal itself still goes through.
        let hyps = vec![app(">=", app("*", v("m"), v("n")), i(0))];
        let goal = app(">=", app("+", app("*", v("m"), v("n")), i(1)), i(0));
        assert_eq!(entails(&hyps, &goal), Verdict::Proved);
    }

    #[test]
    fn a_form_outside_the_fragment_is_unknown_not_an_error() {
        let hyps = vec![];
        assert_eq!(entails(&hyps, &app("!=", v("n"), i(0))), Verdict::Unknown);
    }

    fn errors_for(src_defs: Vec<ats2_domain::ast::Def>) -> Vec<String> {
        let p = ats2_domain::ast::Program::new(src_defs);
        check_program(&p).into_iter().map(|e| e.message).collect()
    }

    /// `fun f {n:nat} (x: int n): int`
    fn nat_taking_fn(name: &str, body: Expr) -> Def {
        Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![Quant { vars: vec![("n".into(), Sort::Nat)], guard: None }],
            existentials: vec![],
            name: name.into(),
            params: vec![Param {
                name: "x".into(),
                ty: Ty::Index(Box::new(Ty::Name("int".into())), vec![v("n")]),
            }],
            ret: Ty::Name("int".into()),
            body,
        })
    }

    #[test]
    fn calling_a_nat_indexed_function_with_a_negative_literal_is_refused() {
        // `f` promises to accept only non-negative arguments; `f(~1)`
        // breaks that promise, and this is the whole reason the static
        // language is kept.
        let caller = Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![],
            existentials: vec![],
            name: "g".into(),
            params: vec![],
            ret: Ty::Name("int".into()),
            body: Expr::Call(Box::new(Expr::Var("f".into())), vec![Expr::IntLit(-1)]),
        });
        let errs = errors_for(vec![nat_taking_fn("f", Expr::IntLit(0)), caller]);
        assert_eq!(errs.len(), 1, "{errs:?}");
        assert!(errs[0].contains("f"), "{errs:?}");
        assert!(errs[0].contains(">= 0"), "{errs:?}");
    }

    #[test]
    fn a_call_that_honours_the_promise_is_accepted() {
        let caller = Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![],
            existentials: vec![],
            name: "g".into(),
            params: vec![],
            ret: Ty::Name("int".into()),
            body: Expr::Call(Box::new(Expr::Var("f".into())), vec![Expr::IntLit(3)]),
        });
        assert!(errors_for(vec![nat_taking_fn("f", Expr::IntLit(0)), caller]).is_empty());
    }

    #[test]
    fn a_call_whose_index_is_not_known_is_left_alone() {
        // The recursive call passes `x - 1`, which is only non-negative
        // when `x > 0` — a fact the checker does not have here.  It must
        // stay silent rather than reject a valid program.
        let f = nat_taking_fn(
            "f",
            Expr::Call(
                Box::new(Expr::Var("f".into())),
                vec![Expr::BinOp(BinOp::Sub, Box::new(Expr::Var("x".into())), Box::new(Expr::IntLit(1)))],
            ),
        );
        assert!(errors_for(vec![f]).is_empty());
    }

    #[test]
    fn contradictory_hypotheses_are_reported_rather_than_proving_everything() {
        // A body reachable only under `n > 0 && n < 0` is dead code, and
        // saying "everything is proved here" would hide that.
        let hyps = vec![app(">", v("n"), i(0)), app("<", v("n"), i(0))];
        assert!(is_contradictory(&hyps));
    }
}
