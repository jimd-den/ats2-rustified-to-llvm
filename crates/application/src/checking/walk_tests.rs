use std::collections::HashMap;
use super::index_env::IndexEnv;
use super::signatures::{CtorTable, SigTable};
use super::walk::*;
use ats2_domain::ast::*;
use ats2_domain::obligation::{Obligation, Origin};
use ats2_domain::statics::{Quant, SExp, Sort};

    fn v(n: &str) -> SExp {
        SExp::Var(n.into())
    }
    fn i(n: i64) -> SExp {
        SExp::IntLit(n)
    }
    fn app(op: &str, a: SExp, b: SExp) -> SExp {
        SExp::App(op.into(), vec![a, b])
    }
    fn int_of(idx: SExp) -> Ty {
        Ty::Index(Box::new(Ty::Name("int".into())), vec![idx])
    }
    fn var(n: &str) -> Expr {
        Expr::Var(n.into())
    }
    fn call(f: &str, args: Vec<Expr>) -> Expr {
        Expr::Call(Box::new(var(f)), args)
    }
    fn nat() -> Quant {
        Quant {
            vars: vec![("n".into(), Sort::Nat)],
            guard: None,
        }
    }

    /// `fun f {n:nat} (x: int n): <ret> = <body>`
    fn fun(name: &str, quants: Vec<Quant>, params: Vec<Param>, ret: Ty, body: Expr) -> Def {
        Def::Fun(FunDef {
            metric: vec![],
            ty_params: vec![],
            universals: quants,
            existentials: vec![],
            name: name.into(),
            params,
            ret,
            body,
            proof: false,
        })
    }

    fn p(name: &str, ty: Ty) -> Param {
        Param {
            name: name.into(),
            ty,
            borrowed: false,
        }
    }

    /// A `nat`-demanding function, and a `main0` whose body is `body`.
    fn with_main(body: Expr) -> Program {
        Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            Def::Implement(ImplementDef {
                ty_params: vec![],
                instance: vec![],
                name: "main0".into(),
                params: vec![],
                ret: None,
                body,
            }),
        ])
    }

    fn goals(program: &Program) -> Vec<String> {
        obligations(program, &Program::new(vec![]))
            .iter()
            .map(|o| o.goal.to_string())
            .collect()
    }

    /// The hypotheses in force at the first obligation mentioning `needle`.
    fn hyps_at(program: &Program, needle: &str) -> Vec<String> {
        obligations(program, &Program::new(vec![]))
            .iter()
            .find(|o| o.goal.to_string().contains(needle))
            .map(|o| o.hyps.iter().map(|h| h.to_string()).collect())
            .unwrap_or_else(|| panic!("no obligation mentioning {needle} in {:?}", goals(program)))
    }

    #[test]
    fn a_call_in_main_owes_the_callees_demand() {
        let program = with_main(call(
            "needs_nat",
            vec![Expr::UnaryNeg(Box::new(Expr::IntLit(1)))],
        ));
        assert!(
            goals(&program).contains(&"~1 >= 0".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_body_may_assume_what_its_own_signature_demanded() {
        // This is what makes dependent types compose: `f`'s promise that
        // `n` is a nat is exactly what lets `f` call `g` with it.
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![nat()],
                vec![p("y", int_of(v("n")))],
                Ty::Name("int".into()),
                call("needs_nat", vec![var("y")]),
            ),
        ]);
        assert!(hyps_at(&program, "n >= 0").contains(&"n >= 0".to_string()));
    }

    #[test]
    fn the_then_branch_assumes_the_condition_and_the_else_branch_denies_it() {
        // `if x > 0 then f(x-1)` is the shape every recursive function
        // over `nat` takes, and it is unprovable without the guard.
        let cond = Expr::BinOp(BinOp::Gt, Box::new(var("x")), Box::new(Expr::IntLit(0)));
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![],
                vec![p("x", int_of(v("k")))],
                Ty::Name("int".into()),
                Expr::IfThenElse(
                    Box::new(cond),
                    Box::new(call(
                        "needs_nat",
                        vec![Expr::BinOp(
                            BinOp::Sub,
                            Box::new(var("x")),
                            Box::new(Expr::IntLit(1)),
                        )],
                    )),
                    Box::new(call("needs_nat", vec![var("x")])),
                ),
            ),
        ]);
        assert!(hyps_at(&program, "k - 1 >= 0").contains(&"k > 0".to_string()));
        assert!(hyps_at(&program, "k >= 0").contains(&"k <= 0".to_string()));
    }

    #[test]
    fn a_let_binding_names_the_index_of_what_it_bound() {
        let program = with_main(Expr::Let(
            vec![LetBind {
                opened: Vec::new(),
                proof: false,
                name: Some("y".into()),
                ty: None,
                value: Expr::IntLit(7),
                mutable: false,
                destructures: None,
                proof_name: None,
            }],
            Box::new(call("needs_nat", vec![var("y")])),
        ));
        assert!(
            goals(&program).contains(&"7 >= 0".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn an_annotated_binding_is_checked_against_its_annotation() {
        // `val x: int(3) = 4` is a lie, and the annotation is the only
        // place that can catch it.
        let program = with_main(Expr::Let(
            vec![LetBind {
                opened: Vec::new(),
                proof: false,
                name: Some("y".into()),
                ty: Some(int_of(i(3))),
                value: Expr::IntLit(4),
                mutable: false,
                destructures: None,
                proof_name: None,
            }],
            Box::new(Expr::Unit),
        ));
        assert!(
            goals(&program).contains(&"4 == 3".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_result_type_is_a_claim_the_body_must_make_good() {
        // The half of the checker the README said was missing: a
        // signature that promises `int(n+1)` and returns `x` is wrong,
        // and nothing about the call sites will ever say so.
        let program = Program::new(vec![fun(
            "succ",
            vec![nat()],
            vec![p("x", int_of(v("n")))],
            int_of(app("+", v("n"), i(1))),
            var("x"),
        )]);
        assert!(
            goals(&program).contains(&"n == n + 1".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_result_type_the_body_honours_is_owed_but_provable() {
        let program = Program::new(vec![fun(
            "succ",
            vec![nat()],
            vec![p("x", int_of(v("n")))],
            int_of(app("+", v("n"), i(1))),
            Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(Expr::IntLit(1))),
        )]);
        assert!(
            goals(&program).contains(&"n + 1 == n + 1".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn writing_to_a_cell_stops_the_checker_believing_what_it_held_before() {
        // `var x = 3; x := ~1; needs_nat(x)` must not be proved by the 3.
        let program = with_main(Expr::Let(
            vec![LetBind {
                opened: Vec::new(),
                proof: false,
                name: Some("x".into()),
                ty: None,
                value: Expr::IntLit(3),
                mutable: true,
                destructures: None,
                proof_name: None,
            }],
            Box::new(Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: None,
                    ty: None,
                    value: Expr::Assign(
                        "x".into(),
                        Box::new(Expr::UnaryNeg(Box::new(Expr::IntLit(1)))),
                    ),
                    mutable: false,
                    destructures: None,
                    proof_name: None,
                }],
                Box::new(call("needs_nat", vec![var("x")])),
            )),
        ));
        assert!(
            !goals(&program).contains(&"3 >= 0".to_string()),
            "stale: {:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_loop_forgets_the_cells_its_body_writes() {
        // Facts established before a loop do not survive it, because the
        // body runs an unknown number of times.
        let body = Expr::Assign(
            "x".into(),
            Box::new(Expr::UnaryNeg(Box::new(Expr::IntLit(1)))),
        );
        let program = with_main(Expr::Let(
            vec![LetBind {
                opened: Vec::new(),
                proof: false,
                name: Some("x".into()),
                ty: None,
                value: Expr::IntLit(3),
                mutable: true,
                destructures: None,
                proof_name: None,
            }],
            Box::new(Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: None,
                    ty: None,
                    value: Expr::While(Box::new(Expr::BoolLit(true)), Box::new(body)),
                    mutable: false,
                    destructures: None,
                    proof_name: None,
                }],
                Box::new(call("needs_nat", vec![var("x")])),
            )),
        ));
        assert!(
            !goals(&program).contains(&"3 >= 0".to_string()),
            "stale after loop: {:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_literal_pattern_tells_its_arm_what_the_scrutinee_was() {
        // `case x of | 0 => f(x)` knows `x` is zero inside the arm.
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![],
                vec![p("x", int_of(v("k")))],
                Ty::Name("int".into()),
                Expr::Case(
                    Box::new(var("x")),
                    vec![(Pattern::Int(0), call("needs_nat", vec![var("x")]))],
                ),
            ),
        ]);
        assert!(hyps_at(&program, "k >= 0").contains(&"k == 0".to_string()));
    }

    #[test]
    fn a_variable_pattern_binds_the_scrutinees_index_to_the_name() {
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![],
                vec![p("x", int_of(v("k")))],
                Ty::Name("int".into()),
                Expr::Case(
                    Box::new(var("x")),
                    vec![(Pattern::Var("y".into()), call("needs_nat", vec![var("y")]))],
                ),
            ),
        ]);
        assert!(
            goals(&program).contains(&"k >= 0".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_subscript_owes_both_ends_of_the_array_it_reaches_into() {
        // `xs[i]` on an `array(int, n)` is only safe for `0 <= i < n`,
        // and this is the obligation ATS exists to make.
        let arr = Ty::Index(
            Box::new(Ty::App("array".into(), vec![Ty::Name("int".into())])),
            vec![v("n")],
        );
        let program = Program::new(vec![fun(
            "get",
            vec![],
            vec![p("xs", arr), p("i", int_of(v("k")))],
            Ty::Name("int".into()),
            Expr::Index(Box::new(var("xs")), Box::new(var("i"))),
        )]);
        let g = goals(&program);
        assert!(g.contains(&"k >= 0".to_string()), "{g:?}");
        assert!(g.contains(&"k < n".to_string()), "{g:?}");
    }

    #[test]
    fn a_nested_function_is_checked_under_its_own_quantifiers() {
        // A `let fun` has a signature and a body like any other, and
        // skipping it would leave most real ATS unchecked.
        let inner = FunDef {
            ty_params: vec![],
            universals: vec![nat()],
            existentials: vec![],
            metric: vec![],
            name: "loop".into(),
            params: vec![p("x", int_of(v("n")))],
            ret: int_of(app("+", v("n"), i(1))),
            body: var("x"),
            proof: false,
        };
        let program = with_main(Expr::LetFun(vec![inner], Box::new(Expr::Unit)));
        assert!(
            goals(&program).contains(&"n == n + 1".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_call_may_assume_what_an_existential_result_promised() {
        // `g(): [r:nat] int r` followed by `needs_nat(g())` is provable
        // only if the existential's guard came back with the value.
        let g = Def::Fun(FunDef {
            metric: vec![],
            ty_params: vec![],
            universals: vec![],
            existentials: vec![Quant {
                vars: vec![("r".into(), Sort::Nat)],
                guard: None,
            }],
            name: "g".into(),
            params: vec![],
            ret: int_of(v("r")),
            body: Expr::IntLit(0),
            proof: false,
        });
        let mut defs = vec![g];
        defs.extend(
            with_main(call("needs_nat", vec![call("g", vec![])]))
                .defs()
                .to_vec(),
        );
        let program = Program::new(defs);
        let o = obligations(&program, &Program::new(vec![]));
        let call_ob = o
            .iter()
            .find(|o| matches!(o.origin, Origin::Call { ref callee } if callee == "needs_nat"))
            .expect("the call");
        assert!(
            call_ob.hyps.iter().any(|h| h.to_string().starts_with("r%")),
            "the witness's nat-ness must be in scope: {:?}",
            call_ob.hyps
        );
    }

    #[test]
    fn a_datatype_declaration_does_not_derail_the_walk() {
        let program = Program::new(vec![Def::Datatype(DatatypeDef {
            linear: false,
            name: "opt".into(),
            ty_params: vec!["a".into()],
            ctors: vec![Ctor {
                name: "none".into(),
                universals: vec![],
                result: None,
                fields: vec![],
            }],
        })]);
        assert!(obligations(&program, &Program::new(vec![])).is_empty());
    }

    #[test]
    fn a_promised_result_is_pushed_into_each_branch_rather_than_joined() {
        // `if c then a else b` checked as a *whole* loses everything:
        // the two arms disagree, so the join is an unknown and the
        // promise becomes unprovable.  Checked branch by branch, each arm
        // answers for itself under its own guard — which is the whole
        // difference between a checker that reads `if` and one that only
        // walks past it.
        let x = var("x");
        let plus1 = Expr::BinOp(BinOp::Add, Box::new(x.clone()), Box::new(Expr::IntLit(1)));
        let program = Program::new(vec![fun(
            "succ",
            vec![nat()],
            vec![p("x", int_of(v("n")))],
            int_of(app("+", v("n"), i(1))),
            Expr::IfThenElse(
                Box::new(Expr::BinOp(
                    BinOp::Gt,
                    Box::new(x),
                    Box::new(Expr::IntLit(0)),
                )),
                Box::new(plus1.clone()),
                Box::new(plus1),
            ),
        )]);
        let g = goals(&program);
        assert!(
            !g.iter().any(|goal| goal.contains("join%")),
            "the arms were joined: {g:?}"
        );
        assert_eq!(g, vec!["n + 1 == n + 1".to_string(); 2], "{g:?}");
    }


    #[test]
    fn an_unannotated_branching_call_argument_still_proves_its_demand() {
        // `needs_nat(if x > 0 then x else 0)` — the argument has no
        // annotation and is not a `let`, so there is no promise to push
        // down into the branches (unlike the test above). The join is
        // an unconstrained fresh variable, and its own guard is the
        // only fact left that could still prove the call's demand.
        let cond = Expr::BinOp(BinOp::Gt, Box::new(var("x")), Box::new(Expr::IntLit(0)));
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![],
                vec![p("x", int_of(v("k")))],
                Ty::Name("int".into()),
                call(
                    "needs_nat",
                    vec![Expr::IfThenElse(
                        Box::new(cond),
                        Box::new(var("x")),
                        Box::new(Expr::IntLit(0)),
                    )],
                ),
            ),
        ]);
        let obs = obligations(&program, &Program::new(vec![]));
        let ob = obs
            .iter()
            .find(|o| o.goal.to_string().contains(">= 0"))
            .expect("a nat demand");
        assert!(
            ob.goal.to_string().contains("join%"),
            "expected the joined argument itself: {}",
            ob.goal
        );
        assert_eq!(
            crate::constraints::entails(&ob.hyps, &ob.goal),
            crate::constraints::Verdict::Proved,
            "goal {} not proved from {:?}",
            ob.goal,
            ob.hyps
        );
    }


    #[test]
    fn a_promised_result_is_pushed_through_a_let_to_the_value_it_ends_with() {
        // A body is usually `let ... in <the answer> end`, and a checker
        // that stopped at the `let` would check almost nothing.
        let program = Program::new(vec![fun(
            "succ",
            vec![nat()],
            vec![p("x", int_of(v("n")))],
            int_of(app("+", v("n"), i(1))),
            Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: Some("y".into()),
                    ty: None,
                    value: Expr::IntLit(1),
                    mutable: false,
                    destructures: None,
                    proof_name: None,
                }],
                Box::new(Expr::BinOp(
                    BinOp::Add,
                    Box::new(var("x")),
                    Box::new(var("y")),
                )),
            ),
        )]);
        assert!(
            goals(&program).contains(&"n + 1 == n + 1".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn each_arm_of_a_case_answers_for_the_promise_on_its_own() {
        let program = Program::new(vec![fun(
            "id",
            vec![nat()],
            vec![p("x", int_of(v("n")))],
            int_of(v("n")),
            Expr::Case(
                Box::new(var("x")),
                vec![
                    (Pattern::Int(0), Expr::IntLit(0)),
                    (Pattern::Var("y".into()), var("y")),
                ],
            ),
        )]);
        let g = goals(&program);
        assert!(g.contains(&"0 == n".to_string()), "{g:?}");
        assert!(g.contains(&"n == n".to_string()), "{g:?}");
    }

    #[test]
    fn main0_knows_that_argv_is_as_long_as_argc_says() {
        // ATS gives the entry point `main0 {n:nat} (argc: int n, argv:
        // !argv(n))`: the count and the array are indexed by the *same*
        // variable.  Without that, `if argc >= 2 then argv[1]` — which is
        // how a third of the corpus reads its arguments — is unprovable,
        // and the checker's first impression of real code is a false
        // alarm on every one of them.
        let guard = Expr::BinOp(BinOp::Ge, Box::new(var("argc")), Box::new(Expr::IntLit(2)));
        let read = Expr::Index(Box::new(var("argv")), Box::new(Expr::IntLit(1)));
        let program = Program::new(vec![Def::Implement(ImplementDef {
            ty_params: vec![],
            instance: vec![],
            name: "main0".into(),
            params: vec![
                p("argc", Ty::Name("int".into())),
                p("argv", Ty::Name("argv".into())),
            ],
            ret: None,
            body: Expr::IfThenElse(Box::new(guard), Box::new(read), Box::new(Expr::Unit)),
        })]);
        let obs = obligations(&program, &Program::new(vec![]));
        let upper = obs
            .iter()
            .find(|o| o.goal.to_string().starts_with("1 <"))
            .unwrap_or_else(|| panic!("no upper-bound check in {:?}", goals(&program)));
        assert_eq!(
            crate::constraints::entails(&upper.hyps, &upper.goal),
            crate::constraints::Verdict::Proved,
            "goal {} from {:?}",
            upper.goal,
            upper.hyps
        );
    }

    #[test]
    fn argv_zero_is_always_there_because_argc_is_never_zero() {
        // `argv[0]` is the program's own name, so `main0`'s count is a
        // `pos`, not merely a `nat`.  Without that, the else-branch of
        // every `if argc >= 2` — the one that falls back on defaults —
        // cannot reach `argv[0]`, which is where the corpus keeps the
        // program name.
        let guard = Expr::BinOp(BinOp::Ge, Box::new(var("argc")), Box::new(Expr::IntLit(2)));
        let read = Expr::Index(Box::new(var("argv")), Box::new(Expr::IntLit(0)));
        let program = Program::new(vec![Def::Implement(ImplementDef {
            ty_params: vec![],
            instance: vec![],
            name: "main0".into(),
            params: vec![
                p("argc", Ty::Name("int".into())),
                p("argv", Ty::Name("argv".into())),
            ],
            ret: None,
            body: Expr::IfThenElse(Box::new(guard), Box::new(Expr::Unit), Box::new(read)),
        })]);
        let obs = obligations(&program, &Program::new(vec![]));
        let upper = obs
            .iter()
            .find(|o| o.goal.to_string().starts_with("0 <"))
            .expect("an upper bound");
        assert_eq!(
            crate::constraints::entails(&upper.hyps, &upper.goal),
            crate::constraints::Verdict::Proved,
            "goal {} from {:?}",
            upper.goal,
            upper.hyps
        );
    }

    #[test]
    fn an_implementation_is_checked_against_the_signature_it_was_declared_with() {
        // `extern fun f {n:nat} (x: int n): int` followed by
        // `implement f (x) = ...` writes the quantifier once.  A checker
        // that read only the `implement` would see an unindexed
        // parameter and could prove nothing about the body at all.
        let program = Program::new(vec![
            Def::Extern(ats2_domain::ast::FunDecl {
                linear: false,
                proof: false,
                name: "f".into(),
                ty_params: vec![],
                universals: vec![nat()],
                existentials: vec![],
                params: vec![p("x", int_of(v("n")))],
                ret: int_of(app("+", v("n"), i(1))),
            }),
            Def::Implement(ImplementDef {
                ty_params: vec![],
                instance: vec![],
                name: "f".into(),
                params: vec![p("x", Ty::Name("int".into()))],
                ret: None,
                body: var("x"),
            }),
        ]);
        // The declared result is `int(n+1)` and the body returns `x`,
        // which is `n`: the promise is broken, and only the declaration
        // could have said so.
        assert!(
            goals(&program).contains(&"n == n + 1".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn an_implementation_that_annotates_its_own_parameters_keeps_them() {
        // Where the `implement` says what it means, it wins: the
        // declaration fills gaps, it does not overrule.
        let program = Program::new(vec![
            Def::Extern(ats2_domain::ast::FunDecl {
                linear: false,
                proof: false,
                name: "f".into(),
                ty_params: vec![],
                universals: vec![nat()],
                existentials: vec![],
                params: vec![p("x", int_of(v("n")))],
                ret: Ty::Name("int".into()),
            }),
            Def::Implement(ImplementDef {
                ty_params: vec![],
                instance: vec![],
                name: "f".into(),
                params: vec![p("x", int_of(i(7)))],
                ret: Some(int_of(i(7))),
                body: var("x"),
            }),
        ]);
        assert!(
            goals(&program).contains(&"7 == 7".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_function_that_merely_happens_to_be_called_argc_gets_no_such_gift() {
        // The convention belongs to the entry point, not to the names.
        // Granting it anywhere else would be inventing a fact.
        let read = Expr::Index(Box::new(var("argv")), Box::new(Expr::IntLit(1)));
        let program = Program::new(vec![fun(
            "not_main",
            vec![],
            vec![
                p("argc", Ty::Name("int".into())),
                p("argv", Ty::Name("argv".into())),
            ],
            Ty::Name("void".into()),
            read,
        )]);
        assert!(
            !goals(&program).iter().any(|g| g.starts_with("1 <")),
            "an unindexed array has no size to check against: {:?}",
            goals(&program)
        );
    }

    /// `fun f {n:nat} .<metric>. (x: int n): int = <body>`
    fn recursive(metric: Vec<SExp>, body: Expr) -> Program {
        Program::new(vec![Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![nat()],
            existentials: vec![],
            metric,
            name: "f".into(),
            params: vec![p("x", int_of(v("n")))],
            ret: Ty::Name("int".into()),
            body,
            proof: false,
        })])
    }

    /// `f(x - 1)`
    fn call_smaller() -> Expr {
        call(
            "f",
            vec![Expr::BinOp(
                BinOp::Sub,
                Box::new(var("x")),
                Box::new(Expr::IntLit(1)),
            )],
        )
    }

    #[test]
    fn a_recursive_call_must_decrease_the_metric_it_was_given() {
        // Without this a function may promise anything at all and keep
        // the promise by never returning, which is not a proof of
        // anything.  The claim is `n - 1 < n`, and it is the program's to
        // make, not the compiler's to assume.
        let program = recursive(vec![v("n")], call_smaller());
        let metric: Vec<&Obligation> = obligations(&program, &Program::new(vec![]))
            .iter()
            .filter(|o| matches!(o.origin, Origin::Metric { .. }))
            .cloned()
            .collect::<Vec<_>>()
            .leak()
            .iter()
            .collect();
        assert!(
            !metric.is_empty(),
            "no metric was checked: {:?}",
            goals(&program)
        );
        for o in metric {
            assert_eq!(
                crate::constraints::entails(&o.hyps, &o.goal),
                crate::constraints::Verdict::Proved,
                "goal {} from {:?}",
                o.goal,
                o.hyps
            );
        }
    }

    #[test]
    fn a_recursive_call_that_grows_the_metric_is_caught() {
        let grows = call(
            "f",
            vec![Expr::BinOp(
                BinOp::Add,
                Box::new(var("x")),
                Box::new(Expr::IntLit(1)),
            )],
        );
        let program = recursive(vec![v("n")], grows);
        let bad = obligations(&program, &Program::new(vec![]))
            .into_iter()
            .find(|o| matches!(o.origin, Origin::Metric { .. }) && o.goal.to_string().contains('<'))
            .expect("a decrease obligation");
        assert_eq!(
            crate::constraints::entails(&bad.hyps, &bad.goal),
            crate::constraints::Verdict::Refuted
        );
    }

    #[test]
    fn a_function_given_no_metric_is_asked_for_no_proof_of_termination() {
        // `.<>.` and a bare `fun` both claim nothing, and a checker that
        // invented the claim would reject every loop written without one.
        let program = recursive(vec![], call_smaller());
        assert!(
            !obligations(&program, &Program::new(vec![]))
                .iter()
                .any(|o| matches!(o.origin, Origin::Metric { .. }))
        );
    }

    #[test]
    fn a_call_to_someone_else_is_not_a_recursion_and_owes_no_decrease() {
        let program = with_main(call("needs_nat", vec![Expr::IntLit(1)]));
        assert!(
            !obligations(&program, &Program::new(vec![]))
                .iter()
                .any(|o| matches!(o.origin, Origin::Metric { .. }))
        );
    }

    #[test]
    fn the_metric_must_be_well_founded_as_well_as_decreasing() {
        // A metric that decreases forever proves nothing: `n` must also
        // be bounded below, or `n-1 < n` is satisfied by descending into
        // the negatives without end.
        let program = recursive(vec![v("n")], call_smaller());
        let goals: Vec<String> = obligations(&program, &Program::new(vec![]))
            .iter()
            .filter(|o| matches!(o.origin, Origin::Metric { .. }))
            .map(|o| o.goal.to_string())
            .collect();
        assert!(
            goals.iter().any(|g| g.contains(">= 0")),
            "no well-foundedness: {goals:?}"
        );
    }

    #[test]
    fn a_lexicographic_metric_decreases_when_a_later_component_does() {
        // `.<m, n>.` allows `m` to stay put as long as `n` falls.  That
        // is a disjunction, and refusing it would reject every nested
        // recursion in the language.
        let program = Program::new(vec![Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("m".into(), Sort::Nat), ("n".into(), Sort::Nat)],
                guard: None,
            }],
            existentials: vec![],
            metric: vec![v("m"), v("n")],
            name: "f".into(),
            params: vec![p("a", int_of(v("m"))), p("b", int_of(v("n")))],
            ret: Ty::Name("int".into()),
            body: call(
                "f",
                vec![
                    var("a"),
                    Expr::BinOp(BinOp::Sub, Box::new(var("b")), Box::new(Expr::IntLit(1))),
                ],
            ),
            proof: false,
        })]);
        for o in obligations(&program, &Program::new(vec![]))
            .iter()
            .filter(|o| matches!(o.origin, Origin::Metric { .. }))
        {
            assert_eq!(
                crate::constraints::entails(&o.hyps, &o.goal),
                crate::constraints::Verdict::Proved,
                "goal {} from {:?}",
                o.goal,
                o.hyps
            );
        }
    }

    #[test]
    fn a_templates_type_argument_is_never_read_as_an_index() {
        // `f<int>(3)` names which *code* to build.  Reading `int` as an
        // index and handing it to a `{n:nat}` would fix `n` to a type
        // name and prove whatever followed from nonsense.
        let program = Program::new(vec![
            Def::Fun(FunDef {
                ty_params: vec!["a".into()],
                universals: vec![nat()],
                existentials: vec![],
                metric: vec![],
                name: "g".into(),
                params: vec![p("x", int_of(v("n")))],
                ret: Ty::Name("int".into()),
                body: Expr::IntLit(0),
                proof: false,
            }),
            Def::Implement(ImplementDef {
                ty_params: vec![],
                instance: vec![],
                name: "main0".into(),
                params: vec![],
                ret: None,
                body: Expr::Call(
                    Box::new(Expr::Inst("g".into(), vec![Ty::Name("int".into())])),
                    vec![Expr::IntLit(3)],
                ),
            }),
        ]);
        // `n` comes from the argument, not from the type argument.
        assert!(
            goals(&program).contains(&"3 >= 0".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_refinement_result_is_a_bound_the_body_must_meet_not_a_value() {
        // `fun f (): intGte(0) = 7` is correct: seven is at least
        // nought.  Reading the index as the value would demand `7 == 0`
        // and reject every program written with a bounded type.
        let ret = Ty::Index(Box::new(Ty::Name("intGte".into())), vec![i(0)]);
        let program = Program::new(vec![fun("f", vec![], vec![], ret, Expr::IntLit(7))]);
        assert_eq!(goals(&program), vec!["7 >= 0".to_string()]);
    }

    #[test]
    fn a_refinement_parameter_is_a_fact_the_body_may_use() {
        // `(i: natLt(n))` is what makes `xs[i]` safe, and it says so
        // twice: not below nought, and below `n`.
        let arr = Ty::Index(
            Box::new(Ty::App("array".into(), vec![Ty::Name("int".into())])),
            vec![v("n")],
        );
        let idx = Ty::Index(Box::new(Ty::Name("natLt".into())), vec![v("n")]);
        let program = Program::new(vec![fun(
            "get",
            vec![],
            vec![p("xs", arr), p("i", idx)],
            Ty::Name("int".into()),
            Expr::Index(Box::new(var("xs")), Box::new(var("i"))),
        )]);
        for o in obligations(&program, &Program::new(vec![]))
            .iter()
            .filter(|o| matches!(o.origin, Origin::Bound { .. }))
        {
            assert_eq!(
                crate::constraints::entails(&o.hyps, &o.goal),
                crate::constraints::Verdict::Proved,
                "goal {} from {:?}",
                o.goal,
                o.hyps
            );
        }
    }

    #[test]
    fn an_annotated_binding_is_checked_branch_by_branch() {
        // `val n = (if n >= 0 then n else 0): intGte(0)` is how the
        // corpus turns an unbounded integer into a bounded one.  Joining
        // the arms first makes it unprovable, so the annotation has to
        // reach into them exactly as a result type does.
        let x = var("x");
        let annotated = Expr::IfThenElse(
            Box::new(Expr::BinOp(
                BinOp::Ge,
                Box::new(x.clone()),
                Box::new(Expr::IntLit(0)),
            )),
            Box::new(x),
            Box::new(Expr::IntLit(0)),
        );
        let program = Program::new(vec![fun(
            "clamp",
            vec![],
            vec![p("x", int_of(v("k")))],
            Ty::Name("int".into()),
            Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: Some("y".into()),
                    ty: Some(Ty::Index(Box::new(Ty::Name("intGte".into())), vec![i(0)])),
                    value: annotated,
                    mutable: false,
                    destructures: None,
                    proof_name: None,
                }],
                Box::new(Expr::Unit),
            ),
        )]);
        for o in obligations(&program, &Program::new(vec![])) {
            assert_eq!(
                crate::constraints::entails(&o.hyps, &o.goal),
                crate::constraints::Verdict::Proved,
                "goal {} from {:?}",
                o.goal,
                o.hyps
            );
        }
    }

    #[test]
    fn opening_an_existential_names_the_witness_the_callee_would_not() {
        // `val [r1:nat] (pf | y) = g()` says: whatever `g` produced,
        // call its witness `r1`.  From then on `r1` is a variable the
        // caller can reason about — and `needs_nat(y)` goes through
        // because `r1` is known to be a nat.
        let g = Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![],
            existentials: vec![Quant {
                vars: vec![("r".into(), Sort::Nat)],
                guard: None,
            }],
            metric: vec![],
            name: "g".into(),
            params: vec![],
            ret: int_of(v("r")),
            body: Expr::IntLit(0),
            proof: false,
        });
        let body = Expr::Let(
            vec![LetBind {
                opened: vec![("r1".into(), Sort::Nat)],
                proof: false,
                name: Some("y".into()),
                ty: None,
                value: call("g", vec![]),
                mutable: false,
                destructures: None,
                proof_name: None,
            }],
            Box::new(call("needs_nat", vec![var("y")])),
        );
        let mut defs = vec![g];
        defs.extend(with_main(body).defs().to_vec());
        let program = Program::new(defs);
        let opened = obligations(&program, &Program::new(vec![]))
            .into_iter()
            .find(|o| matches!(o.origin, Origin::Call { ref callee } if callee == "needs_nat"))
            .expect("the call");
        assert!(
            opened.hyps.iter().any(|h| h.to_string() == "r1 >= 0"),
            "the witness was not named: {:?}",
            opened.hyps
        );
    }

    #[test]
    fn a_proof_keeps_every_index_its_proposition_is_about() {
        // `prval pf = FACTind{3}{2}(...)` proves `FACT(3, 6)`.  Binding
        // only the first index would leave a proof that says half of
        // what it says, and nothing downstream could use it.
        let ctor = Def::Extern(ats2_domain::ast::FunDecl {
            linear: false,
            proof: false,
            name: "FACTind".into(),
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("n".into(), Sort::Pos), ("r".into(), Sort::Int)],
                guard: None,
            }],
            existentials: vec![],
            params: vec![],
            ret: Ty::Index(
                Box::new(Ty::Name("FACT".into())),
                vec![v("n"), app("*", v("n"), v("r"))],
            ),
        });
        let body = Expr::Let(
            vec![LetBind {
                opened: vec![],
                proof: true,
                name: Some("pf".into()),
                ty: None,
                value: Expr::Call(
                    Box::new(Expr::StaticInst(Box::new(var("FACTind")), vec![i(3), i(2)])),
                    vec![],
                ),
                mutable: false,
                destructures: None,
                proof_name: None,
            }],
            Box::new(Expr::Unit),
        );
        let mut defs = vec![ctor];
        defs.extend(with_main(body).defs().to_vec());
        let program = Program::new(defs);
        // The walk records both indices; nothing is demanded, but the
        // proof is in scope with everything it proves.
        assert!(
            obligations(&program, &Program::new(vec![]))
                .iter()
                .all(|o| o.goal.to_string() != "3 > 0"
                    || crate::constraints::entails(&o.hyps, &o.goal)
                        == crate::constraints::Verdict::Proved)
        );
        assert_eq!(
            proof_indices(&program, "pf"),
            vec!["3".to_string(), "3 * 2".to_string()]
        );
    }

    /// The indices the walk gave a proof binding — reached by re-walking
    /// with a probe, since obligations alone do not show an environment.
    fn proof_indices(program: &Program, name: &str) -> Vec<String> {
        let sigs = SigTable::of(program);
        let ctors = CtorTable::default();
        let mut walk = Walk {
            sigs: &sigs,
            local_sigs: Vec::new(),
            ctors: &ctors,
            consts: HashMap::new(),
            out: Vec::new(),
            function: String::new(),
            metric: Vec::new(),
            last_call: None,
        };
        let mut env = IndexEnv::new();
        for def in program.defs() {
            if let Def::Implement(im) = def {
                if let Expr::Let(binds, _) = &im.body {
                    for b in binds {
                        walk.let_bind(b, &mut env);
                    }
                }
            }
        }
        env.indices_of(name).iter().map(|t| t.to_string()).collect()
    }

    #[test]
    fn a_proof_determines_the_witness_the_arithmetic_cannot() {
        // `fun f {n:nat} (x: int n): [r:int] (P(n, r) | int(r*k)) =
        // (pf | v)` — the existential `r` appears multiplied in the value
        // half, and no linear solver divides.  The proposition names it
        // directly: matching `P(n, r)` against the proof's own
        // `P(n, 3)` fixes `r` at three, and the value half is then an
        // ordinary equation.  This is what a `dataprop` is *for*.
        let ctor = Def::Extern(ats2_domain::ast::FunDecl {
            linear: false,
            proof: true,
            name: "mk".into(),
            ty_params: vec![],
            universals: vec![],
            existentials: vec![],
            params: vec![],
            ret: Ty::Index(Box::new(Ty::Name("P".into())), vec![v("n"), i(3)]),
        });
        let body = Expr::Let(
            vec![LetBind {
                opened: vec![],
                proof: true,
                name: Some("pf".into()),
                ty: None,
                value: call("mk", vec![]),
                mutable: false,
                destructures: None,
                proof_name: None,
            }],
            Box::new(Expr::ProofPair(
                Box::new(var("pf")),
                Box::new(Expr::BinOp(
                    BinOp::Mul,
                    Box::new(Expr::IntLit(3)),
                    Box::new(var("k")),
                )),
            )),
        );
        let f = Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![nat()],
            existentials: vec![Quant {
                vars: vec![("r".into(), Sort::Int)],
                guard: None,
            }],
            metric: vec![],
            name: "f".into(),
            params: vec![p("x", int_of(v("n"))), p("k", int_of(v("k")))],
            ret: Ty::Proof(
                Box::new(Ty::Index(
                    Box::new(Ty::Name("P".into())),
                    vec![v("n"), v("r")],
                )),
                Box::new(int_of(app("*", v("r"), v("k")))),
            ),
            body,
            proof: false,
        });
        let program = Program::new(vec![ctor, f]);
        for o in obligations(&program, &Program::new(vec![]))
            .iter()
            .filter(|o| matches!(o.origin, Origin::Return { .. }))
        {
            assert_eq!(
                crate::constraints::entails(&o.hyps, &o.goal),
                crate::constraints::Verdict::Proved,
                "goal {} from {:?}",
                o.goal,
                o.hyps
            );
        }
    }

    #[test]
    fn a_pair_without_a_matching_proof_still_answers_for_its_value() {
        // No proposition to read the witness from, so the value half is
        // all there is — and it must still be checked.
        let f = Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![nat()],
            existentials: vec![],
            metric: vec![],
            name: "f".into(),
            params: vec![p("x", int_of(v("n")))],
            ret: int_of(app("+", v("n"), i(1))),
            body: Expr::ProofPair(Box::new(var("pf")), Box::new(var("x"))),
            proof: false,
        });
        assert!(
            goals(&Program::new(vec![f])).contains(&"n == n + 1".to_string()),
            "{:?}",
            goals(&Program::new(vec![f2()]))
        );
    }

    fn f2() -> Def {
        Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![nat()],
            existentials: vec![],
            metric: vec![],
            name: "f".into(),
            params: vec![p("x", int_of(v("n")))],
            ret: int_of(app("+", v("n"), i(1))),
            body: Expr::ProofPair(Box::new(var("pf")), Box::new(var("x"))),
            proof: false,
        })
    }

    #[test]
    fn an_assertion_establishes_what_it_asserts() {
        // `val () = assertexn(n >= 0)` is how ATS moves a check from run
        // time into the static world: past that line the program either
        // stopped or `n` is a nat, and a checker that ignored it would
        // reject the argument handling of half the corpus.
        let assertion = Expr::Call(
            Box::new(var("assertexn")),
            vec![Expr::BinOp(
                BinOp::Ge,
                Box::new(var("x")),
                Box::new(Expr::IntLit(0)),
            )],
        );
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![],
                vec![p("x", int_of(v("k")))],
                Ty::Name("int".into()),
                Expr::Let(
                    vec![LetBind {
                        opened: vec![],
                        proof: false,
                        name: None,
                        ty: None,
                        value: assertion,
                        mutable: false,
                        destructures: None,
                        proof_name: None,
                    }],
                    Box::new(call("needs_nat", vec![var("x")])),
                ),
            ),
        ]);
        let owed = obligations(&program, &Program::new(vec![]))
            .into_iter()
            .find(|o| matches!(o.origin, Origin::Call { ref callee } if callee == "needs_nat"))
            .expect("the call");
        assert_eq!(
            crate::constraints::entails(&owed.hyps, &owed.goal),
            crate::constraints::Verdict::Proved,
            "goal {} from {:?}",
            owed.goal,
            owed.hyps
        );
    }

    #[test]
    fn an_ordinary_call_establishes_nothing_merely_by_being_made() {
        // Only the assertions assert.  Any other function taking a
        // boolean would otherwise make its argument true by being called.
        let checked = Expr::Call(
            Box::new(var("check")),
            vec![Expr::BinOp(
                BinOp::Ge,
                Box::new(var("x")),
                Box::new(Expr::IntLit(0)),
            )],
        );
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![],
                vec![p("x", int_of(v("k")))],
                Ty::Name("int".into()),
                Expr::Let(
                    vec![LetBind {
                        opened: vec![],
                        proof: false,
                        name: None,
                        ty: None,
                        value: checked,
                        mutable: false,
                        destructures: None,
                        proof_name: None,
                    }],
                    Box::new(call("needs_nat", vec![var("x")])),
                ),
            ),
        ]);
        let owed = obligations(&program, &Program::new(vec![]))
            .into_iter()
            .find(|o| matches!(o.origin, Origin::Call { ref callee } if callee == "needs_nat"))
            .expect("the call");
        assert_ne!(
            crate::constraints::entails(&owed.hyps, &owed.goal),
            crate::constraints::Verdict::Proved
        );
    }

    #[test]
    fn an_ascription_is_checked_branch_by_branch_like_any_other_claim() {
        // `val n = (if n >= 0 then n else 0): intGte(0)` is how the
        // corpus bounds an integer it read from the command line.  The
        // claim has to reach into the arms, exactly as a result type
        // does — joined first, it is unprovable.
        let x = var("x");
        let inner = Expr::IfThenElse(
            Box::new(Expr::BinOp(
                BinOp::Ge,
                Box::new(x.clone()),
                Box::new(Expr::IntLit(0)),
            )),
            Box::new(x),
            Box::new(Expr::IntLit(0)),
        );
        let bounded = Expr::Ascribe(
            Box::new(inner),
            Ty::Index(Box::new(Ty::Name("intGte".into())), vec![i(0)]),
        );
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![],
                vec![p("x", int_of(v("k")))],
                Ty::Name("int".into()),
                Expr::Let(
                    vec![LetBind {
                        opened: vec![],
                        proof: false,
                        name: Some("y".into()),
                        ty: None,
                        value: bounded,
                        mutable: false,
                        destructures: None,
                        proof_name: None,
                    }],
                    Box::new(call("needs_nat", vec![var("y")])),
                ),
            ),
        ]);
        for o in obligations(&program, &Program::new(vec![])) {
            assert_eq!(
                crate::constraints::entails(&o.hyps, &o.goal),
                crate::constraints::Verdict::Proved,
                "goal {} from {:?}",
                o.goal,
                o.hyps
            );
        }
    }

    #[test]
    fn every_obligation_says_which_function_it_came_from() {
        let program = Program::new(vec![fun(
            "succ",
            vec![nat()],
            vec![p("x", int_of(v("n")))],
            int_of(app("+", v("n"), i(1))),
            var("x"),
        )]);
        assert_eq!(
            obligations(&program, &Program::new(vec![]))[0].origin,
            Origin::Return {
                function: "succ".into()
            }
        );
    }
