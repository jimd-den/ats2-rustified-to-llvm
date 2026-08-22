use super::*;

    use super::*;

    // --- helpers ----------------------------------------------------

    fn body_of(source: &str) -> Expr {
        let p = Parser::parse(source).expect("parse");
        let Def::Fun(f) = &p.defs()[0] else {
            panic!("expected a fun def")
        };
        f.body.clone()
    }

    fn impl_body(source: &str) -> Expr {
        let p = Parser::parse(source).expect("parse");
        let Def::Implement(i) = &p.defs()[0] else {
            panic!("expected an implement def")
        };
        i.body.clone()
    }

    fn expect_err(source: &str) -> CompileError {
        Parser::parse(source)
            .expect_err("should fail")
            .into_iter()
            .next()
            .expect("at least one error")
    }

    fn int(n: i64) -> Expr {
        Expr::IntLit(n)
    }
    fn var(name: &str) -> Expr {
        Expr::Var(name.to_string())
    }

    // --- programs ---------------------------------------------------

    #[test]
    fn parses_an_empty_program() {
        for src in ["", "\n\n", "(* only comments *)"] {
            let p = Parser::parse(src).expect("parse");
            assert_eq!(p.defs().len(), 0, "src: {src}");
        }
    }

    #[test]
    fn parses_a_simple_function() {
        let p = Parser::parse("fun f(x: int): int = x + 1").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.name, "f");
        assert_eq!(f.params.len(), 1);
        assert_eq!(
            f.params[0],
            Param {
                borrowed: false,
                name: "x".into(),
                ty: Ty::Name("int".into())
            }
        );
        assert_eq!(f.ret, Ty::Name("int".into()));
        assert_eq!(
            f.body,
            Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(int(1)))
        );
    }

    #[test]
    fn parses_multi_param_and_zero_param_functions() {
        let p = Parser::parse("fun add(x: int, y: int): int = x + y").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.params.len(), 2);

        let p = Parser::parse("fun forty_two(): int = 42").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.params.len(), 0);
        assert_eq!(f.body, int(42));
    }

    #[test]
    fn parses_two_definitions_in_order() {
        let p =
            Parser::parse("fun f(): int = 1\nimplement main0() = println!(f())").expect("parse");
        assert_eq!(p.defs().len(), 2);
        assert!(matches!(p.defs()[0], Def::Fun(_)));
        assert!(matches!(p.defs()[1], Def::Implement(_)));
    }

    #[test]
    fn rejects_non_definitions_at_top_level() {
        let err = expect_err("42");
        assert_eq!(err.kind(), ats2_domain::errors::ErrorKind::Parse);
        assert_eq!(err.message(), "expected a definition");
    }

    #[test]
    fn dependency_parsing_keeps_declarations_before_an_unsupported_form() {
        let source = "extern fun declared(): int\nimplement";
        assert!(Parser::parse(source).is_err(), "root parsing stays strict");

        let program = Parser::parse_dependency(source).expect("dependency parse");
        assert_eq!(program.defs().len(), 1);
        let Def::Extern(declaration) = &program.defs()[0] else {
            panic!("expected the available declaration")
        };
        assert_eq!(declaration.name, "declared");
    }

    #[test]
    fn dependency_parsing_recovers_declarations_after_an_unsupported_form() {
        let source = "\
extern fun before(): int
implement
extern fun after(): int
";
        assert!(Parser::parse(source).is_err(), "root parsing stays strict");

        let program = Parser::parse_dependency(source).expect("dependency parse");
        let names: Vec<&str> = program
            .defs()
            .iter()
            .filter_map(|def| match def {
                Def::Extern(declaration) => Some(declaration.name.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(names, ["before", "after"]);
    }

    // --- datatypes -------------------------------------------------

    #[test]
    fn parses_a_datatype_with_type_parameters() {
        let p = Parser::parse("datatype list(a) = nil | cons(a, list(a))").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else {
            panic!()
        };
        assert_eq!(d.name, "list");
        assert_eq!(d.ty_params, vec!["a"]);
        assert_eq!(d.ctors.len(), 2);
        assert_eq!(
            d.ctors[0],
            Ctor {
                name: "nil".into(),
                universals: vec![],
                result: None,
                fields: vec![]
            }
        );
        assert_eq!(d.ctors[1].name, "cons");
        assert_eq!(d.ctors[1].fields.len(), 2);
    }

    // --- juxtaposition in types -----------------------------------

    #[test]
    fn a_juxtaposed_type_variable_applies_the_type() {
        // `bintree a`, where `a` is the template's own parameter: the
        // juxtaposition is an application, so the element type survives
        // for inference to read.
        let p = Parser::parse("fun{a:t@ype} size (bt: !bintree a): int = 0").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(
            f.params[0].ty,
            Ty::App("bintree".into(), vec![Ty::Name("a".into())]),
            "got {:?}",
            f.params[0].ty
        );
    }

    #[test]
    fn a_juxtaposed_type_variable_in_datatype_fields() {
        // `cons(bintree a, a, bintree a)` — the datatype's own parameter
        // applied to itself, so the recursive field carries the element
        // type.
        let p = Parser::parse("datatype bintree(a) = nil | cons(bintree a, a, bintree a)")
            .expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else {
            panic!()
        };
        assert_eq!(
            d.ctors[1].fields[0],
            Ty::App("bintree".into(), vec![Ty::Name("a".into())]),
            "got {:?}",
            d.ctors[1].fields[0]
        );
    }

    #[test]
    fn a_juxtaposed_index_is_still_dropped() {
        // `int n` where `n` is an index quantifier, not a type
        // parameter: an indexed `int`, which erases to plain `int`.
        let p = Parser::parse("fun{n:int} f (x: int n): int = 0").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(
            f.params[0].ty,
            Ty::Index(
                Box::new(Ty::Name("int".into())),
                vec![SExp::Var("n".into())]
            )
        );
    }

    #[test]
    fn a_skipped_directive_stops_at_a_datavtype() {
        // A `staload` line is skipped until the next definition begins —
        // and a `datavtype` is a definition, so the skip must stop there
        // rather than eating it.
        let p = Parser::parse("staload _ = \"x.dats\"\ndatavtype t(a) = nil of () | cons of (a, t a)\nfun f(): int = 1").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else {
            panic!("got {:?}", &p.defs()[0])
        };
        assert_eq!(d.name, "t");
        assert_eq!(d.ctors.len(), 2);
    }

    // --- `staload`, recorded rather than forgotten -----------------

    #[test]
    fn an_include_records_a_source_dependency() {
        let p = Parser::parse("#include \"parts/body.dats\"\nfun f(): int = 1").expect("parse");
        assert_eq!(p.includes().len(), 1);
        assert_eq!(p.includes()[0].path, "parts/body.dats");
        assert_eq!(p.defs().len(), 1);
    }

    #[test]
    fn an_include_inside_local_stops_before_in() {
        let p =
            Parser::parse("local\n#include \"parts/body.dats\"\nin\nfun public(): int = 1\nend")
                .expect("parse");
        assert_eq!(p.includes()[0].path, "parts/body.dats");
        assert_eq!(p.defs().len(), 1);
    }

    #[test]
    fn a_datatype_where_alias_is_available_to_following_signatures() {
        let p = Parser::parse(
            "datatype tree = Leaf | Node of treelst\n\
             where treelst = List0(tree)\n\
             fun children(x: tree): treelst",
        )
        .expect("parse");
        let Def::Extern(children) = &p.defs()[1] else {
            panic!("expected the following signature");
        };
        assert_eq!(
            children.ret,
            Ty::App("list0".into(), vec![Ty::Name("tree".into())])
        );
    }

    #[test]
    fn a_declared_datatype_may_be_a_bare_signature_parameter() {
        let p = Parser::parse("datatype token = Tok\nfun consume(token): void").expect("parse");
        let Def::Extern(consume) = &p.defs()[1] else {
            panic!("expected the signature");
        };
        assert_eq!(consume.params[0].ty, Ty::Name("token".into()));
    }

    #[test]
    fn a_staload_says_which_file_it_wants() {
        let p = Parser::parse("staload \"helper.sats\"\nfun f(): int = 1").expect("parse");
        assert_eq!(p.staloads().len(), 1, "{:?}", p.staloads());
        assert_eq!(p.staloads()[0].path, "helper.sats");
        assert_eq!(p.staloads()[0].alias, None);
        assert_eq!(p.staloads()[0].kind, ats2_domain::ast::LoadKind::Interface);
        // Recording it must not stop the rest of the file parsing.
        assert_eq!(p.defs().len(), 1);
    }

    #[test]
    fn a_staload_with_a_name_keeps_the_name() {
        // `$UN.cast` is written in source, so something has to know that
        // `UN` was a module rather than a value.
        let p = Parser::parse("staload UN = \"unsafe.sats\"\nfun f(): int = 1").expect("parse");
        assert_eq!(p.staloads().len(), 1, "{:?}", p.staloads());
        assert_eq!(p.staloads()[0].path, "unsafe.sats");
        assert_eq!(p.staloads()[0].alias.as_deref(), Some("UN"));
    }

    #[test]
    fn an_anonymous_staload_introduces_no_name() {
        // `_` and `_(*anon*)` both mean \"for its definitions, not its
        // namespace\" — there is no alias to record.
        for src in [
            "staload _ = \"x.dats\"\nfun f(): int = 1",
            "staload _(*anon*) = \"x.dats\"\nfun f(): int = 1",
        ] {
            let p = Parser::parse(src).expect("parse");
            assert_eq!(p.staloads().len(), 1, "{src:?} -> {:?}", p.staloads());
            assert_eq!(p.staloads()[0].path, "x.dats", "{src:?}");
            assert_eq!(p.staloads()[0].alias, None, "{src:?}");
            assert_eq!(
                p.staloads()[0].kind,
                ats2_domain::ast::LoadKind::Implementation
            );
        }
    }

    #[test]
    fn a_dynload_is_a_staload_said_differently() {
        let p = Parser::parse("dynload \"x.dats\"\nfun f(): int = 1").expect("parse");
        assert_eq!(p.staloads().len(), 1, "{:?}", p.staloads());
        assert_eq!(p.staloads()[0].path, "x.dats");
        assert_eq!(p.staloads()[0].kind, ats2_domain::ast::LoadKind::Dynamic);
    }

    #[test]
    fn every_staload_in_a_file_is_kept_in_order() {
        let p = Parser::parse(
            "staload \"a.sats\"\nstaload B = \"b.sats\"\ndynload \"c.dats\"\nfun f(): int = 1",
        )
        .expect("parse");
        let paths: Vec<&str> = p.staloads().iter().map(|s| s.path.as_str()).collect();
        assert_eq!(paths, ["a.sats", "b.sats", "c.dats"]);
    }

    // --- `val rec` -------------------------------------------------

    #[test]
    fn a_val_with_a_literal_pattern_asserts_the_value() {
        // `val- 55 = _55` — the pattern must match, and a literal pattern
        // is an assertion on the value.
        let body = impl_body("implement main0 () = { val _55 = 55 val- 55 = _55 }");
        let Expr::Let(_, inner) = &body else {
            panic!("got {body:?}")
        };
        let Expr::Case(scrut, arms) = &**inner else {
            panic!("got {body:?}")
        };
        assert!(
            matches!(&**scrut, Expr::Var(n) if n == "_55"),
            "got {body:?}"
        );
        assert_eq!(arms[0].0, Pattern::Int(55));
        // no fallback: a non-match leaves through `exit`
        assert_eq!(arms.len(), 2);
    }

    #[test]
    fn a_val_with_a_constructor_pattern_destructures_it() {
        // `val cons(n, ns) = xs` — a pattern that binds the fields
        // scopes over everything that follows it in the block.
        let body = impl_body("implement main0 () = { val cons(n, ns) = xs val () = g(n, ns) }");
        // The pattern is the block's first binding, so the match is the
        // block itself; a name bound before it would wrap it in a `let`.
        let Expr::Case(scrut, arms) = &body else {
            panic!("got {body:?}")
        };
        assert!(
            matches!(&**scrut, Expr::Var(n) if n == "xs"),
            "got {body:?}"
        );
        assert_eq!(
            arms[0].0,
            Pattern::Ctor(
                "cons".into(),
                vec![Pattern::Var("n".into()), Pattern::Var("ns".into())]
            )
        );
    }

    #[test]
    fn val_rec_binds_a_chain_of_mutually_recursive_values() {
        // `val rec a = ... and b = ...` — each binding may mention the
        // others, which is what a mutually recursive lazy value needs.
        let p = Parser::parse("val rec a: int = f(b) and b: int = f(a)\nimplement main0 () = ()")
            .expect("parse");
        assert_eq!(p.defs().len(), 3, "got {:?}", p.defs());
        let Def::Val(v0) = &p.defs()[0] else { panic!() };
        let Def::Val(v1) = &p.defs()[1] else { panic!() };
        assert_eq!(v0.name, "a");
        assert_eq!(v1.name, "b");
        assert_eq!(v0.ty, Some(Ty::Name("int".into())));
    }

    #[test]
    fn parses_a_datavtype_as_a_datatype() {
        // `datavtype` — a datatype whose values are linear.  The views
        // that make it linear are erased here, so it parses as an
        // ordinary datatype and its constructors exist at runtime.
        let p = Parser::parse(
            "datavtype bintree(a) = BTnil of () | BTcons of (bintree a, a, bintree a)",
        )
        .expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else {
            panic!("got {:?}", &p.defs()[0])
        };
        assert_eq!(d.name, "bintree");
        assert_eq!(d.ctors.len(), 2);
        assert_eq!(d.ctors[0].name, "BTnil");
        assert_eq!(d.ctors[1].name, "BTcons");
    }

    #[test]
    fn a_constructor_quantified_over_its_indices_is_read() {
        // `| {n:nat} btnode (a, n) of (int(n), a)` — an indexed
        // constructor whose index variables are declared in braces before
        // its name. Both the binder and indexed result survive so pattern
        // checking can invert the constructor later.
        let p =
            Parser::parse("datatype btree(a) = BTleaf | {n:nat} BTnode (a, n) of (int(n), a)\n")
                .expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else {
            panic!("got {:?}", &p.defs()[0])
        };
        assert_eq!(d.ctors[1].name, "BTnode");
        assert_eq!(d.ctors[1].universals[0].vars[0].0, "n");
        assert_eq!(
            d.ctors[1].result,
            Some(Ty::Index(
                Box::new(Ty::App("btree".into(), vec![Ty::Name("a".into())])),
                vec![SExp::Var("n".into())],
            ))
        );
        assert_eq!(d.ctors[1].fields.len(), 2);
    }

    #[test]
    fn a_datatype_group_joined_by_and_reads_every_clause() {
        // `datatype btree(...) = ... and btreelst(...) = ...` — datatypes
        // that refer to one another are written as one group joined by
        // `and`.  Each clause is a datatype, not a function, so the `and`
        // continues the group instead of starting a function body.
        let p = Parser::parse(
            "datatype btree(a) = BTnil | BTcons of (a, btree(a))\n             and btreelst(a) = BLnil | BLcons of (a, btreelst(a))\n",
        )
        .expect("parse");
        let names: Vec<&str> = p
            .defs()
            .iter()
            .filter_map(|d| match d {
                Def::Datatype(d) => Some(d.name.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(names, vec!["btree", "btreelst"]);
    }

    #[test]
    fn a_bare_type_may_stand_as_a_parameter() {
        // `fun f (list0(a), int): int` — a signature may name a
        // parameter by its type alone, with no variable name.  A bare
        // `int` here is a parameter of type int, not an unannotated
        // variable.
        let p = Parser::parse("extern fun list0_remove_at_exn (list0(a), int): list0(a)\n")
            .expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("expected an extern")
        };
        assert_eq!(d.params.len(), 2);
        assert_eq!(d.params[1].ty, Ty::Name("int".into()));
    }

    // --- template arguments in braces ------------------------------

    #[test]
    fn brace_template_arguments_name_the_instance() {
        // `BTnil{int}()` — ATS writes a template's arguments in braces
        // as readily as in angle brackets, and a group that parses as
        // types names the instance.
        let p = Parser::parse("implement main0 () = { val x = BTnil{int}() }").expect("parse");
        let rendered = format!("{:?}", &p.defs()[0]);
        assert!(
            rendered.contains("Inst(\"BTnil\", [Name(\"int\")])"),
            "got:\n{rendered}"
        );
    }

    // --- parameterized macros --------------------------------------

    #[test]
    fn a_parameterized_macdef_expands_at_the_use_site() {
        // `macdef size (bt) = succ ,(bt)` — a macro with parameters is
        // expanded where it is used, the argument spliced in for the
        // parameter, exactly as ATS's own macro expander does.
        let p = Parser::parse("macdef size (bt) = succ ,(bt)\nimplement main0 () = size (3)")
            .expect("parse");
        let Def::Implement(i) = &p.defs()[0] else {
            panic!("got {:?}", &p.defs()[0])
        };
        assert_eq!(i.body, Expr::Call(Box::new(var("succ")), vec![int(3)]));
    }

    #[test]
    fn a_parameterized_macdef_substitutes_everywhere_in_its_body() {
        // The parameter may appear more than once, and nested.
        let p = Parser::parse("macdef twice (x) = ,(x) + ,(x)\nimplement main0 () = twice (n)")
            .expect("parse");
        let Def::Implement(i) = &p.defs()[0] else {
            panic!("got {:?}", &p.defs()[0])
        };
        assert_eq!(
            i.body,
            Expr::BinOp(BinOp::Add, Box::new(var("n")), Box::new(var("n")))
        );
    }

    #[test]
    fn a_parameterized_macdef_may_be_called_by_juxtaposition() {
        // `free bt1` — a one-parameter macro used without parentheses:
        // the following atom is the argument.
        let p = Parser::parse("macdef free (bt) = g ,(bt)\nimplement main0 () = free x")
            .expect("parse");
        let Def::Implement(i) = &p.defs()[0] else {
            panic!("got {:?}", &p.defs()[0])
        };
        assert_eq!(i.body, Expr::Call(Box::new(var("g")), vec![var("x")]));
    }

    #[test]
    fn a_comma_prefixed_expression_splices() {
        // `f(,(x))` inside a macro body — the comma is the splice
        // marker; the expression it prefixes stands on its own, and the
        // use site's argument arrives in its place.
        let p = Parser::parse("macdef m (x) = f(,(x))\nimplement main0 () = m(1)").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else {
            panic!("got {:?}", &p.defs()[0])
        };
        assert_eq!(i.body, Expr::Call(Box::new(var("f")), vec![int(1)]));
    }

    #[test]
    fn a_static_brace_group_after_a_name_is_still_skipped() {
        // `from{n:int} (n)` — the group carries a sort, so it is a
        // quantifier-like static argument, not types, and it contributes
        // nothing.
        let p = Parser::parse("fun f(): int = from{n:int} (1)").expect("parse");
        let rendered = format!("{:?}", &p.defs()[0]);
        assert!(
            !rendered.contains("Inst(\"from\""),
            "a static group was read as a template argument:\n{rendered}"
        );
        assert!(
            !rendered.contains("StaticInst"),
            "a binder was read as an argument:\n{rendered}"
        );
    }

    #[test]
    fn parses_a_datatype_without_parameters() {
        let p = Parser::parse("datatype color = red | green | blue").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else {
            panic!()
        };
        assert_eq!(d.ty_params, vec![] as Vec<String>);
        assert_eq!(d.ctors.len(), 3);
    }

    #[test]
    fn empty_constructor_list_is_an_error() {
        let err = expect_err("datatype t = ");
        assert!(err.message().contains("constructor"), "{}", err);
    }

    // --- implement ------------------------------------------------

    #[test]
    fn parses_an_implement_clause() {
        let p = Parser::parse("implement main0() = println!(\"hi\")").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else {
            panic!()
        };
        assert_eq!(i.name, "main0");
        assert_eq!(i.ret, None);
        assert_eq!(
            i.body,
            Expr::MacroCall("println!".into(), vec![Expr::StrLit("hi".into())])
        );
    }

    #[test]
    fn implement_may_carry_an_explicit_return_type() {
        let p = Parser::parse("implement f(): int = 1").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else {
            panic!()
        };
        assert_eq!(i.ret, Some(Ty::Name("int".into())));
    }

    // --- expressions: precedence ----------------------------------

    #[test]
    fn multiplication_binds_tighter_than_addition() {
        assert_eq!(
            body_of("fun f(): int = 1 + 2 * 3"),
            Expr::BinOp(
                BinOp::Add,
                Box::new(int(1)),
                Box::new(Expr::BinOp(BinOp::Mul, Box::new(int(2)), Box::new(int(3))))
            )
        );
        assert_eq!(
            body_of("fun f(): int = 1 * 2 + 3"),
            Expr::BinOp(
                BinOp::Add,
                Box::new(Expr::BinOp(BinOp::Mul, Box::new(int(1)), Box::new(int(2)))),
                Box::new(int(3))
            )
        );
    }

    #[test]
    fn comparisons_bind_looser_than_arithmetic() {
        assert_eq!(
            body_of("fun f(x: int): int = x + 1 = 2"),
            Expr::BinOp(
                BinOp::Eq,
                Box::new(Expr::BinOp(
                    BinOp::Add,
                    Box::new(var("x")),
                    Box::new(int(1))
                )),
                Box::new(int(2))
            )
        );
    }

    #[test]
    fn boolean_connectives_are_loosest_and_left_associative() {
        assert_eq!(
            body_of("fun f(a: bool, b: bool): bool = a andalso b orelse a"),
            Expr::BinOp(
                BinOp::Orelse,
                Box::new(Expr::BinOp(
                    BinOp::Andalso,
                    Box::new(var("a")),
                    Box::new(var("b"))
                )),
                Box::new(var("a"))
            )
        );
        assert_eq!(
            body_of("fun f(a: bool, b: bool, c: bool): bool = a andalso b andalso c"),
            Expr::BinOp(
                BinOp::Andalso,
                Box::new(Expr::BinOp(
                    BinOp::Andalso,
                    Box::new(var("a")),
                    Box::new(var("b"))
                )),
                Box::new(var("c"))
            )
        );
    }

    #[test]
    fn mod_division_and_multiplication_share_a_precedence_level() {
        assert_eq!(
            body_of("fun f(x: int, y: int): int = x * y mod 2"),
            Expr::BinOp(
                BinOp::Mod,
                Box::new(Expr::BinOp(
                    BinOp::Mul,
                    Box::new(var("x")),
                    Box::new(var("y"))
                )),
                Box::new(int(2))
            )
        );
    }
    #[test]
    fn percent_is_the_modulo_operator() {
        // `x % 3` — the `%` that opens an inline-C block when it is
        // followed by `{` is the modulo operator when used as a binary
        // infix, sharing `mod`'s precedence.
        let Expr::BinOp(BinOp::Mod, a, b) = body_of("fun f(x: int): int = x % 3") else {
            panic!("expected a modulo")
        };
        assert_eq!(*a, Expr::Var("x".into()));
        assert_eq!(*b, int(3));
    }

    // --- expressions: structure -----------------------------------

    #[test]
    fn parses_if_then_else() {
        assert_eq!(
            body_of("fun fact(n: int): int = if n = 0 then 1 else 2"),
            Expr::IfThenElse(
                Box::new(Expr::BinOp(BinOp::Eq, Box::new(var("n")), Box::new(int(0)))),
                Box::new(int(1)),
                Box::new(int(2)),
            )
        );
    }

    #[test]
    fn if_without_else_is_a_statement() {
        // ATS allows the one-armed `if` as a statement.  The missing arm
        // is unit, so the whole form has type void.
        assert_eq!(
            impl_body("implement main0() = if true then println!(\"hi\")"),
            Expr::IfThenElse(
                Box::new(Expr::BoolLit(true)),
                Box::new(Expr::MacroCall(
                    "println!".into(),
                    vec![Expr::StrLit("hi".into())]
                )),
                Box::new(Expr::Unit),
            )
        );
    }

    // --- datatype declarations --------------------------------------

    fn ctors_of(source: &str) -> Vec<Ctor> {
        let p = Parser::parse(source).expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else {
            panic!("expected a datatype")
        };
        d.ctors.clone()
    }

    #[test]
    fn a_constructor_may_be_written_with_of() {
        // `C of (t, u)` is how ATS spells it; `C(t, u)` is accepted too.
        let c = ctors_of("datatype t = A of (int, bool) | B of () | C");
        assert_eq!(c[0].name, "A");
        assert_eq!(
            c[0].fields,
            vec![Ty::Name("int".into()), Ty::Name("bool".into())]
        );
        assert!(
            c[1].fields.is_empty(),
            "`of ()` is a constructor with no fields"
        );
        assert!(c[2].fields.is_empty(), "a bare name has no fields either");
    }

    #[test]
    fn a_constructor_may_take_one_unparenthesized_field() {
        let c = ctors_of("datatype t = Some of int | None of ()");
        assert_eq!(c[0].fields, vec![Ty::Name("int".into())]);
    }

    #[test]
    fn a_datatype_may_take_type_parameters() {
        let p = Parser::parse("datatype list0(a) = list0_nil of () | list0_cons of (a, list0(a))")
            .expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else {
            panic!("expected a datatype")
        };
        assert_eq!(d.ty_params, vec!["a".to_string()]);
        assert_eq!(d.ctors[1].fields[0], Ty::Name("a".into()));
        assert_eq!(
            d.ctors[1].fields[1],
            Ty::App("list0".into(), vec![Ty::Name("a".into())])
        );
    }

    #[test]
    fn a_leading_bar_before_the_first_constructor_is_optional() {
        assert_eq!(ctors_of("datatype t = | A | B").len(), 2);
    }

    #[test]
    fn a_datatype_parameter_may_carry_a_sort() {
        let p = Parser::parse("datatype list0(a:t@ype) = nil0 of ()").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else {
            panic!("expected a datatype")
        };
        assert_eq!(d.ty_params, vec!["a".to_string()]);
    }

    // --- top-level values -------------------------------------------

    #[test]
    fn a_val_may_stand_at_the_top_level() {
        let p = Parser::parse("val limit = 10").expect("parse");
        let Def::Val(v) = &p.defs()[0] else {
            panic!("expected a val, got {:?}", p.defs()[0])
        };
        assert_eq!(v.name, "limit");
        assert_eq!(v.value, int(10));
        assert_eq!(v.ty, None);
    }

    #[test]
    fn a_top_level_val_may_be_annotated() {
        let p = Parser::parse("val limit: int = 10").expect("parse");
        let Def::Val(v) = &p.defs()[0] else {
            panic!("expected a val")
        };
        assert_eq!(v.ty, Some(ty("int")));
    }

    #[test]
    fn the_empty_termination_metric_is_skipped() {
        // `.<>.` — the lexer reads `<>` as the not-equal token, so the
        // empty metric arrives as three tokens rather than four.
        let p = Parser::parse("fun f {n:nat} .<>. (n: int): int = n").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else {
            panic!("expected a fun")
        };
        assert_eq!(f.name, "f");
    }

    // --- templates and declarations ---------------------------------

    #[test]
    fn an_extern_fun_declares_a_signature() {
        let p = Parser::parse("extern fun twice (x: int): int").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("expected an extern, got {:?}", p.defs()[0])
        };
        assert_eq!(d.name, "twice");
        assert_eq!(d.params[0].ty, ty("int"));
        assert_eq!(d.ret, ty("int"));
        assert!(d.ty_params.is_empty());
    }

    #[test]
    fn an_extern_template_records_its_type_parameters() {
        let p = Parser::parse("extern fun{a:t@ype} size (xs: int): int").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("expected an extern")
        };
        assert_eq!(d.ty_params, vec!["a".to_string()]);
    }

    #[test]
    fn a_template_definition_records_its_type_parameters() {
        let p = Parser::parse("fun{a:t0p} ident (x: a): a = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else {
            panic!("expected a fun")
        };
        assert_eq!(f.ty_params, vec!["a".to_string()]);
    }

    #[test]
    fn an_implement_may_leave_its_parameters_untyped() {
        // The types come from the `extern` declaration above it, so the
        // definition need not repeat them.
        let p = Parser::parse("extern fun twice (x: int): int implement twice (x) = x + x")
            .expect("parse");
        let Def::Implement(i) = &p.defs()[1] else {
            panic!("expected an implement, got {:?}", p.defs()[1])
        };
        assert_eq!(i.params.len(), 1);
        assert_eq!(i.params[0].name, "x");
    }

    #[test]
    fn an_implement_records_the_template_parameters_it_binds() {
        let p = Parser::parse("extern fun{a:t@ype} f (x: a): int implement{a} f (x) = 0")
            .expect("parse");
        let Def::Implement(i) = &p.defs()[1] else {
            panic!("expected an implement")
        };
        assert_eq!(i.ty_params, vec!["a".to_string()]);
    }

    #[test]
    fn an_unparsable_extern_is_still_skipped() {
        // Foreign declarations carry syntax the subset does not model
        // (`= "ext#name"`, linear types).  Those must go on being ignored
        // rather than becoming parse errors.
        let p = Parser::parse(
            "extern fun weird {n:nat} (x: &int >> int n): void = \"ext#weird\" fun g(): int = 1",
        )
        .expect("parse");
        assert!(p
            .defs()
            .iter()
            .any(|d| matches!(d, Def::Fun(f) if f.name == "g")));
    }

    // --- case and patterns -----------------------------------------

    fn arms(source: &str) -> Vec<(Pattern, Expr)> {
        let Expr::Case(_, arms) = impl_body(source) else {
            panic!("expected a case")
        };
        arms
    }

    #[test]
    fn parses_a_case_with_constructor_patterns() {
        let a = arms("implement main0() = case xs of | nil() => 0 | cons(x, r) => 1");
        assert_eq!(a.len(), 2);
        assert_eq!(a[0].0, Pattern::Ctor("nil".into(), vec![]));
        assert_eq!(
            a[1].0,
            Pattern::Ctor(
                "cons".into(),
                vec![Pattern::Var("x".into()), Pattern::Var("r".into())]
            )
        );
        assert_eq!(a[1].1, int(1));
    }

    #[test]
    fn a_leading_bar_is_optional() {
        let a = arms("implement main0() = case xs of nil() => 0 | cons(x, r) => 1");
        assert_eq!(a.len(), 2);
    }

    #[test]
    fn the_exhaustiveness_marker_is_part_of_the_keyword() {
        // `case+` asks the type checker for an exhaustiveness proof; the
        // arms are the same either way.
        assert_eq!(arms("implement main0() = case+ xs of | _ => 0").len(), 1);
    }

    #[test]
    fn a_bare_name_pattern_binds_but_a_nullary_constructor_tests() {
        // `x` binds; `nil()` tests.  The parentheses are what tell them
        // apart, which is exactly how ATS reads them.
        let a = arms("implement main0() = case xs of | other => 0");
        assert_eq!(a[0].0, Pattern::Var("other".into()));
    }

    #[test]
    fn parses_literal_and_wildcard_patterns() {
        let a = arms("implement main0() = case n of | 0 => 1 | _ => 2");
        assert_eq!(a[0].0, Pattern::Int(0));
        assert_eq!(a[1].0, Pattern::Wildcard);
    }

    #[test]
    fn parses_a_tuple_pattern() {
        let a = arms("implement main0() = case p of | (x, y) => 0");
        assert_eq!(
            a[0].0,
            Pattern::Tuple(vec![Pattern::Var("x".into()), Pattern::Var("y".into())])
        );
    }

    #[test]
    fn a_case_arm_may_hold_a_let() {
        let a = arms("implement main0() = case xs of | cons(x, r) => let val y = x in y end");
        assert!(matches!(a[0].1, Expr::Let(..)), "got {:?}", a[0].1);
    }

    // --- ascription and indexing -----------------------------------

    #[test]
    fn a_type_ascription_is_kept_as_the_claim_it_is() {
        // `(e): int` says what `e` should be, which is a claim — and
        // there is a checker to make it to.  The value is untouched, so
        // every stage after the checker looks through it.
        let body = impl_body("implement main0() = (1 + 2): int");
        let Expr::Ascribe(inner, ty) = &body else {
            panic!("{body:?}")
        };
        assert_eq!(
            **inner,
            Expr::BinOp(BinOp::Add, Box::new(int(1)), Box::new(int(2)))
        );
        assert_eq!(*ty, Ty::Name("int".into()));
    }

    #[test]
    fn an_ascription_may_name_a_dependent_type() {
        // `intGte(0)` is where an unbounded integer becomes a bounded
        // one, and the only line in the file that says so.
        let body = impl_body("implement main0() = 5: intGte(0)");
        let Expr::Ascribe(inner, ty) = &body else {
            panic!("{body:?}")
        };
        assert_eq!(**inner, int(5));
        assert_eq!(
            *ty,
            Ty::Index(Box::new(Ty::Name("intGte".into())), vec![SExp::IntLit(0)])
        );
    }

    #[test]
    fn indexing_parses_as_an_index_expression() {
        assert_eq!(
            impl_body("implement main0() = argv[1]"),
            Expr::Index(Box::new(var("argv")), Box::new(int(1)))
        );
    }

    #[test]
    fn indexing_binds_tighter_than_arithmetic() {
        assert_eq!(
            impl_body("implement main0() = xs[0] + 1"),
            Expr::BinOp(
                BinOp::Add,
                Box::new(Expr::Index(Box::new(var("xs")), Box::new(int(0)))),
                Box::new(int(1))
            )
        );
    }

    #[test]
    fn main_may_take_argc_and_argv_without_annotations() {
        // Their types are fixed by the language, so ATS lets them go
        // unwritten.
        let p = Parser::parse("implement main0(argc, argv) = println!(argc)").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else {
            panic!("expected an implement")
        };
        assert_eq!(i.params.len(), 2);
        assert_eq!(i.params[0].name, "argc");
        assert_eq!(i.params[0].ty, Ty::Name("int".into()));
        assert_eq!(i.params[1].name, "argv");
    }

    // --- skipping declarations without losing the ones that matter -

    #[test]
    fn a_proof_binding_keeps_its_proof_and_the_block_around_it() {
        // `prval () = fact_ind{n}()` is proof-level: it is kept, marked,
        // and the body that follows it survives.  The `{n}` inside must
        // not be mistaken for the end of the enclosing block, or the
        // `in` after it is never seen.
        let body = impl_body("implement main0() = let prval () = fact_ind{n}() in println!(1) end");
        let Expr::Let(binds, rest) = &body else {
            panic!("{body:?}")
        };
        assert!(binds[0].proof);
        assert_eq!(**rest, Expr::MacroCall("println!".into(), vec![int(1)]));
    }

    #[test]
    fn a_proof_binding_whose_left_hand_side_is_a_pattern_is_still_kept() {
        let body = impl_body(
            "implement main0() = let prval EQINT() = eqint_make{n,0}[x] in println!(2) end",
        );
        let Expr::Let(binds, rest) = &body else {
            panic!("{body:?}")
        };
        assert!(binds[0].proof);
        assert_eq!(**rest, Expr::MacroCall("println!".into(), vec![int(2)]));
    }

    #[test]
    fn a_block_still_ends_at_its_closing_brace() {
        // The depth tracking must not swallow a genuine block terminator.
        let body = impl_body("implement main0() = { val x = 1 println!(x) }");
        assert!(matches!(body, Expr::Let(..)), "got {body:?}");
    }

    // --- sequencing, wildcards, template arguments -----------------

    #[test]
    fn a_parenthesized_sequence_runs_in_order() {
        // `(a; b)` evaluates `a` for its effect, then yields `b`.  It is
        // the same construct as a `let` with a discard binding, so it
        // desugars to one.
        let body = impl_body("implement main0() = (println!(\"a\"); println!(\"b\"))");
        let Expr::Let(binds, tail) = &body else {
            panic!("expected a let, got {body:?}")
        };
        assert_eq!(binds.len(), 1);
        assert_eq!(binds[0].name, None, "the first element is discarded");
        assert_eq!(
            binds[0].value,
            Expr::MacroCall("println!".into(), vec![Expr::StrLit("a".into())])
        );
        assert_eq!(
            **tail,
            Expr::MacroCall("println!".into(), vec![Expr::StrLit("b".into())])
        );
    }

    #[test]
    fn a_longer_sequence_nests_to_the_right() {
        let body =
            impl_body("implement main0() = (println!(\"a\"); println!(\"b\"); println!(\"c\"))");
        let Expr::Let(_, tail) = &body else {
            panic!("expected a let")
        };
        assert!(
            matches!(**tail, Expr::Let(..)),
            "expected the rest to nest, got {tail:?}"
        );
    }

    #[test]
    fn a_wildcard_is_an_expression() {
        // `_` stands for a value the caller does not name.
        let body = impl_body("implement main0() = f(_)");
        assert_eq!(body, Expr::Call(Box::new(var("f")), vec![Expr::Wildcard]));
    }

    #[test]
    fn template_arguments_on_a_call_are_recorded() {
        // `gfact<int>(12)` picks an instantiation, and which one is
        // needed later: monomorphisation turns each into its own
        // function, so the types are kept rather than dropped.
        let body = impl_body("implement main0() = gfact<int>(12)");
        assert_eq!(
            body,
            Expr::Call(
                Box::new(Expr::Inst("gfact".into(), vec![Ty::Name("int".into())])),
                vec![int(12)]
            )
        );
    }

    #[test]
    fn brace_arguments_on_a_call_name_the_instance() {
        // `cons{int}(l, r)` — a brace group that parses as types names
        // the instance, exactly as `cons<int>(l, r)` does; ATS uses the
        // two notations interchangeably for template arguments.
        let body = impl_body("implement main0() = cons{int}(1, 2)");
        assert_eq!(
            body,
            Expr::Call(
                Box::new(Expr::Inst("cons".into(), vec![Ty::Name("int".into())])),
                vec![int(1), int(2)]
            )
        );
    }

    // --- the type grammar of real ATS ------------------------------

    fn ty(name: &str) -> Ty {
        Ty::Name(name.into())
    }

    fn param_ty(source: &str) -> Ty {
        let p = Parser::parse(source).expect("parse");
        let Def::Fun(f) = &p.defs()[0] else {
            panic!("expected a fun def")
        };
        f.params[0].ty.clone()
    }

    #[test]
    fn a_by_reference_parameter_keeps_its_underlying_type() {
        // `&int` says the callee may write through the parameter.  That is
        // a calling convention, not a different type.
        assert_eq!(param_ty("fun f(x: &int): int = 1"), ty("int"));
    }

    #[test]
    fn a_linear_parameter_keeps_its_underlying_type() {
        // `!t` borrows a linear value for the call's duration.
        assert_eq!(param_ty("fun f(x: !int): int = 1"), ty("int"));
    }

    #[test]
    fn an_uninitialized_type_keeps_its_underlying_type() {
        // `int?` is an `int` whose storage is not yet written.
        assert_eq!(param_ty("fun f(x: int?): int = 1"), ty("int"));
    }

    #[test]
    fn a_tuple_type_parses_into_its_components() {
        assert_eq!(
            param_ty("fun f(x: (int, bool)): int = 1"),
            Ty::Tuple(vec![ty("int"), ty("bool")])
        );
    }

    #[test]
    fn a_flat_tuple_type_parses_like_a_boxed_one() {
        // `@(...)` is the unboxed spelling; the components are the same.
        assert_eq!(
            param_ty("fun f(x: @(int, int)): int = 1"),
            Ty::Tuple(vec![ty("int"), ty("int")])
        );
    }

    #[test]
    fn a_type_application_records_every_argument_as_written() {
        // `list(int, n)` carries an element type and a length.  Nothing
        // here can tell a type variable from a static index — `a` and `n`
        // look the same — so the parser keeps both and leaves the
        // distinction to whoever assigns them meaning.
        assert_eq!(
            param_ty("fun f(x: bag(int, n)): int = 1"),
            Ty::App("bag".into(), vec![ty("int"), ty("n")])
        );
    }

    // --- mutable state: `var`, `:=`, `while`, `for` ----------------

    #[test]
    fn a_var_declaration_binds_a_mutable_cell() {
        let body = impl_body("implement main0() = let var x: int = 1 in x end");
        let Expr::Let(binds, _) = &body else {
            panic!("expected a let, got {body:?}")
        };
        assert_eq!(binds.len(), 1);
        assert!(binds[0].mutable, "`var` must bind a mutable cell");
        assert_eq!(binds[0].name.as_deref(), Some("x"));
        assert_eq!(binds[0].value, int(1));
    }

    #[test]
    fn a_val_declaration_is_still_immutable() {
        let body = impl_body("implement main0() = let val x: int = 1 in x end");
        let Expr::Let(binds, _) = &body else {
            panic!("expected a let")
        };
        assert!(!binds[0].mutable);
    }

    #[test]
    fn an_uninitialized_var_gets_a_zero_of_its_type() {
        // `var i: int` — ATS forbids reading it before it is written, so
        // materializing a zero is observationally equivalent.
        let body = impl_body("implement main0() = let var i: int in i end");
        let Expr::Let(binds, _) = &body else {
            panic!("expected a let")
        };
        assert!(binds[0].mutable);
        assert_eq!(binds[0].value, int(0));
    }

    #[test]
    fn parses_an_assignment() {
        let body = impl_body("implement main0() = let var x: int = 1 in x := 5 end");
        let Expr::Let(_, inner) = &body else {
            panic!("expected a let")
        };
        assert_eq!(**inner, Expr::Assign("x".into(), Box::new(int(5))));
    }

    #[test]
    fn a_compound_assignment_expands_to_the_operator() {
        // `x :=+ 2` means `x := x + 2`; ATS spells the operator into the
        // assignment rather than into a separate form.
        let body = impl_body("implement main0() = let var x: int = 1 in x :=+ 2 end");
        let Expr::Let(_, inner) = &body else {
            panic!("expected a let")
        };
        assert_eq!(
            **inner,
            Expr::Assign(
                "x".into(),
                Box::new(Expr::BinOp(
                    BinOp::Add,
                    Box::new(var("x")),
                    Box::new(int(2))
                ))
            )
        );
    }

    #[test]
    fn parses_a_while_loop() {
        let body = impl_body("implement main0() = while (true) println!(\"x\")");
        assert_eq!(
            body,
            Expr::While(
                Box::new(Expr::BoolLit(true)),
                Box::new(Expr::MacroCall(
                    "println!".into(),
                    vec![Expr::StrLit("x".into())]
                )),
            )
        );
    }

    #[test]
    fn parses_a_for_loop_with_three_clauses() {
        let body = impl_body("implement main0() = for (i := 0; i < 3; i :=+ 1) println!(i)");
        let Expr::For(init, cond, step, _) = &body else {
            panic!("expected a for loop, got {body:?}")
        };
        assert_eq!(**init, Expr::Assign("i".into(), Box::new(int(0))));
        assert_eq!(
            **cond,
            Expr::BinOp(BinOp::Lt, Box::new(var("i")), Box::new(int(3)))
        );
        assert_eq!(
            **step,
            Expr::Assign(
                "i".into(),
                Box::new(Expr::BinOp(
                    BinOp::Add,
                    Box::new(var("i")),
                    Box::new(int(1))
                ))
            )
        );
    }

    #[test]
    fn parses_let_in_end_bindings() {
        assert_eq!(
            body_of("fun f(x: int): int = let val y = x + 1 in y * 2 end"),
            Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: Some("y".into()),
                    ty: None,
                    value: Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(int(1))),
                    mutable: false
                }],
                Box::new(Expr::BinOp(
                    BinOp::Mul,
                    Box::new(var("y")),
                    Box::new(int(2))
                )),
            )
        );
    }

    #[test]
    fn let_bindings_may_have_type_annotations_and_discards() {
        let p = Parser::parse("fun f(): int = let val x: int = 1; val () = g() in x end")
            .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else {
            panic!("expected let")
        };
        assert_eq!(binds.len(), 2);
        assert_eq!(binds[0].ty, Some(Ty::Name("int".into())));
        assert_eq!(binds[1].name, None); // val () = g();  discard binding
    }

    #[test]
    fn one_declaration_may_carry_several_bindings_joined_by_and() {
        // `val a = 1 and b = 2` is a single declaration with two
        // bindings.  ATS binds them simultaneously; the run below is
        // lowered sequentially, which agrees whenever the right-hand
        // sides do not mention a name the same declaration rebinds.
        let p =
            Parser::parse("fun f(): int = let val a = 1 and b = 2 in a + b end").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else {
            panic!("expected let")
        };
        assert_eq!(binds.len(), 2);
        assert_eq!(binds[0].name.as_deref(), Some("a"));
        assert_eq!(binds[1].name.as_deref(), Some("b"));
        assert_eq!(binds[1].value, int(2));
    }

    #[test]
    fn a_dot_and_a_number_project_out_of_a_tuple() {
        assert_eq!(
            body_of("fun f(xs: (int, int)): int = xs.0 + xs.1"),
            Expr::BinOp(
                BinOp::Add,
                Box::new(Expr::Proj(Box::new(var("xs")), 0)),
                Box::new(Expr::Proj(Box::new(var("xs")), 1)),
            )
        );
    }

    #[test]
    fn a_projection_can_be_assigned_to() {
        assert_eq!(
            body_of("fun f(xs: (int, int)): void = xs.0 := 7"),
            Expr::Store(
                Box::new(Expr::Proj(Box::new(var("xs")), 0)),
                Box::new(int(7))
            )
        );
    }

    #[test]
    fn a_typedef_names_a_type_and_is_expanded_where_it_is_used() {
        let p = Parser::parse("typedef T = int\nfun f(x: T): T = x").expect("parse");
        let Def::Fun(f) = p
            .defs()
            .iter()
            .find(|d| matches!(d, Def::Fun(_)))
            .expect("fun")
        else {
            panic!()
        };
        assert_eq!(f.params[0].ty, Ty::Name("int".into()));
        assert_eq!(f.ret, Ty::Name("int".into()));
    }

    #[test]
    fn a_typedef_may_name_a_tuple() {
        let p = Parser::parse("typedef T2 = (int, int)\nfun f(x: T2): int = x.0").expect("parse");
        let Def::Fun(f) = p
            .defs()
            .iter()
            .find(|d| matches!(d, Def::Fun(_)))
            .expect("fun")
        else {
            panic!()
        };
        assert_eq!(
            f.params[0].ty,
            Ty::Tuple(vec![Ty::Name("int".into()), Ty::Name("int".into())])
        );
    }

    #[test]
    fn a_proof_component_is_erased_from_what_a_value_is() {
        // `(PROOF | int)` is a value of type `int` carrying a proof.
        // The proof is kept, because it is what the checker reasons
        // with; what the value *is* stays `int`, which is what every
        // stage after the checker asks.
        let p = Parser::parse("fun f(x: int): (FACT(n, r) | int) = (pf | x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.ret.erased(), Ty::Name("int".into()));
        assert!(
            f.ret.proof().is_some(),
            "the proposition is kept: {:?}",
            f.ret
        );
    }

    #[test]
    fn a_proof_component_is_erased_from_what_an_expression_evaluates_to() {
        let body = body_of("fun f(x: int): int = (pf | x)");
        let Expr::ProofPair(proof, value) = &body else {
            panic!("{body:?}")
        };
        assert_eq!(**proof, var("pf"));
        assert_eq!(**value, var("x"), "what runs is the value half");
    }

    #[test]
    fn a_proof_argument_is_erased_from_a_call() {
        assert_eq!(
            body_of("fun f(x: int): int = g (pf | x, 1)"),
            Expr::Call(Box::new(var("g")), vec![var("x"), int(1)])
        );
    }

    #[test]
    fn a_proof_component_is_erased_from_a_pattern() {
        let p = Parser::parse("fun f(x: int): int = let val (pf1 | r1) = g(x) in r1 end")
            .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else {
            panic!("expected let")
        };
        assert_eq!(binds[0].name.as_deref(), Some("r1"));
    }

    #[test]
    fn a_termination_metric_is_read_rather_than_skipped() {
        // `.<n>.` is the claim that makes a function *total*: without it
        // a definition may promise anything and satisfy the promise by
        // never returning.  It is a claim, so it is kept.
        let p = Parser::parse("fun f {n:nat} .<n>. (x: int n): int = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.metric, vec![SExp::Var("n".into())]);
        assert_eq!(
            f.universals.len(),
            1,
            "the quantifier must survive the metric"
        );
    }

    #[test]
    fn a_metric_may_be_lexicographic() {
        let p = Parser::parse("fun f {m,n:nat} .<m, n>. (x: int m): int = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.metric, vec![SExp::Var("m".into()), SExp::Var("n".into())]);
    }

    #[test]
    fn a_metric_may_be_an_expression_not_only_a_variable() {
        let p = Parser::parse("fun f {n:nat} .<n-1>. (x: int n): int = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(
            f.metric,
            vec![SExp::App(
                "-".into(),
                vec![SExp::Var("n".into()), SExp::IntLit(1)]
            )]
        );
    }

    #[test]
    fn the_empty_metric_claims_nothing_and_is_recorded_as_nothing() {
        // `.<>.` is ATS for "no metric here".  It must not become a
        // metric with no components, which would be a claim about an
        // empty tuple.
        let p = Parser::parse("fun f {n:nat} .<>. (x: int n): int = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert!(f.metric.is_empty());
        assert_eq!(f.universals.len(), 1);
    }

    #[test]
    fn a_bracket_may_hold_a_bare_proposition_with_nothing_bound() {
        // `[fact(0) == 1] void` is how a proof function states what it
        // proves: no witness is named, because there is nothing to name
        // — the claim *is* the content.  Read as a binder it parses as
        // nothing at all, and the axiom says nothing.
        let p = Parser::parse("extern fun ax (): [fact(0) == 1] void").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("{:?}", p.defs()[0])
        };
        assert_eq!(d.existentials.len(), 1);
        assert!(d.existentials[0].vars.is_empty(), "nothing is bound");
        assert_eq!(
            d.existentials[0].guard,
            Some(SExp::App(
                "==".into(),
                vec![
                    SExp::App("fact".into(), vec![SExp::IntLit(0)]),
                    SExp::IntLit(1)
                ]
            ))
        );
    }

    #[test]
    fn a_proof_function_is_a_signature_like_any_other() {
        // `praxi` declares an axiom: a proof that exists by fiat, whose
        // *result type* is the claim it establishes.  Skipping it threw
        // away the only statement in the file that said anything.
        let p = Parser::parse("extern praxi fact_ind {n:pos} (): [fact(n) == n * fact(n-1)] void")
            .expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("{:?}", p.defs()[0])
        };
        assert_eq!(d.name, "fact_ind");
        assert_eq!(d.universals[0].vars, vec![("n".to_string(), Sort::Pos)]);
        assert_eq!(d.existentials.len(), 1);
    }

    #[test]
    fn a_static_argument_at_a_call_site_is_kept() {
        // `fact_ind{n}()` and `fact_ind{m}()` are the same code and
        // different claims.  An axiom applied at the wrong index is the
        // one mistake a proof language exists to catch, so the index
        // cannot be thrown away on the way in.
        let p = Parser::parse("fun f {n:nat} (x: int n): int = g{n, 0}(x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Call(callee, _) = &f.body else {
            panic!("{:?}", f.body)
        };
        let Expr::StaticInst(inner, at) = &**callee else {
            panic!("{:?}", callee)
        };
        assert_eq!(**inner, Expr::Var("g".into()));
        assert_eq!(*at, vec![SExp::Var("n".into()), SExp::IntLit(0)]);
    }

    #[test]
    fn several_static_argument_groups_are_read_in_order() {
        let p = Parser::parse("fun f {n:nat} (x: int n): int = g{n+1}{n}(x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Call(callee, _) = &f.body else {
            panic!()
        };
        let Expr::StaticInst(_, at) = &**callee else {
            panic!("{:?}", callee)
        };
        assert_eq!(
            *at,
            vec![
                SExp::App("+".into(), vec![SExp::Var("n".into()), SExp::IntLit(1)]),
                SExp::Var("n".into())
            ]
        );
    }

    #[test]
    fn a_group_that_reads_as_a_type_stays_a_type_argument() {
        // `{int}` and `{n}` are the same shape; the parser cannot tell
        // them apart and does not try.  It calls the group what it
        // parses as, and the checker — which can see the callee's
        // quantifiers — re-reads it when the signature wants an index.
        let p = Parser::parse("fun f (): int = g{n}(1)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Call(callee, _) = &f.body else {
            panic!()
        };
        assert_eq!(**callee, Expr::Inst("g".into(), vec![Ty::Name("n".into())]));
    }

    #[test]
    fn a_call_with_no_static_arguments_is_left_unwrapped() {
        let p = Parser::parse("fun f (x: int): int = g(x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Call(callee, _) = &f.body else {
            panic!()
        };
        assert_eq!(**callee, Expr::Var("g".into()));
    }

    #[test]
    fn a_proof_value_becomes_a_binding_the_checker_can_see() {
        // `prval () = fact_ind{n}()` is the line that establishes the
        // claim the rest of the body relies on.  Skipping it threw away
        // the proof and left the body unprovable; emitting it would call
        // a function that was never built.  So it is kept, and marked.
        let p = Parser::parse("fun f {n:nat} (x: int n): int = let prval () = ax{n}() in x end")
            .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else {
            panic!("{:?}", f.body)
        };
        assert_eq!(binds.len(), 1);
        assert!(binds[0].proof, "a proof binding must say so");
        assert_eq!(binds[0].name, None, "`()` names nothing");
        assert!(
            matches!(binds[0].value, Expr::Call(..)),
            "{:?}",
            binds[0].value
        );
    }

    #[test]
    fn a_proof_value_may_be_given_a_name() {
        let p = Parser::parse("fun f {n:nat} (x: int n): int = let prval pf = ax{n}() in x end")
            .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else {
            panic!()
        };
        assert_eq!(binds[0].name.as_deref(), Some("pf"));
        assert!(binds[0].proof);
    }

    #[test]
    fn a_proof_value_bound_by_a_pattern_still_runs_its_proof() {
        // `prval EQINT() = eqint_make{n,0}()` names nothing this
        // compiler tracks, but the call on the right is still what
        // establishes the equality.
        let p =
            Parser::parse("fun f {n:nat} (x: int n): int = let prval EQINT() = mk{n,0}() in x end")
                .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else {
            panic!("{:?}", f.body)
        };
        assert!(binds[0].proof);
        assert!(
            matches!(binds[0].value, Expr::Call(..)),
            "{:?}",
            binds[0].value
        );
    }

    #[test]
    fn a_proof_declaration_that_does_not_parse_is_still_skipped() {
        let p = Parser::parse("fun f (): int = let prval pf = ?? ~~ in 1 end").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert!(
            matches!(f.body, Expr::Let(..) | Expr::IntLit(1)),
            "{:?}",
            f.body
        );
    }

    #[test]
    fn a_dataprop_constructor_becomes_the_signature_it_is() {
        // `dataprop FACT(int,int) = | {n:pos}{r:int} FACTind (n, n*r) of
        // FACT(n-1, r)` declares `FACTind` as a function from a proof of
        // `FACT(n-1,r)` to a proof of `FACT(n, n*r)`.  That is all a
        // constructor of a proposition is, and saying so needs no
        // machinery a function does not already have.
        let p = Parser::parse(
            "dataprop FACT (int, int) = | FACTbas (0, 1) of () \
             | {n:pos}{r:int} FACTind (n, n*r) of FACT (n-1, r)",
        )
        .expect("parse");
        let decl = |name: &str| {
            p.defs()
                .iter()
                .find_map(|d| match d {
                    Def::Extern(d) if d.name == name => Some(d.clone()),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("no `{name}` in {:?}", p.defs()))
        };
        let bas = decl("FACTbas");
        assert!(bas.params.is_empty());
        assert_eq!(
            bas.ret,
            Ty::Index(
                Box::new(Ty::Name("FACT".into())),
                vec![SExp::IntLit(0), SExp::IntLit(1)]
            )
        );
        let ind = decl("FACTind");
        assert_eq!(ind.universals.len(), 2);
        assert_eq!(ind.params.len(), 1, "the proof it consumes");
        assert_eq!(
            ind.ret,
            Ty::Index(
                Box::new(Ty::Name("FACT".into())),
                vec![
                    SExp::Var("n".into()),
                    SExp::App(
                        "*".into(),
                        vec![SExp::Var("n".into()), SExp::Var("r".into())]
                    )
                ]
            )
        );
    }

    #[test]
    fn an_existential_result_may_be_opened_by_naming_its_witness() {
        // `val [r1:int] (pf1 | r1) = fact (x-1)` names the witness the
        // callee refused to name.  Without the name every fact about the
        // returned value is about a variable nobody can mention twice,
        // and the proof that follows has nothing to attach to.
        let p =
            Parser::parse("fun f (x: int): int = let val [r1:int] (pf1 | res) = g(x) in res end")
                .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else {
            panic!("{:?}", f.body)
        };
        assert_eq!(binds[0].opened, vec![("r1".to_string(), Sort::Int)]);
        assert_eq!(
            binds[0].name.as_deref(),
            Some("res"),
            "the value half is what is bound"
        );
        assert!(!binds[0].proof, "the value half runs");
    }

    #[test]
    fn a_binding_that_opens_nothing_says_so() {
        let p = Parser::parse("fun f (x: int): int = let val y = g(x) in y end").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else {
            panic!()
        };
        assert!(binds[0].opened.is_empty());
    }

    #[test]
    fn a_result_type_keeps_the_proof_it_promises() {
        // `[r:int] (FACT(n,r) | int(r))` pins `r` down through the
        // proposition.  Erasing the proof half leaves only `int(r)`, and
        // then `r` has to be recovered from arithmetic that is often
        // nonlinear and out of any linear solver's reach.
        let p = Parser::parse("fun f {n:nat} (x: int n): [r:int] (FACT(n, r) | int(r)) = x")
            .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Ty::Proof(proof, value) = &f.ret else {
            panic!("{:?}", f.ret)
        };
        // A proposition applied to plain names parses as a type
        // application; the checker reads its arguments as index terms.
        assert_eq!(
            **proof,
            Ty::App(
                "FACT".into(),
                vec![Ty::Name("n".into()), Ty::Name("r".into())]
            )
        );
        assert_eq!(
            **value,
            Ty::Index(
                Box::new(Ty::Name("int".into())),
                vec![SExp::Var("r".into())]
            )
        );
        // What the value *is* is still the value half.
        assert_eq!(f.ret.erased(), Ty::Name("int".into()));
        assert_eq!(f.ret.indices(), &[SExp::Var("r".into())]);
    }

    #[test]
    fn a_returned_pair_keeps_the_proof_it_returns() {
        let p = Parser::parse("fun f (x: int): int = (pf | x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::ProofPair(proof, value) = &f.body else {
            panic!("{:?}", f.body)
        };
        assert_eq!(**proof, Expr::Var("pf".into()));
        assert_eq!(**value, Expr::Var("x".into()));
    }

    #[test]
    fn a_plain_parenthesised_expression_is_not_a_pair() {
        let p = Parser::parse("fun f (x: int): int = (x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.body, Expr::Var("x".into()));
    }

    /// The type of `f`'s only parameter.
    fn first_param_ty(src: &str) -> Ty {
        let p = Parser::parse(src).expect("parse");
        let Def::Fun(f) = &p.defs()[0] else {
            panic!("expected a fun")
        };
        f.params[0].ty.clone()
    }

    /// `array(int, n)` — an array of `int`, `n` long.
    fn int_array(size: SExp) -> Ty {
        Ty::Index(
            Box::new(Ty::App("array".into(), vec![Ty::Name("int".into())])),
            vec![size],
        )
    }

    #[test]
    fn an_array_keeps_the_size_it_was_declared_with() {
        // The size is the whole reason to write `array(int, n)` rather
        // than `array(int)`: without it `A[i]` cannot be checked against
        // anything, and a bounds check is the obligation ATS exists to
        // make.
        assert_eq!(
            first_param_ty("fun f {n:nat} (a: array(int, n)): int = 1"),
            int_array(SExp::Var("n".into()))
        );
    }

    #[test]
    fn the_bracket_spelling_of_an_array_is_the_same_array() {
        // `@[int][n]` is a flat array of `n` ints — the same type
        // `array(int, n)` names, written the way a `var` declares one.
        assert_eq!(
            first_param_ty("fun f {n:nat} (a: @[int][n]): int = 1"),
            int_array(SExp::Var("n".into()))
        );
    }

    #[test]
    fn a_by_reference_array_is_the_array_it_refers_to() {
        // `&(@[int][m]) >> _` passes the array by reference and says its
        // view is unchanged.  Neither the `&` nor the `>>` alters what
        // the value is or how long it is.
        assert_eq!(
            first_param_ty("fun f {m:nat} (t: &(@[int][m]) >> _): int = 1"),
            int_array(SExp::Var("m".into()))
        );
    }

    #[test]
    fn an_arrayref_is_an_array_with_its_size() {
        assert_eq!(
            first_param_ty("fun f {n:nat} (a: arrayref(int, n)): int = 1"),
            int_array(SExp::Var("n".into()))
        );
    }

    #[test]
    fn a_size_may_be_an_expression_rather_than_a_variable() {
        assert_eq!(
            first_param_ty("fun f {n:nat} (a: array(int, n+1)): int = 1"),
            int_array(SExp::App(
                "+".into(),
                vec![SExp::Var("n".into()), SExp::IntLit(1)]
            ))
        );
    }

    #[test]
    fn a_run_of_bytes_is_indexed_by_how_many_there_are() {
        // `b0ytes(n)` is `n` bytes, uninitialised; `bytes(n)` is `n`
        // bytes that have been written.  The difference is a view, which
        // this compiler does not track; the length is not, and it is
        // what a bounds check needs.
        for name in ["bytes", "b0ytes"] {
            let ty = first_param_ty(&format!("fun f {{n:pos}} (b: {name}(n)): int = 1"));
            assert_eq!(ty.indices(), &[SExp::Var("n".into())], "{name}: {ty:?}");
        }
    }

    #[test]
    fn an_arrays_size_is_static_and_leaves_no_trace_in_what_it_is() {
        // Emission must not notice any of this: an `array(int, n)` and
        // an `array(int)` are the same bytes.
        assert_eq!(
            first_param_ty("fun f {n:nat} (a: array(int, n)): int = 1").erased(),
            Ty::App("array".into(), vec![Ty::Name("int".into())])
        );
    }

    #[test]
    fn a_block_of_inline_c_survives_to_the_program() {
        // A program that declares `extern fun f = "ext#f"` and defines
        // `f` in a `%{ %}` block used to compile and then fail to link,
        // naming a symbol whose definition was thrown away three stages
        // earlier.  The text is not this compiler's language; it is the
        // toolchain's, and it has to reach it.
        let p = Parser::parse(
            "%{^\nint triple (int n) { return 3 * n; }\n%}\n\
             extern fun triple (n: int): int = \"ext#triple\"\n\
             implement main0 () = println! (triple (2))",
        )
        .expect("parse");
        let c: Vec<&String> = p
            .defs()
            .iter()
            .filter_map(|d| match d {
                Def::InlineC(text) => Some(text),
                _ => None,
            })
            .collect();
        assert_eq!(c.len(), 1, "{:?}", p.defs());
        assert!(c[0].contains("return 3 * n"), "{}", c[0]);
    }

    #[test]
    fn the_marker_that_says_where_the_c_goes_is_not_part_of_it() {
        // `%{^` puts it above the output and `%{$` below.  Neither
        // marker is C, and leaving one in makes the file not compile.
        let p =
            Parser::parse("%{$\nint z = 1;\n%}\nimplement main0 () = println! (0)").expect("parse");
        let Some(Def::InlineC(text)) = p.defs().iter().find(|d| matches!(d, Def::InlineC(_)))
        else {
            panic!("{:?}", p.defs())
        };
        assert!(!text.contains('$'), "the marker survived: {text}");
        assert!(text.trim().starts_with("int z"), "{text}");
    }

    #[test]
    fn a_linear_datatype_says_that_it_is_one() {
        // `datavtype` declares values that must be consumed exactly
        // once.  Parsing it as an ordinary `datatype` erases the only
        // thing that distinguishes it, and the resource discipline that
        // is half of what ATS is for goes unchecked.
        let p = Parser::parse("datavtype box_vt(a) = mk_vt of (a)").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else {
            panic!("{:?}", p.defs()[0])
        };
        assert!(d.linear, "a datavtype is linear");
    }

    #[test]
    fn an_ordinary_datatype_is_not_linear() {
        let p = Parser::parse("datatype box(a) = mk of (a)").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else {
            panic!()
        };
        assert!(!d.linear);
    }

    #[test]
    fn a_dataview_is_linear_as_well() {
        // A `dataview` is a `dataprop` whose proofs are resources: it
        // stands for permission to touch something, and permission that
        // could be used twice would not be permission at all.
        let p = Parser::parse("dataview owned (int) = | own (0) of ()").expect("parse");
        let owned = p
            .defs()
            .iter()
            .any(|d| matches!(d, Def::Extern(e) if e.name == "own" && e.linear));
        assert!(owned, "{:?}", p.defs());
    }

    #[test]
    fn a_borrowed_parameter_says_that_it_is_borrowed() {
        // `!xs` is lent, not given: the caller keeps it, and the body
        // must *not* consume it.  Dropping the `!` makes every borrow
        // look like a handover.
        let p = Parser::parse("fun f (xs: !box_vt(int), ys: box_vt(int)): int = 1").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert!(f.params[0].borrowed, "`!` marks a borrow");
        assert!(!f.params[1].borrowed, "a plain parameter is given");
    }

    #[test]
    fn a_by_reference_parameter_is_borrowed_too() {
        // `&t` passes a cell the caller keeps: the callee may write
        // through it and may not consume it.
        let p = Parser::parse("fun f (a: &int): int = 1").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert!(f.params[0].borrowed);
    }

    #[test]
    fn a_dataprop_that_does_not_parse_is_skipped_not_fatal() {
        let p = Parser::parse("dataprop WEIRD = | ??? \n fun f(): int = 1").expect("parse");
        assert!(p
            .defs()
            .iter()
            .any(|d| matches!(d, Def::Fun(f) if f.name == "f")));
    }

    #[test]
    fn a_proof_function_needs_no_extern_before_it() {
        let p = Parser::parse("praxi ax (): [1 == 1] void").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("{:?}", p.defs()[0])
        };
        assert_eq!(d.name, "ax");
    }

    #[test]
    fn a_proof_function_that_does_not_parse_is_skipped_not_fatal() {
        // The fallback must survive: a proof language this compiler does
        // not model costs its own declaration, never the file.
        let p =
            Parser::parse("praxi weird {a:t@ype} (!list(a) >> list(a)): void\nfun f(): int = 1")
                .expect("parse");
        assert!(p
            .defs()
            .iter()
            .any(|d| matches!(d, Def::Fun(f) if f.name == "f")));
    }

    #[test]
    fn a_bracket_holding_a_binder_is_still_read_as_a_binder() {
        let p = Parser::parse("extern fun g (): [r:nat] int r").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!()
        };
        assert_eq!(d.existentials[0].vars, vec![("r".to_string(), Sort::Nat)]);
        assert_eq!(d.existentials[0].guard, None);
    }

    #[test]
    fn a_brace_holding_only_a_name_is_an_instantiation_and_binds_nothing() {
        // `f{n}(...)` hands a static argument to a call; it is not a
        // quantifier, and reading it as a bare proposition would turn
        // every instantiation into an assumption.
        let p = Parser::parse("fun f {n:nat} (x: int n): int = g{n}(x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.universals.len(), 1);
        assert_eq!(f.universals[0].vars, vec![("n".to_string(), Sort::Nat)]);
    }

    #[test]
    fn an_extern_declaration_records_its_quantifiers_too() {
        // `extern fun f {n:nat} (int n): int` is how the corpus declares
        // everything it implements elsewhere, and a declaration that
        // forgets its quantifier is a promise nobody can keep.
        let p = Parser::parse("extern fun ext {n:nat} (x: int n): int").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("{:?}", p.defs()[0])
        };
        assert_eq!(d.universals.len(), 1);
        assert_eq!(d.universals[0].vars, vec![("n".to_string(), Sort::Nat)]);
    }

    #[test]
    fn a_universal_quantifier_is_recorded_rather_than_skipped() {
        // `{n:nat | n > 0}` is the dependent half of the signature.  It
        // is what makes the type of `f` say something about *which*
        // integers it accepts, so it is kept, not skipped.
        let p = Parser::parse("fun f {n:nat | n > 0} (x: int n): int n = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.universals.len(), 1);
        assert_eq!(f.universals[0].vars, vec![("n".to_string(), Sort::Nat)]);
        assert_eq!(
            f.universals[0].guard,
            Some(SExp::App(
                ">".into(),
                vec![SExp::Var("n".into()), SExp::IntLit(0)]
            ))
        );
    }

    #[test]
    fn a_guard_may_be_several_claims_separated_by_semicolons() {
        // `{i,j:nat | i <= j+1; i+j == n-1}` is one guard written as two
        // conjuncts, and it is how every real ATS loop invariant is
        // spelled.  Failing to read the `;` cost the *whole* quantifier
        // — the sorts included — so a loop lost even its nat-ness.
        let p = Parser::parse("fun loop {i,j:nat | i <= j; i+j == 4} (x: int i): int = x")
            .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.universals.len(), 1);
        assert_eq!(f.universals[0].vars.len(), 2);
        assert_eq!(
            f.universals[0].guard,
            Some(SExp::App(
                "&&".into(),
                vec![
                    SExp::App(
                        "<=".into(),
                        vec![SExp::Var("i".into()), SExp::Var("j".into())]
                    ),
                    SExp::App(
                        "==".into(),
                        vec![
                            SExp::App(
                                "+".into(),
                                vec![SExp::Var("i".into()), SExp::Var("j".into())]
                            ),
                            SExp::IntLit(4)
                        ]
                    ),
                ]
            ))
        );
    }

    #[test]
    fn every_conjunct_of_a_guard_reaches_the_checker_as_a_hypothesis() {
        let p = Parser::parse("fun loop {i,j:nat | i <= j; i+j == 4} (x: int i): int = x")
            .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let hyps: Vec<String> = f.universals[0]
            .hypotheses()
            .iter()
            .map(|h| h.to_string())
            .collect();
        assert!(hyps.contains(&"i >= 0".to_string()), "{hyps:?}");
        assert!(hyps.contains(&"j >= 0".to_string()), "{hyps:?}");
        assert!(hyps.iter().any(|h| h.contains("i <= j")), "{hyps:?}");
    }

    #[test]
    fn several_quantifiers_may_precede_a_signature() {
        let p = Parser::parse("fun f {m,n:nat} {r:int} (x: int m): int = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.universals.len(), 2);
        assert_eq!(f.universals[0].vars.len(), 2);
        assert_eq!(f.universals[1].vars, vec![("r".to_string(), Sort::Int)]);
    }

    #[test]
    fn an_indexed_type_keeps_its_index() {
        let p = Parser::parse("fun f {n:nat} (x: int n): int(n+1) = x + 1").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(
            f.params[0].ty,
            Ty::Index(
                Box::new(Ty::Name("int".into())),
                vec![SExp::Var("n".into())]
            )
        );
        assert_eq!(
            f.ret,
            Ty::Index(
                Box::new(Ty::Name("int".into())),
                vec![SExp::App(
                    "+".into(),
                    vec![SExp::Var("n".into()), SExp::IntLit(1)]
                )]
            )
        );
    }

    #[test]
    fn parses_brace_blocks_as_lets() {
        assert_eq!(
            impl_body("implement main0() = { val x = 1; x + 1 }"),
            Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: Some("x".into()),
                    ty: None,
                    value: int(1),
                    mutable: false
                }],
                Box::new(Expr::BinOp(
                    BinOp::Add,
                    Box::new(var("x")),
                    Box::new(int(1))
                )),
            )
        );
    }

    #[test]
    fn parses_lambdas() {
        assert_eq!(
            body_of("fun f(): int = lam (x: int) => x + 1"),
            Expr::Lam(
                vec![Param {
                    borrowed: false,
                    name: "x".into(),
                    ty: Ty::Name("int".into())
                }],
                None,
                Box::new(Expr::BinOp(
                    BinOp::Add,
                    Box::new(var("x")),
                    Box::new(int(1))
                )),
            )
        );
    }

    #[test]
    fn a_macro_splice_may_follow_another_argument() {
        // The comma that separates two arguments is not the comma that
        // opens a splice, and only what follows it says which is which.
        assert_eq!(
            body_of("macdef get (n) = f (xs, ,(n))\nfun g(x: int): int = get(x)"),
            Expr::Call(Box::new(var("f")), vec![var("xs"), var("x")])
        );
        assert_eq!(
            body_of("macdef get (n) = f (xs, 1)\nfun g(x: int): int = get(x)"),
            Expr::Call(Box::new(var("f")), vec![var("xs"), int(1)])
        );
    }

    #[test]
    fn a_macro_body_may_unquote_its_parameter() {
        // `,(n)` inside a `macdef` body is ATS's unquote: it splices the
        // argument in rather than naming it.  Since a macro is expanded
        // as it is read, the splice has already happened by the time the
        // body is parsed, and the marker means nothing more than
        // parentheses do.
        assert_eq!(
            body_of("macdef twice (n) = ,(n) + ,(n)\nfun f(x: int): int = twice(x)"),
            Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(var("x")))
        );
    }

    #[test]
    fn raise_names_the_exception_it_throws() {
        assert_eq!(
            body_of("fun f(): int = $raise StreamSubscriptExn"),
            Expr::Raise(Box::new(var("StreamSubscriptExn")))
        );
    }

    #[test]
    fn an_exception_declaration_keeps_its_payload() {
        // `exception Found of int` — the payload type, written without
        // parentheses, is kept for the emitter to box and the `try` to
        // read back.
        let p = Parser::parse("exception Found of int").expect("parse");
        assert_eq!(
            p.defs()[0],
            Def::Exception("Found".into(), vec![Ty::Name("int".into())])
        );
        let p = Parser::parse("exception Found of (int, double)").expect("parse");
        assert_eq!(
            p.defs()[0],
            Def::Exception(
                "Found".into(),
                vec![Ty::Name("int".into()), Ty::Name("double".into())]
            )
        );
    }

    #[test]
    fn one_exception_declaration_may_name_several() {
        // `exception A and B of int` — the canonical TESTATS spelling.
        // Each name is its own constructor of `exn`, so each becomes its
        // own definition.
        let p = Parser::parse("exception A and B of int").expect("parse");
        let defs: Vec<Def> = p.defs().to_vec();
        assert_eq!(
            defs,
            vec![
                Def::Exception("A".into(), vec![]),
                Def::Exception("B".into(), vec![Ty::Name("int".into())])
            ]
        );
    }

    #[test]
    fn an_arrow_may_carry_its_effects() {
        // `-<cloref1>` is an arrow that also says the function is a
        // closure.  Who may call it is a question for the type checker;
        // that it *is* an arrow is a question for the parser.
        let p = Parser::parse("extern fun apply (f: (int) -<cloref1> bool): bool").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("expected an extern")
        };
        assert_eq!(
            d.params[0].ty,
            Ty::Fun(
                vec![Ty::Name("int".into())],
                Box::new(Ty::Name("bool".into()))
            )
        );
    }

    #[test]
    fn a_template_parameter_shadows_a_typedef_of_the_same_name() {
        // `implement(res) f<res> (...)` binds `res` as the
        // implementation's own type parameter.  A `typedef res` in scope
        // is an outer name, and a binder shadows one — expanding it here
        // would turn the generic implementation into an instance of
        // whatever the alias happened to mean.
        let p = Parser::parse("typedef res = int\nimplement(res) f<res> (x: res): res = x")
            .expect("parse");
        let Def::Implement(i) = &p.defs()[0] else {
            panic!("expected an implement")
        };
        assert_eq!(i.ty_params, vec!["res".to_string()]);
        assert_eq!(i.instance, vec![Ty::Name("res".into())]);
    }

    #[test]
    fn only_angle_brackets_name_the_instance_an_implement_fills_in() {
        // `implement{a} f {n} (xs) = ...` quantifies over the *index*
        // `n`; it is still the generic implementation.  Reading the
        // brace group as a type argument would file it under an instance
        // nobody ever asks for, and the generic body would be missing.
        let p = Parser::parse("implement{a} f {n} (xs: int): int = xs").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else {
            panic!("expected an implement")
        };
        assert!(
            i.instance.is_empty(),
            "a static argument was read as an instance: {:?}",
            i.instance
        );

        let p = Parser::parse("implement f<int> (xs: int): int = xs").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else {
            panic!("expected an implement")
        };
        assert_eq!(i.instance, vec![Ty::Name("int".into())]);
    }

    #[test]
    fn a_list_literal_becomes_the_conses_that_build_it() {
        // `$list{int}(1, 2)` is list-literal syntax and nothing more, so
        // it is desugared here rather than carried to the emitter as a
        // form of its own — and everything downstream, inference
        // included, then sees an ordinary list.
        assert_eq!(
            body_of("fun f(): list0(int) = $list{int}(1, 2)"),
            Expr::Call(
                Box::new(Expr::Inst(
                    "list0_cons".into(),
                    vec![Ty::Name("int".into())]
                )),
                vec![
                    int(1),
                    Expr::Call(
                        Box::new(Expr::Inst(
                            "list0_cons".into(),
                            vec![Ty::Name("int".into())]
                        )),
                        vec![
                            int(2),
                            Expr::Call(
                                Box::new(Expr::Inst(
                                    "list0_nil".into(),
                                    vec![Ty::Name("int".into())]
                                )),
                                vec![],
                            ),
                        ],
                    ),
                ],
            )
        );
    }

    #[test]
    fn an_assumed_type_is_known_even_above_the_assumption() {
        // `abstype` hides a type; `assume` says what it really is.  The
        // assumption may sit far below the uses — in ordset it is inside
        // a `local` near the end of the file — and it still has to
        // decide what those uses mean.
        let p = Parser::parse(concat!(
            "abstype set (a:t@ype) = ptr\n",
            "fun f(): set(int) = g()\n",
            "assume set (a:t@ype) = list0(a)\n",
        ))
        .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else {
            panic!("expected a fun")
        };
        assert_eq!(f.ret, Ty::App("list0".into(), vec![Ty::Name("int".into())]));
    }

    #[test]
    fn an_at_joined_abstract_linear_type_is_an_alias() {
        // `abst@ype` — the linear (unboxed) abstract type form — is cut
        // by the lexer at the `@` into `abst @ ype`.  It is still a
        // declaration of a type name, so the parser must rejoin the
        // pieces (the way it rejoins a sort name) and know that name the
        // way it knows any other abstract type.
        let p = Parser::parse(concat!(
            "abst@ype int2 = (int, int)\n",
            "fun f (): int2 = (1, 2)\n",
        ))
        .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else {
            panic!("first definition is not a fun")
        };
        assert_eq!(
            f.ret,
            Ty::Tuple(vec![Ty::Name("int".into()), Ty::Name("int".into())])
        );
    }

    #[test]
    fn every_abstract_type_spelling_with_an_at_is_rejoined() {
        // `abst@ype`, `absvt@ype`, `absviewt@ype` — the linear, view and
        // viewtype abstract forms — are all cut at the `@` by the lexer
        // into three tokens.  Only the `abst` one used to be rejoined and
        // read as a type alias; the other two stopped a `.sats` header
        // before its declarations were ever seen.
        let p = Parser::parse(concat!(
            "absvt@ype v = int\n",
            "absviewt@ype a = int\n",
            "fun f (x: v, y: a): int = 1\n",
        ))
        .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else {
            panic!("first definition is not a fun")
        };
        assert_eq!(f.params[0].ty, Ty::Name("int".into()));
        assert_eq!(f.params[1].ty, Ty::Name("int".into()));
    }

    #[test]
    fn a_fun_with_no_body_is_a_declaration() {
        // A `.sats` file states a signature with `fun f (x: int): int`
        // and leaves the body to the `.dats`.  A top-level `fun` with no
        // body is therefore a declaration, not a definition.
        let p = Parser::parse("fun f (x: int): int\n").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("expected an extern declaration")
        };
        assert_eq!(d.name, "f");
        assert_eq!(d.ret, Ty::Name("int".into()));
    }

    #[test]
    fn a_fun_declared_as_a_curried_type_is_a_declaration() {
        // `fun abs_int0 : int -<fun> int = "mac#%"` — the signature is
        // the curried type after the colon, with no parameter list, and
        // the `= "mac#%"` names where the implementation lives rather
        // than providing a body.
        let p = Parser::parse("fun abs_int0 : int -<fun> int = \"mac#%\"\n").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("expected an extern declaration")
        };
        assert_eq!(d.name, "abs_int0");
        assert_eq!(d.params.len(), 1);
        assert_eq!(d.params[0].ty, Ty::Name("int".into()));
        assert_eq!(d.ret, Ty::Name("int".into()));
    }

    #[test]
    fn an_extern_fun_with_a_curried_type_declares_its_parameters() {
        // `extern fun fact : int -> int = "mac#fact"` — a signature with
        // no parenthesised parameter list: the whole type is the curried
        // arrow after the colon, which declares one parameter of `int`
        // returning `int`.  It used to be skipped, so the `implement`
        // that followed found nothing to fill in.
        let p = Parser::parse("extern fun fact : int -> int = \"mac#fact\"\n").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("expected an extern declaration")
        };
        assert_eq!(d.name, "fact");
        assert_eq!(d.params.len(), 1);
        assert_eq!(d.params[0].ty, Ty::Name("int".into()));
        assert_eq!(d.ret, Ty::Name("int".into()));
    }

    #[test]
    fn an_extern_val_with_a_function_type_is_a_function_declaration() {
        let p = Parser::parse("extern val fact: (int) -> int\n").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("expected an extern declaration")
        };
        assert_eq!(d.name, "fact");
        assert_eq!(d.params.len(), 1);
        assert_eq!(d.params[0].ty, Ty::Name("int".into()));
        assert_eq!(d.ret, Ty::Name("int".into()));
    }

    #[test]
    fn a_template_declaration_accepts_a_type_only_parameter() {
        let p =
            Parser::parse("fun cloref1_app {a:t0p;b:vt0p} (f: cfun1(a, b), a): b = \"mac#%\"\n")
                .expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("expected an extern declaration")
        };
        assert_eq!(d.name, "cloref1_app");
        assert_eq!(d.params.len(), 2);
        assert_eq!(d.params[1].ty, Ty::Name("a".into()));
    }

    #[test]
    fn a_declaration_may_have_an_empty_template_group_before_its_name() {
        let p = Parser::parse("fun{} matrix0_of_mtrxszref {a:vt0p}(mtrxszref(a)):<> matrix0(a)\n")
            .expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("expected an extern declaration")
        };
        assert_eq!(d.name, "matrix0_of_mtrxszref");
        assert_eq!(d.ty_params, vec!["a"]);
        assert_eq!(d.params.len(), 1);
    }

    #[test]
    fn an_endif_does_not_consume_the_next_declaration() {
        let p = Parser::parse(
            "#if(0)\n#endif // #if(0)\nfun{} matrix0_of_mtrxszref {a:vt0p}(mtrxszref(a)):<> matrix0(a)\n",
        )
        .expect("parse");
        assert!(p.defs().iter().any(
            |definition| matches!(definition, Def::Extern(d) if d.name == "matrix0_of_mtrxszref")
        ));
    }

    #[test]
    fn an_inline_c_include_does_not_consume_the_next_declaration() {
        let p = Parser::parse(
            "%{#\n#include \"libats/CATS/hashfun.cats\"\n%}\nfun{} inthash_jenkins(uint32):<> uint32\n",
        )
        .expect("parse");
        assert!(p
            .defs()
            .iter()
            .any(|definition| matches!(definition, Def::Extern(d) if d.name == "inthash_jenkins")));
        let Def::Extern(declaration) = &p.defs()[1] else {
            panic!("expected the hash declaration after inline C")
        };
        assert_eq!(declaration.params[0].ty, Ty::Name("int".into()));
        assert_eq!(declaration.ret, Ty::Name("int".into()));
    }

    #[test]
    fn a_bare_double_parameter_is_an_ambient_scalar_type() {
        let p = Parser::parse("fun gvalue_float(double): gvalue = \"mac#%\"\n").expect("parse");
        let Def::Extern(declaration) = &p.defs()[0] else {
            panic!("expected a declaration")
        };
        assert_eq!(declaration.params[0].ty, Ty::Name("double".into()));
    }

    #[test]
    fn an_ml_basis_reference_alias_is_available_to_a_declaration() {
        let p = Parser::parse("fun{} gvalue_ref(gvref): gvalue\n").expect("parse");
        let Def::Extern(declaration) = &p.defs()[0] else {
            panic!("expected a declaration")
        };
        assert_eq!(declaration.params[0].ty, Ty::Name("ptr".into()));
    }

    #[test]
    fn an_imported_bare_type_is_allowed_in_a_declaration_only() {
        let p = Parser::parse("fun{} gvalue_is_nil(gvalue): bool\n").expect("declaration");
        let Def::Extern(declaration) = &p.defs()[0] else {
            panic!("expected a declaration")
        };
        assert_eq!(declaration.params[0].ty, Ty::Name("gvalue".into()));

        let errors = Parser::parse("fun f(x): int = 0\n").expect_err("definition needs a type");
        assert!(errors[0]
            .message()
            .contains("parameter `x` needs a type annotation"));
    }

    #[test]
    fn a_declaration_may_bind_its_type_parameter_after_its_name() {
        let p =
            Parser::parse("fun fun2cloref0 {res:t@ype} (fopr: () -> res): cfun(res) = \"mac#%\"\n")
                .expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("expected an extern declaration")
        };
        assert_eq!(d.name, "fun2cloref0");
        assert_eq!(d.ty_params, vec!["res"]);
        assert_eq!(d.params.len(), 1);
    }

    #[test]
    fn the_prelude_fprint_type_alias_expands_to_two_parameters() {
        let p = Parser::parse("fun fprint_form : fprint_type(form)\n").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("expected an extern declaration")
        };
        assert_eq!(d.params.len(), 2);
        assert_eq!(d.params[0].ty, Ty::Name("FILEref".into()));
        assert_eq!(d.params[1].ty, Ty::Name("form".into()));
        assert_eq!(d.ret, Ty::Name("void".into()));
    }

    #[test]
    fn ambient_library_function_type_aliases_expand() {
        let p = Parser::parse(
            "fun emit_value : emit_type(value)\nfun jsonize_value : jsonize_ftype(value)\n",
        )
        .expect("parse");
        let Def::Extern(emit) = &p.defs()[0] else {
            panic!("expected an emit declaration")
        };
        let Def::Extern(jsonize) = &p.defs()[1] else {
            panic!("expected a jsonize declaration")
        };
        assert_eq!(emit.params.len(), 2);
        assert_eq!(emit.ret, Ty::Name("void".into()));
        assert_eq!(jsonize.params.len(), 1);
        assert_eq!(jsonize.ret, Ty::Name("jsonval".into()));
    }

    #[test]
    fn a_type_qualified_by_a_staload_alias_drops_the_alias() {
        // `$STDLIB.FILEref` names a type in the module a `staload` bound
        // to `$STDLIB`.  This compiler keeps one flat namespace, so the
        // qualifier is dropped and the name stands as the type it is —
        // exactly as the same qualifier is dropped in an expression.
        let p = Parser::parse("extern fun f (x: $STDLIB.FILEref): int\n").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else {
            panic!("expected an extern declaration")
        };
        assert_eq!(d.params[0].ty, Ty::Name("FILEref".into()));
    }

    #[test]
    fn a_constructor_qualified_by_a_staload_alias_drops_the_alias() {
        // `| $C.Red() => ...` — a constructor reached through the module
        // a `staload` bound to `$C`.  The qualifier is dropped and the
        // constructor stands alone, as it does in an expression and a
        // type.
        let a = arms("implement main0() = case c of | $C.Red() => 0 | $C.Green() => 1");
        assert_eq!(a.len(), 2);
        assert_eq!(a[0].0, Pattern::Ctor("Red".into(), vec![]));
        assert_eq!(a[1].0, Pattern::Ctor("Green".into(), vec![]));
    }

    #[test]
    fn implementing_a_value_binds_it() {
        // `implement x0 = e` fills in an `extern val`: no parameter list
        // sits between the name and the `=`, which is the whole of what
        // separates a value from a function here.  It binds the name the
        // way a top-level `val` would.
        let p = Parser::parse("implement x0 = 1 + 2\n").expect("parse");
        let Def::Val(v) = &p.defs()[0] else {
            panic!("a value implement is not a val")
        };
        assert_eq!(v.name, "x0");
    }

    #[test]
    fn an_existential_return_type_written_with_a_hash_is_read() {
        // `fun f (n: int): #[n1:nat | n1 >= n] int` — the hash is ATS's
        // "exists" marker on the return type.  It was not read, so a
        // signature that promised an existential witness stopped at the
        // return type.
        let p = Parser::parse("fun f (n: int): #[n1:nat | n1 >= n] int = n\n").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else {
            panic!("expected a fun")
        };
        assert_eq!(f.ret, Ty::Name("int".into()));
        assert!(
            !f.existentials.is_empty(),
            "an existential type was recorded"
        );
    }

    #[test]
    fn a_pragmatic_staload_names_its_unit_like_the_plain_form() {
        // `#staload H = "..."` and `#dynload "..."` are the pseudocode
        // spellings of `staload`/`dynload`.  The unit they name is a
        // dependency either way; recording only the unpragmatic form
        // would make a program silently one file again.
        let p = Parser::parse(concat!(
            "#staload H = \"./h.sats\"\n",
            "#staload \"./plain.sats\"\n",
            "#dynload \"./l.dats\"\n",
        ))
        .expect("parse");
        let paths: Vec<&str> = p.staloads().iter().map(|s| s.path.as_str()).collect();
        assert_eq!(paths, vec!["./h.sats", "./plain.sats", "./l.dats"]);
    }

    #[test]
    fn an_instantiated_template_may_be_applied_without_parentheses() {
        // `f<int> '{ x= 1 }` — ATS lets application drop its
        // parentheses, and naming the instance does not take that away.
        assert_eq!(
            body_of("fun f(): int = make<int> '{ x= 1 }"),
            Expr::Call(
                Box::new(Expr::Inst("make".into(), vec![Ty::Name("int".into())])),
                vec![Expr::RecordLit(vec![("x".into(), int(1))])],
            )
        );
    }

    #[test]
    fn a_typedef_may_take_parameters() {
        // `typedef ordmod (a:t@ype) = '{ ... }` names a *family* of
        // types.  Each use supplies the arguments, and the alias means
        // its body with those substituted in.
        let p =
            Parser::parse("typedef pair (a:t@ype) = '{ fst= a, snd= a }\nfun f(): pair(int) = g()")
                .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else {
            panic!("expected a fun")
        };
        assert_eq!(
            f.ret,
            Ty::Record(vec![
                ("fst".into(), Ty::Name("int".into())),
                ("snd".into(), Ty::Name("int".into())),
            ])
        );
    }

    #[test]
    fn skipping_a_directive_stops_at_the_next_val() {
        // Nothing punctuates the end of a `staload`, so the skip runs
        // until it recognises the start of the next form — and a
        // top-level `val` is one.  Missing it swallowed the declaration
        // whole, and the name it bound went undefined.
        let p = Parser::parse("staload \"x.sats\"\nval a: int = 1").expect("parse");
        assert!(
            p.defs()
                .iter()
                .any(|d| matches!(d, Def::Val(v) if v.name == "a")),
            "the `val` was swallowed: {:?}",
            p.defs()
        );
    }

    #[test]
    fn a_stream_takes_its_element_type_by_juxtaposition() {
        // `stream N2` and `stream(N2)` are the same type written two
        // ways.  Without the arity a juxtaposed name reads as a static
        // index and is dropped, which loses the element type.
        let p = Parser::parse("typedef N2 = int\nfun f(): stream N2 = g()").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else {
            panic!("expected a fun")
        };
        assert_eq!(
            f.ret,
            Ty::App("stream".into(), vec![Ty::Name("int".into())])
        );
    }

    #[test]
    fn delay_wraps_its_body_in_a_nullary_lambda() {
        assert_eq!(
            body_of("fun f(): int = $delay(1)"),
            Expr::Call(
                Box::new(var("$delay")),
                vec![Expr::Lam(vec![], None, Box::new(int(1)))],
            )
        );
    }

    #[test]
    fn ldelay_drops_the_cleanup_it_is_given() {
        // `$ldelay(e, ~xs)` names what to run if the stream is dropped
        // unforced.  The arena frees everything at once, so there is
        // nothing for it to do.
        assert_eq!(
            body_of("fun f(): int = $ldelay(1, free(x))"),
            Expr::Call(
                Box::new(var("$delay")),
                vec![Expr::Lam(vec![], None, Box::new(int(1)))],
            )
        );
    }

    #[test]
    fn a_define_renames_a_constructor_in_patterns_and_expressions() {
        let src = "#define cons stream_vt_cons\n\
                   fun f(xs: list0(int)): int = case xs of | cons(n, r) => n | _ => 0";
        let Expr::Case(_, arms) = body_of(src) else {
            panic!("expected a case")
        };
        assert_eq!(
            arms[0].0,
            Pattern::Ctor(
                "stream_vt_cons".into(),
                vec![Pattern::Var("n".into()), Pattern::Var("r".into())]
            )
        );
    }

    #[test]
    fn a_renamed_constructor_is_renamed_in_expressions_too() {
        let src = "#define cons stream_vt_cons\nfun f(x: int): int = cons(x, x)";
        assert_eq!(
            body_of(src),
            Expr::Call(Box::new(var("stream_vt_cons")), vec![var("x"), var("x")])
        );
    }

    #[test]
    fn a_vtypedef_names_a_type_the_same_way_a_typedef_does() {
        let p = Parser::parse(
            "vtypedef res = list0(int)
fun f(): res = list0_nil()",
        )
        .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else {
            panic!("expected a fun")
        };
        assert_eq!(f.ret, Ty::App("list0".into(), vec![Ty::Name("int".into())]));
    }

    #[test]
    fn an_implement_may_take_its_template_parameters_in_parentheses() {
        let p = Parser::parse("implement(a) f<a> (x) = x").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else {
            panic!("expected an implement")
        };
        assert_eq!(i.ty_params, vec!["a".to_string()]);
    }

    #[test]
    fn a_let_body_may_be_a_sequence() {
        assert_eq!(
            body_of("fun f(): int = let val x = 1 in g(); x end"),
            Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: Some("x".into()),
                    ty: None,
                    value: int(1),
                    mutable: false
                }],
                Box::new(Expr::Let(
                    vec![LetBind {
                        opened: Vec::new(),
                        proof: false,
                        name: None,
                        ty: None,
                        value: Expr::Call(Box::new(var("g")), vec![]),
                        mutable: false
                    }],
                    Box::new(var("x")),
                )),
            )
        );
    }

    #[test]
    fn fold_at_is_a_no_op() {
        assert_eq!(
            body_of("fun f(x: int): int = let val () = fold@ x in x end"),
            Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: None,
                    ty: None,
                    value: Expr::Unit,
                    mutable: false
                }],
                Box::new(var("x")),
            )
        );
    }

    #[test]
    fn a_semicolon_may_follow_a_pattern_binding() {
        let body =
            body_of("fun f(xs: list0(int)): int = let val-cons(n, r) = xs; val p = n in p end");
        assert!(
            matches!(body, Expr::Case(..)),
            "expected a case, got {body:?}"
        );
    }

    #[test]
    fn a_module_qualifier_is_dropped_from_a_call() {
        assert_eq!(
            body_of("fun f(): double = $STDLIB.drand48()"),
            Expr::Call(Box::new(var("drand48")), vec![])
        );
    }

    #[test]
    fn a_val_binding_may_open_with_an_at_pattern() {
        let Expr::Case(_, arms) =
            body_of("fun f(xs: list0(int)): int = let val-@cons(n, r) = xs in n end")
        else {
            panic!("expected a case")
        };
        assert_eq!(
            arms[0].0,
            Pattern::InPlace(Box::new(Pattern::Ctor(
                "cons".into(),
                vec![Pattern::Var("n".into()), Pattern::Var("r".into())]
            )))
        );
    }

    #[test]
    fn a_local_block_inside_a_body_contributes_its_public_bindings() {
        let Expr::Let(binds, body) =
            body_of("fun f(): int = let local val hidden = 1 in val shown = 2 end in shown end")
        else {
            panic!("expected a let")
        };
        assert_eq!(
            binds
                .iter()
                .filter_map(|b| b.name.as_deref())
                .collect::<Vec<_>>(),
            vec!["hidden", "shown"]
        );
        assert_eq!(*body, var("shown"));
    }

    #[test]
    fn an_implement_may_qualify_its_name_with_a_module() {
        let p = Parser::parse("implement $RG.randgen_val<int> () = 1").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else {
            panic!("expected an implement")
        };
        assert_eq!(i.name, "randgen_val");
    }

    #[test]
    fn begin_end_brackets_a_sequence() {
        assert_eq!(
            body_of("fun f(): int = begin g(); 1 end"),
            Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: None,
                    ty: None,
                    value: Expr::Call(Box::new(var("g")), vec![]),
                    mutable: false
                }],
                Box::new(int(1)),
            )
        );
    }

    #[test]
    fn begin_end_tolerates_a_trailing_semicolon() {
        assert_eq!(body_of("fun f(): int = begin 1 ; end"), int(1));
    }

    #[test]
    fn an_at_marks_a_pattern_as_matching_in_place() {
        let Expr::Case(_, arms) =
            body_of("fun f(xs: list0(int)): int = case xs of | @cons(n, r) => 1 | _ => 0")
        else {
            panic!("expected a case")
        };
        assert_eq!(
            arms[0].0,
            Pattern::InPlace(Box::new(Pattern::Ctor(
                "cons".into(),
                vec![Pattern::Var("n".into()), Pattern::Var("r".into())]
            )))
        );
    }

    #[test]
    fn a_proof_bar_drops_the_proofs_from_a_tuple_pattern() {
        let Expr::Let(binds, _) = body_of("fun f(): int = let val (pfat, pfgc | p) = g() in p end")
        else {
            panic!("expected a let")
        };
        assert_eq!(binds[0].name.as_deref(), Some("p"));
    }

    #[test]
    fn template_arguments_may_be_type_applications() {
        let Expr::Call(head, _) =
            body_of("fun f(out: int): int = fprint_tupval2<int,tup(bool,char)> (out, 1)")
        else {
            panic!("expected a call")
        };
        let Expr::Inst(name, args) = *head else {
            panic!("expected an instantiation, got {head:?}")
        };
        assert_eq!(name, "fprint_tupval2");
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn parses_cons_as_an_infix_pattern() {
        let Expr::Case(_, arms) =
            body_of("fun f(xs: list0(int)): int = case xs of | x :: rest => 1 | _ => 0")
        else {
            panic!("expected a case")
        };
        assert_eq!(
            arms[0].0,
            Pattern::Ctor(
                "cons".into(),
                vec![Pattern::Var("x".into()), Pattern::Var("rest".into())]
            )
        );
    }

    #[test]
    fn cons_patterns_nest_to_the_right() {
        let Expr::Case(_, arms) =
            body_of("fun f(xs: list0(int)): int = case xs of | x :: y :: rest => 1 | _ => 0")
        else {
            panic!("expected a case")
        };
        assert_eq!(
            arms[0].0,
            Pattern::Ctor(
                "cons".into(),
                vec![
                    Pattern::Var("x".into()),
                    Pattern::Ctor(
                        "cons".into(),
                        vec![Pattern::Var("y".into()), Pattern::Var("rest".into())]
                    ),
                ]
            )
        );
    }

    #[test]
    fn parses_cons_as_an_infix_expression() {
        assert_eq!(
            body_of("fun f(x: int, xs: list0(int)): list0(int) = x :: xs"),
            Expr::Call(Box::new(var("cons")), vec![var("x"), var("xs")],)
        );
    }

    #[test]
    fn a_define_renames_the_cons_operator() {
        let Expr::Case(_, arms) = body_of(
            "#define :: stream_vt_cons
fun f(xs: list0(int)): int = case xs of | x :: rest => 1 | _ => 0",
        ) else {
            panic!("expected a case")
        };
        assert_eq!(
            arms[0].0,
            Pattern::Ctor(
                "stream_vt_cons".into(),
                vec![Pattern::Var("x".into()), Pattern::Var("rest".into())]
            )
        );
    }

    #[test]
    fn parses_lambda_with_bare_parameter() {
        assert_eq!(
            body_of("fun f(): int = lam x => x + 1"),
            Expr::Lam(
                vec![Param {
                    borrowed: false,
                    name: "x".into(),
                    ty: Ty::Name("_".into())
                }],
                None,
                Box::new(Expr::BinOp(
                    BinOp::Add,
                    Box::new(var("x")),
                    Box::new(int(1))
                )),
            )
        );
    }

    #[test]
    fn parses_lambda_with_unannotated_parameters() {
        assert_eq!(
            body_of("fun f(): int = lam (x0, x1) => x0 + x1"),
            Expr::Lam(
                vec![
                    Param {
                        borrowed: false,
                        name: "x0".into(),
                        ty: Ty::Name("_".into())
                    },
                    Param {
                        borrowed: false,
                        name: "x1".into(),
                        ty: Ty::Name("_".into())
                    },
                ],
                None,
                Box::new(Expr::BinOp(
                    BinOp::Add,
                    Box::new(var("x0")),
                    Box::new(var("x1"))
                )),
            )
        );
    }

    #[test]
    fn parses_unary_negation_with_tilde_and_dash() {
        assert_eq!(
            body_of("fun f(x: int): int = ~x"),
            Expr::UnaryNeg(Box::new(var("x")))
        );
        assert_eq!(
            body_of("fun f(x: int): int = -x"),
            Expr::UnaryNeg(Box::new(var("x")))
        );
        // Unary binds tighter than multiplication.
        assert_eq!(
            body_of("fun f(x: int): int = ~x * 2"),
            Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::UnaryNeg(Box::new(var("x")))),
                Box::new(int(2))
            )
        );
    }

    #[test]
    fn parses_calls_and_chained_calls() {
        assert_eq!(
            body_of("fun f(): int = fact(n - 1)"),
            Expr::Call(
                Box::new(var("fact")),
                vec![Expr::BinOp(
                    BinOp::Sub,
                    Box::new(var("n")),
                    Box::new(int(1))
                )]
            )
        );
        assert_eq!(
            body_of("fun f(): int = g(1)(2)"),
            Expr::Call(
                Box::new(Expr::Call(Box::new(var("g")), vec![int(1)])),
                vec![int(2)]
            )
        );
    }

    #[test]
    fn parses_macro_calls_after_an_identifier() {
        assert_eq!(
            impl_body("implement main0() = println!(\"x = \", 1)"),
            Expr::MacroCall("println!".into(), vec![Expr::StrLit("x = ".into()), int(1)])
        );
    }

    #[test]
    fn parses_function_types() {
        // A higher-order parameter type: (int, int) -> int   and   int -> int
        let p =
            Parser::parse("fun apply(f: (int, int) -> int, x: int): int = f(x, x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(
            f.params[0].ty,
            Ty::Fun(
                vec![Ty::Name("int".into()), Ty::Name("int".into())],
                Box::new(Ty::Name("int".into()))
            )
        );

        let p = Parser::parse("fun id(f: int -> int): int = f(1)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(
            f.params[0].ty,
            Ty::Fun(
                vec![Ty::Name("int".into())],
                Box::new(Ty::Name("int".into()))
            )
        );
    }

    #[test]
    fn parses_type_applications() {
        // A name with no special meaning: `list` is the prelude's, and
        // would be canonicalised.
        let p = Parser::parse("fun len(xs: bag(a)): int = 0").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(
            f.params[0].ty,
            Ty::App("bag".into(), vec![Ty::Name("a".into())])
        );

        let p = Parser::parse("datatype tree = leaf | node(tree, tree)").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else {
            panic!()
        };
        assert_eq!(d.ctors[1].fields[0], Ty::Name("tree".into()));
    }

    #[test]
    fn type_application_insists_on_matching_parens() {
        let err = expect_err("fun len(xs: list(a): int = 0");
        assert!(err.message().contains(")"), "{}", err);
    }

    // --- strings ---------------------------------------------------

    #[test]
    fn decodes_extended_escapes_and_line_continuations() {
        let p = Parser::parse("fun f(): string = \"line1\\\nline2\"").expect("line continuation parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.body, Expr::StrLit("line1line2".into()));

        let p2 = Parser::parse("fun f(): string = \"\\a\\b\\f\\v\\(\"").expect("extended escapes");
        let Def::Fun(f2) = &p2.defs()[0] else { panic!() };
        assert_eq!(f2.body, Expr::StrLit("\x07\x08\x0c\x0b(".into()));
    }

    #[test]
    fn decodes_string_escapes_at_parse_time() {
        let p = Parser::parse("fun f(): string = \"a\\nb\"").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.body, Expr::StrLit("a\nb".into()));

        let p = Parser::parse("fun f(): string = \"q\\\"w\"").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.body, Expr::StrLit("q\"w".into()));
    }

    #[test]
    fn unknown_escape_sequences_are_errors() {
        let err = expect_err("fun f(): string = \"a\\qz\"");
        assert!(err.message().contains("escape"), "{}", err);
    }

    // --- errors ----------------------------------------------------

    #[test]
    fn missing_type_annotation_is_an_error() {
        let err = expect_err("fun f(x) = x");
        assert!(err.message().contains("type"), "{}", err);
    }

    #[test]
    fn termination_metrics_are_skipped() {
        // `.<x>.` proves the recursion terminates — a promise to the ATS
        // type checker with no bearing on what we emit.
        assert_eq!(
            body_of("fun f(x: int): int .<x>. = x"),
            Expr::Var("x".into())
        );
    }

    #[test]
    fn template_parameters_are_skipped() {
        // `{a:type}` constrains the static language, which this compiler
        // does not check; the function underneath it parses normally.
        assert_eq!(
            body_of("fun f{a:type}(x: int): int = x"),
            Expr::Var("x".into())
        );
    }

    #[test]
    fn dangling_constructor_call_is_an_error() {
        let err = expect_err("datatype t = a | ");
        assert!(err.message().contains("constructor"), "{}", err);
    }

    #[test]
    fn truncated_inputs_yield_errors_not_panics() {
        for src in [
            "fun f(",
            "fun f(): int =",
            "fun f(): int = 1 +",
            "implement main0(",
            "let x = 1 in 2",
        ] {
            let err = expect_err(src);
            assert_eq!(
                err.kind(),
                ats2_domain::errors::ErrorKind::Parse,
                "src: {src}"
            );
        }
    }

    #[test]
    fn empty_token_stream_is_rejected() {
        let err = expect_err_from_tokens(&[]);
        assert!(err.message().contains("empty"), "{}", err);
    }

    fn expect_err_from_tokens(tokens: &[Token]) -> CompileError {
        Parser::parse_tokens(tokens)
            .expect_err("should fail")
            .into_iter()
            .next()
            .expect("at least one error")
    }

    // --- integration: a realistic mini-program --------------------

    #[test]
    fn parses_a_realistic_program() {
        let src = "datatype list(a) = nil | cons(a, list(a))\n\nfun len(xs: list(a)): int = 0\n\nimplement main0() = { val xs = nil; println!(\"ok\") }\n";
        let p = Parser::parse(src).expect("parse");
        assert_eq!(p.defs().len(), 3);
        assert!(matches!(p.defs()[0], Def::Datatype(_)));
        assert!(matches!(p.defs()[1], Def::Fun(_)));
        assert!(matches!(p.defs()[2], Def::Implement(_)));
    }

    #[test]
    fn an_extval_is_a_type_a_c_name_and_its_arguments() {
        // `$extval(T, "c_fn", args...)` is how ATS reaches a C function:
        // the first argument is a *type* ATS sees, the second the C
        // spelling, the rest ordinary arguments.  Parsing it as a plain
        // call would turn the type into a variable and hand the emitter a
        // function nobody declared.
        let body = impl_body("implement main0 () = $extval(int, \"strlen\", \"hi\")");
        match body {
            Expr::ExtVal {
                ty,
                name,
                args,
                via_ptr,
            } => {
                assert_eq!(ty, Ty::Name("int".into()));
                assert_eq!(name, "strlen");
                assert_eq!(args, vec![Expr::StrLit("hi".into())]);
                assert!(!via_ptr);
            }
            other => panic!("expected an ExtVal, got {other:?}"),
        }
    }

    #[test]
    fn an_extval_without_arguments_is_a_value_not_a_call() {
        // `$extval(T, "C_CONST")` names a C constant or macro, not a
        // function: there is nothing to call, only a value to read.
        let body = impl_body("implement main0 () = $extval(int, \"EOF\")");
        match body {
            Expr::ExtVal {
                ty,
                name,
                args,
                via_ptr,
            } => {
                assert_eq!(ty, Ty::Name("int".into()));
                assert_eq!(name, "EOF");
                assert!(args.is_empty());
                assert!(!via_ptr);
            }
            other => panic!("expected an ExtVal, got {other:?}"),
        }
    }

    #[test]
    fn an_extfcall_is_a_call_through_a_function_pointer() {
        // `$extfcall(T, "f", args...)` is the same reach into C, but the
        // address is a function pointer rather than a named function.
        let body = impl_body("implement main0 () = $extfcall(int, \"atoi\", \"7\")");
        match body {
            Expr::ExtVal {
                ty,
                name,
                args,
                via_ptr,
            } => {
                assert_eq!(ty, Ty::Name("int".into()));
                assert_eq!(name, "atoi");
                assert_eq!(args, vec![Expr::StrLit("7".into())]);
                assert!(via_ptr);
            }
            other => panic!("expected an ExtVal, got {other:?}"),
        }
    }
    #[test]
    fn a_local_fnx_is_a_function_definition() {
        // `fnx` is ATS's named-recursion spelling of `fun`.  Inside a
        // `let` it declares a function like any other — a loop written
        // that way is how real ATS counts itself down — and it used to
        // make the parser look for the `in` that never came.
        let body = impl_body(
            "implement main0 () = let fnx loop (n: int): int = \
             if n = 0 then 0 else loop (n - 1) in loop (3) end",
        );
        match body {
            Expr::LetFun(funs, _) => {
                assert_eq!(funs.len(), 1);
                assert_eq!(funs[0].name, "loop");
            }
            other => panic!("expected a LetFun, got {other:?}"),
        }
    }

    #[test]
    fn a_bodyless_fun_inside_a_let_is_a_declaration_not_a_panic() {
        // `let fun g (x: int): int in ... end` declares a signature with
        // no body here; a `where` block's declarations are exactly this
        // shape.  A declaration has no place in a *recursive* group, so
        // it is set aside rather than forced in — and, before that, it
        // used to make the group's reader reach an unreachable panic.
        let body = impl_body("implement main0 () = let fun g (x: int): int in 1 end");
        assert!(matches!(body, Expr::IntLit(1)), "got {body:?}");
    }

    #[test]
    fn a_top_level_fnx_is_a_function_definition() {
        let program = Parser::parse("fnx loop (n: int): int = if n = 0 then 0 else loop (n - 1)")
            .expect("parse");
        let Def::Fun(f) = &program.defs()[0] else {
            panic!("expected a fun def");
        };
        assert_eq!(f.name, "loop");
    }

    #[test]
    fn a_pointer_field_read_is_a_deref_then_a_field() {
        // `p->f` is ATS's shorthand for `(!p).f`: the pointer is read, then
        // the field.  It failed before because `->` had no expression arm.
        let body = impl_body("implement main0 () = p->f");
        match body {
            Expr::Field(base, f) => {
                assert_eq!(f, "f");
                match *base {
                    Expr::Deref(inner) => assert_eq!(*inner, Expr::Var("p".into())),
                    other => panic!("expected a deref, got {other:?}"),
                }
            }
            other => panic!("expected a field read, got {other:?}"),
        }
    }

    #[test]
    fn a_pointer_field_store_writes_through_the_pointer() {
        // `p->f := e` stores through the pointer into the field, so the
        // place is the field reached by deref and `:=` is the store.
        let body = impl_body("implement main0 () = p->f := 7");
        match body {
            Expr::Store(place, value) => {
                assert_eq!(*value, Expr::IntLit(7));
                match *place {
                    Expr::Field(base, f) => {
                        assert_eq!(f, "f");
                        assert!(matches!(*base, Expr::Deref(_)));
                    }
                    other => panic!("expected a field place, got {other:?}"),
                }
            }
            other => panic!("expected a store, got {other:?}"),
        }
    }

    #[test]
    fn a_proof_implementation_parses_even_if_its_body_is_skipped() {
        // `primplmnt` fills in the body of an `extern prfun`.  This
        // compiler does not model proof implementations, but the line must
        // not stop the file: it used to read as "expected a definition".
        let p = Parser::parse("primplmnt f () = ()").expect("parse");
        assert!(p.defs().is_empty(), "a skipped directive produces no defs");
    }

    #[test]
    fn a_viewtypedef_is_skipped_not_refused() {
        // `viewtypedef` and its kind are declarations this compiler does
        // not model; they are skipped like every other directive, never
        // made into a parse error.
        let p = Parser::parse("viewtypedef v = view").expect("parse");
        assert!(p.defs().is_empty());
    }

    #[test]
    fn a_typedef_chained_with_and_is_not_a_function() {
        // `typedef key = string and itm = symbol` declares two aliases; the
        // `and` is the chain, not a function's mutual-recursion word.  It
        // was read as the latter, and the parser went looking for a
        // parameter list on `itm`.
        let p = Parser::parse("typedef key = string and itm = symbol").expect("parse");
        assert!(p.defs().is_empty(), "typedefs fold into a table, not defs");
    }

    #[test]
    fn a_constructor_with_a_juxtaposed_wildcard_is_a_pattern() {
        // `CAhelp _` is `CAhelp(_)` — a constructor applied to a wildcard,
        // written without the parentheses ATS allows omitting.  The `_` was
        // left unparsed, and the arm unreadable.
        let body = impl_body("implement main0 () = case+ x of | CAhelp _ => 0");
        match body {
            Expr::Case(_, arms) => {
                assert_eq!(arms.len(), 1);
                assert_eq!(
                    arms[0].0,
                    Pattern::Ctor("CAhelp".into(), vec![Pattern::Wildcard])
                );
            }
            other => panic!("expected a case, got {other:?}"),
        }
    }

    #[test]
    fn parses_pattern_guards_with_when() {
        let src = "fun classify(x: int): int =\n  case+ x of\n  | n when n > 0 => 1\n  | n when n < 0 => ~1\n  | _ => 0\n";
        let p = Parser::parse(src).expect("parse pattern guards");
        assert_eq!(p.defs().len(), 1);
    }

    #[test]
    fn toplevel_semicolons_and_chained_defines_are_tolerated() {
        let src = "#define S0 0\n#define B1 1; #define B2 2\ntypedef T = int;\nfun foo(): int = 42;\n";
        let p = Parser::parse(src).expect("parse succeeds despite semicolons");
        assert_eq!(p.defs().len(), 4);
    }

