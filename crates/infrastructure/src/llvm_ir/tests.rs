use crate::llvm_ir::LlvmIrEmitter;
use super::builder::*;
use super::emitter::*;
use super::expr::*;
use super::matching::*;
use super::types::*;
use ats2_domain::ast::*;
use ats2_domain::errors::CompileError;
use ats2_domain::tokens::*;
use crate::parser::Parser;

fn emit(source: &str) -> Result<String, CompileError> {
    let program = Parser::parse(source).expect("parse");
    LlvmIrEmitter::emit(&program)
}

fn emit_err(source: &str) -> CompileError {
    emit(source).expect_err("should fail")
}

#[test]
fn ambient_runtime_functions_can_be_implemented_and_called() {
    let ir = emit("implement atsruntime_handle_uncaughtexn(exn) = ()\nfun test_call(): void = patsolve_cnstrnt__dynload()").expect("emit");
    assert!(ir.contains("define void @atsruntime_handle_uncaughtexn(ptr %exn)"), "got:\n{ir}");
    assert!(ir.contains("declare void @patsolve_cnstrnt__dynload()"), "got:\n{ir}");
}

#[test]
fn auto_declares_foreign_c_and_erases_proof_calls() {
    let ir = emit("fun test(): void = let val () = lemma_matrixref_param() val () = patsolve_parsing__dynload() in () end").expect("emit");
    assert!(ir.contains("declare void @patsolve_parsing__dynload()"), "got:\n{ir}");
    assert!(!ir.contains("lemma_matrixref_param"), "got:\n{ir}");
}

#[test]
fn test_format_and_extracted_shims_pipeline() {
    let ir = emit("implement main0() = let val () = println!(\"hello %s\", \"world\") val arr = arrayptr_make_elt<int>(10, 0) in () end").expect("emit");
    assert!(ir.contains("@printf"), "got:\n{ir}");
    assert!(ir.contains(".ats_alloc"), "got:\n{ir}");
}

#[test]
fn standalone_implement_without_extern_fun_is_emitted() {
    let ir = emit("implement my_helper(x: int): int = x + 1").expect("emit");
    assert!(ir.contains("define i64 @my_helper(i64 %x)"), "got:\n{ir}");
}

    #[test]
    fn a_type_variable_and_an_unknown_lower_to_a_pointer() {
        // `a`, an unconstrained template parameter, and `_`, a type the
        // source declined to name, are both boxed by ATS: their value is
        // reached through a pointer, not met with the int/bool/string
        // wall.
        let registry = Registry::default();
        let for_a = llvm_type_in(&Ty::Name("a".into()), &registry).expect("a lowers");
        assert_eq!(for_a, LlvmType::I8Ptr, "a type variable is boxed");
        let for_under = llvm_type_in(&Ty::Name("_".into()), &registry).expect("_ lowers");
        assert_eq!(for_under, LlvmType::I8Ptr, "an unnamed type is boxed");
    }

    #[test]
    fn an_already_canonical_scalar_does_not_recurse() {
        let registry = Registry::default();
        let double = llvm_type_in(&Ty::Name("double".into()), &registry).expect("double lowers");
        assert_eq!(double, LlvmType::F64);
    }

    #[test]
    fn an_abstract_type_with_no_representation_is_a_boxed_pointer() {
        // `abstype point` hides a type without saying what it is.  Its
        // representation is opaque, so its values are boxed: a parameter
        // of `point` is a pointer, not a refusal.
        let ir = emit("abstype point\nfun f(x: point): int = 0").expect("abstract type emits");
        assert!(ir.contains("define i64 @f(ptr %x)"), "got:\n{ir}");
    }

    #[test]
    fn an_at_joined_abstract_type_with_no_representation_is_boxed() {
        // `abst@ype input_t0ype` — an abstract *linear* type with no
        // concrete form.  Like any opaque type its values are boxed: a
        // use of it is a pointer, not a refusal.
        let ir =
            emit("abst@ype input_t0ype\ntypedef input = input_t0ype\nfun f(x: input): int = 0")
                .expect("abstract linear type emits");
        assert!(ir.contains("define i64 @f(ptr %x)"), "got:\n{ir}");
    }

    fn module_starts_with_identifier_and_printf_declaration() {
        let ir = emit("").expect("emit");
        assert!(ir.starts_with("; ModuleID = 'ats2llvm'"), "got:\n{ir}");
        assert!(ir.contains("declare i32 @printf(ptr, ...)"), "got:\n{ir}");
    }

    #[test]
    fn emits_a_simple_function_exactly() {
        let ir = emit("fun f(x: int): int = x + 1").expect("emit");
        let expected = "define i64 @f(i64 %x) {\nentry:\n  %t.0 = add i64 %x, 1\n  ret i64 %t.0\n}";
        assert!(ir.contains(expected), "got:\n{ir}");
    }

    // --- functions and recursion ----------------------------------

    #[test]
    fn emits_recursive_calls_to_functions_defined_anywhere() {
        let ir =
            emit("fun fact(n: int): int = if n = 0 then 1 else n * fact(n - 1)").expect("emit");
        assert!(ir.contains("define i64 @fact(i64 %n)"), "got:\n{ir}");
        assert!(ir.contains("call i64 @fact(i64 %t."), "got:\n{ir}");
        assert!(ir.contains("icmp eq i64 %n, 0"), "got:\n{ir}");
        assert!(ir.contains("phi i64"), "got:\n{ir}");
    }

    #[test]
    fn emits_multiple_functions_in_source_order() {
        let ir = emit("fun a(): int = 1\nfun b(): int = 2").expect("emit");
        let ia = ir.find("define i64 @a").expect("a");
        let ib = ir.find("define i64 @b").expect("b");
        assert!(ia < ib, "got:\n{ir}");
    }

    // --- top-level `var` (statically allocated references) ---------

    #[test]
    fn a_top_level_var_is_a_dereferenceable_reference() {
        // `var x: int = 0` outside any body is storage whose address
        // outlives every call: `!x` must read it back.
        let ir = emit("var _count_: int = 0\nfun get(): int = !_count_\nimplement main0 () = ()")
            .expect("emit");
        assert!(ir.contains("define i64 @get()"), "got:\n{ir}");
    }

    #[test]
    fn a_top_level_var_reads_its_type_off_the_annotation() {
        // The initializer here (`if`) is not one of the shapes the
        // emitter can type on its own, so only the annotation can say
        // what the cell holds.
        let ir = emit(
            "var flag: int = if true then 1 else 0\nfun get(): int = !flag\nimplement main0 () = ()",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @get()"), "got:\n{ir}");
    }

    #[test]
    fn a_global_ref_gets_its_type_from_the_value_it_wraps() {
        // `val r = ref(0)` — the type is the one-slot tuple of the
        // wrapped value's type, read off the call itself.
        let ir =
            emit("val r = ref(0)\nfun get(): int = !r\nimplement main0 () = ()").expect("emit");
        assert!(ir.contains("define i64 @get()"), "got:\n{ir}");
    }

    #[test]
    fn ref_make_viewptr_takes_the_type_of_the_storage_it_wraps() {
        // `ref_make_viewptr (view@ x | addr@ x)` hands back the cell `x`
        // already is, so its type is `x`'s.
        let ir = emit(
            "var cell: int = 0\nval r = ref_make_viewptr (view@ cell | addr@ cell)\nfun get(): int = !r\nimplement main0 () = ()",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @get()"), "got:\n{ir}");
    }

    #[test]
    fn unknown_function_calls_are_errors() {
        let err = emit_err("fun f(x: int): int = g(x)");
        assert!(err.message().contains("unknown function"), "{}", err);
    }

    #[test]
    fn wrong_argument_count_is_an_error() {
        let err = emit_err("fun f(x: int): int = f()");
        assert!(err.message().contains("argument"), "{}", err);
    }

    // --- if / short-circuit ---------------------------------------

    #[test]
    fn emits_if_as_branches_and_a_phi() {
        let ir = emit("fun f(x: int): int = if x = 0 then 1 else 2").expect("emit");
        assert!(
            ir.contains("br i1 %t.0, label %if.t.0, label %if.e.0"),
            "got:\n{ir}"
        );
        assert!(ir.contains("if.t.0:"), "got:\n{ir}");
        assert!(ir.contains("if.e.0:"), "got:\n{ir}");
        assert!(ir.contains("if.m.0:"), "got:\n{ir}");
        assert!(
            ir.contains("phi i64 [ 1, %if.t.0 ], [ 2, %if.e.0 ]"),
            "got:\n{ir}"
        );
    }

    #[test]
    fn emits_short_circuit_andalso_and_orelse() {
        let ir = emit("fun f(a: bool, b: bool): bool = a andalso b").expect("emit");
        assert!(
            ir.contains("br i1 %a, label %and.t.0, label %and.f.0"),
            "got:\n{ir}"
        );
        assert!(
            ir.contains("phi i1 [ %b, %and.t.0 ], [ false, %and.f.0 ]"),
            "got:\n{ir}"
        );

        let ir = emit("fun f(a: bool, b: bool): bool = a orelse b").expect("emit");
        assert!(
            ir.contains("phi i1 [ true, %or.t.0 ], [ %b, %or.f.0 ]"),
            "got:\n{ir}"
        );
    }

    #[test]
    fn if_condition_must_be_a_bool() {
        let err = emit_err("fun f(x: int): int = if x then 1 else 2");
        assert!(err.message().contains("bool"), "{}", err);
    }

    #[test]
    fn if_branches_must_agree_on_a_type() {
        let err = emit_err("fun f(x: int): int = if true then 1 else true");
        assert!(err.message().contains("types"), "{}", err);
    }

    // --- let bindings ---------------------------------------------

    #[test]
    fn emits_let_bindings_in_order() {
        let ir = emit("fun f(x: int): int = let val y = x + 1 in y * 2 end").expect("emit");
        assert!(ir.contains("%t.0 = add i64 %x, 1"), "got:\n{ir}");
        assert!(ir.contains("%t.1 = mul i64 %t.0, 2"), "got:\n{ir}");
    }

    #[test]
    fn let_bind_type_annotations_are_checked() {
        let err = emit_err("fun f(x: int): int = let val y: bool = x in 0 end");
        assert!(err.message().contains("type"), "{}", err);
    }

    #[test]
    fn discard_bindings_evaluate_but_are_ignored() {
        let ir =
            emit("implement main0() = { val () = f(1); println!(\"ok\") }\nfun f(x: int): int = x")
                .expect("emit");
        assert!(ir.contains("call i64 @f(i64 1)"), "got:\n{ir}");
        assert!(ir.contains("ret i32 0"), "got:\n{ir}");
    }

    // --- literals and strings -------------------------------------

    #[test]
    fn emits_string_constants_and_returns_their_addresses() {
        let ir = emit("fun f(): string = \"hi\"").expect("emit");
        assert!(
            ir.contains("@.str.0 = private unnamed_addr constant [3 x i8] c\"hi\\00\""),
            "got:\n{ir}"
        );
        // With opaque pointers, the global's address is the value itself.
        assert!(ir.contains("ret ptr @.str.0"), "got:\n{ir}");
    }

    #[test]
    fn string_constants_are_deduplicated() {
        let ir = emit("fun f(): string = \"hi\"\nfun g(): string = \"hi\"").expect("emit");
        assert_eq!(ir.matches("@.str.0 = private").count(), 1, "got:\n{ir}");
        assert!(!ir.contains("@.str.1"), "got:\n{ir}");
    }

    #[test]
    fn emits_escaped_string_bytes() {
        let ir = emit("fun f(): string = \"a\\tb\"").expect("emit");
        assert!(ir.contains("a\\09b"), "got:\n{ir}");
    }

    #[test]
    fn emits_bool_and_int_literals() {
        let ir = emit("fun t(): bool = true\nfun f(): int = 42").expect("emit");
        assert!(ir.contains("ret i1 true"), "got:\n{ir}");
        assert!(ir.contains("ret i64 42"), "got:\n{ir}");
    }

    // --- main0 ----------------------------------------------------

    #[test]
    fn implements_main0_as_the_entry_point() {
        let ir = emit("implement main0() = println!(\"ok\")").expect("emit");
        assert!(ir.contains("define i32 @main()"), "got:\n{ir}");
        assert!(ir.contains("ret i32 0"), "got:\n{ir}");
    }

    #[test]
    fn main0_cannot_be_called_like_a_function() {
        let err = emit_err("fun f(): int = main0()");
        assert!(err.message().contains("main0"), "{}", err);
    }

    #[test]
    fn implementing_an_undeclared_name_is_rejected() {
        // Any name may be implemented now, but only if something declared
        // it: the declaration is where the parameter types come from.
        let err = emit_err("implement something() = println!(\"hi\")");
        assert!(err.message().contains("never declared"), "{}", err);
    }

    // --- println! -------------------------------------------------

    #[test]
    fn println_builds_a_printf_call_from_the_literal() {
        let ir = emit(
            "implement main0() = println!(\"fact(5) = \", fact(5))\nfun fact(n: int): int = 1",
        )
        .expect("emit");
        assert!(
            ir.contains(
                "@.fmt.0 = private unnamed_addr constant [15 x i8] c\"fact(5) = %ld\\0A\\00\""
            ),
            "got:\n{ir}"
        );
        assert!(ir.contains("call i32 (ptr, ...) @printf"), "got:\n{ir}");
        assert!(ir.contains("call i64 @fact(i64 5)"), "got:\n{ir}");
    }

    #[test]
    fn println_mixes_strings_and_values_in_the_format() {
        let ir =
            emit("implement main0() = let val s = \"z\" in println!(\"x=\", 1, \" y=\", s) end")
                .expect("emit");
        // The runtime format is  x=%ld y=%s<newline>
        assert!(ir.contains("x=%ld y=%s"), "got:\n{ir}");
    }

    #[test]
    fn literal_percent_is_doubled_in_printf_formats_but_not_in_strings() {
        let ir = emit("implement main0() = println!(\"100% done\")\nfun s(): string = \"100%\"")
            .expect("emit");
        // format: 100%% done + newline ; string: 100% unchanged
        assert!(ir.contains("100%% done"), "got:\n{ir}");
        assert!(ir.contains("c\"100%\\00\""), "got:\n{ir}");
    }

    #[test]
    fn unknown_macros_are_errors() {
        let err = emit_err("fun f(): int = magic!(1)");
        assert!(err.message().contains("macro"), "{}", err);
    }

    #[test]
    fn printing_a_bool_selects_between_two_words() {
        // ATS prints a bool as `true`/`false`.  A `select` picks the
        // constant, so printing costs no branch.
        let ir = emit("implement main0() = println!(true)").expect("emit");
        assert!(ir.contains("select i1 true, ptr @.str."), "got:\n{ir}");
        assert!(ir.contains(r#"c"true\00""#), "got:\n{ir}");
        assert!(ir.contains(r#"c"false\00""#), "got:\n{ir}");
    }

    // --- tuples and nested patterns ---------------------------------

    #[test]
    fn a_tuple_is_a_record_of_its_components() {
        let ir =
            emit("fun pair(): (int, int) = (1, 2) implement main0() = println!(1)").expect("emit");
        assert!(ir.contains("define ptr @pair()"), "got:\n{ir}");
        assert!(ir.contains("store i64 1, ptr"), "got:\n{ir}");
        assert!(ir.contains("store i64 2, ptr"), "got:\n{ir}");
    }

    #[test]
    fn a_flat_tuple_is_written_the_same_way() {
        let ir = emit("fun pair(): @(int, bool) = @(1, true) implement main0() = println!(1)")
            .expect("emit");
        assert!(ir.contains("define ptr @pair()"), "got:\n{ir}");
    }

    #[test]
    fn a_tuple_pattern_binds_each_component() {
        let ir = emit(
            "fun fst(p: (int, int)): int = case p of | (a, b) => a \
             implement main0() = println!(fst((3, 4)))",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @fst(ptr %p)"), "got:\n{ir}");
    }

    #[test]
    fn a_tuple_of_the_wrong_width_is_an_error() {
        let err = emit_err("fun f(p: (int, int)): int = case p of | (a, b, c) => a");
        assert!(
            err.message().contains("2") || err.message().contains("width"),
            "{err}"
        );
    }

    #[test]
    fn a_pattern_may_nest_inside_a_constructor() {
        let ir = emit(
            "datatype lst(a) = Nil of () | Cons of (a, lst(a)) \
             fun second(xs: lst(int)): int = case xs of | Cons(_, Cons(y, _)) => y | _ => 0 \
             implement main0() = println!(second(Cons(1, Cons(2, Nil()))))",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @second(ptr %xs)"), "got:\n{ir}");
    }

    #[test]
    fn a_nested_pattern_is_tested_only_after_the_outer_one_matches() {
        // Reading the tail's tag before knowing the value *is* a `Cons`
        // would follow whatever the other constructor left in that slot.
        // So the inner test must sit in its own block, reached only when
        // the outer test succeeded.
        let ir = emit(
            "datatype lst(a) = Nil of () | Cons of (a, lst(a)) \
             fun second(xs: lst(int)): int = case xs of | Cons(_, Cons(y, _)) => y | _ => 0 \
             implement main0() = println!(second(Nil()))",
        )
        .expect("emit");
        let tests = ir.matches("icmp eq i64").count();
        assert!(
            tests >= 2,
            "expected an outer and an inner tag test, got {tests}:\n{ir}"
        );
    }

    #[test]
    fn every_constructor_of_a_datatype_reserves_the_same_room() {
        // A `Nil` is allocated as wide as a `Cons`, so that reading a
        // field of one always lands inside the value rather than past it.
        let ir = emit(
            "datatype lst(a) = Nil of () | Cons of (a, lst(a)) \
             implement main0() = let val x: lst(int) = Nil() in println!(1) end",
        )
        .expect("emit");
        // tag + two fields = three words, even for the nullary case.
        assert!(
            ir.contains("call ptr @.ats_alloc(i64 24)"),
            "Nil must reserve the full width:\n{ir}"
        );
    }

    #[test]
    fn a_tuple_pattern_may_hold_constructors() {
        let ir = emit(
            "datatype lst(a) = Nil of () | Cons of (a, lst(a)) \
             fun both(p: (lst(int), lst(int))): int = \
               case p of | (Cons(x, _), Cons(y, _)) => x + y | _ => 0 \
             implement main0() = println!(both((Cons(1, Nil()), Cons(2, Nil()))))",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @both(ptr %p)"), "got:\n{ir}");
    }

    // --- floating point ---------------------------------------------

    #[test]
    fn a_double_is_an_llvm_double() {
        let ir = emit("fun f(x: double): double = x").expect("emit");
        assert!(ir.contains("define double @f(double %x)"), "got:\n{ir}");
    }

    #[test]
    fn a_float_literal_keeps_its_value() {
        let ir = emit("fun f(): double = 1.5 implement main0() = println!(1)").expect("emit");
        assert!(ir.contains("ret double 1.5"), "got:\n{ir}");
    }

    #[test]
    fn double_arithmetic_uses_the_floating_instructions() {
        let ir = emit("fun f(x: double, y: double): double = x * y + x").expect("emit");
        assert!(ir.contains("fmul double"), "got:\n{ir}");
        assert!(ir.contains("fadd double"), "got:\n{ir}");
    }

    #[test]
    fn doubles_compare_with_the_ordered_predicates() {
        let ir = emit("fun f(x: double, y: double): bool = x < y").expect("emit");
        assert!(ir.contains("fcmp olt double"), "got:\n{ir}");
    }

    #[test]
    fn printing_a_double_uses_the_float_placeholder() {
        let ir = emit("fun f(x: double): void = println!(x)").expect("emit");
        assert!(ir.contains("%f"), "got:\n{ir}");
    }

    #[test]
    fn an_int_converts_to_a_double_when_asked() {
        let ir = emit("fun f(n: int): double = int2double(n)").expect("emit");
        assert!(ir.contains("sitofp i64"), "got:\n{ir}");
    }

    #[test]
    fn mixing_an_int_and_a_double_widens_the_int() {
        // Changed deliberately: this used to be an error.
        //
        // ATS resolves `x * n` through the prelude's overloads, which
        // are keyed on *both* operand types (`gmul_double_int`).  This
        // compiler's overload table maps an operator to a single
        // function, so it cannot express that, and refusing the
        // expression outright was the wrong half of the trade: it made
        // `10 * env` unwritable in code where `env` is a double, which
        // is how the corpus writes it.  Widening loses the check that
        // the two operands agree; it gains the arithmetic ATS programs
        // actually contain.
        let ir = emit(
            "fun f(x: double, n: int): double = x * n implement main0() = println!(f(1.5, 2))",
        )
        .expect("emit");
        assert!(ir.contains("sitofp i64"), "the int must widen:\n{ir}");
        assert!(
            ir.contains("fmul double"),
            "the product must be a float one:\n{ir}"
        );
    }

    // --- macdef, overload, and the generic numeric shims -------------

    #[test]
    fn a_macdef_stands_for_the_expression_it_names() {
        let ir = emit(
            "fun twice (n: int): int = n + n \
             implement main0() = let macdef f = twice in println!(f(21)) end",
        )
        .expect("emit");
        assert!(ir.contains("call i64 @twice(i64 21)"), "got:\n{ir}");
    }

    #[test]
    fn a_macdef_may_name_a_template_instance() {
        let ir = emit(
            "extern fun{a:t@ype} id (x: a): a implement{a} id (x) = x \
             implement main0() = let macdef g = id<int> in println!(g(4)) end",
        )
        .expect("emit");
        assert!(ir.contains("call i64 @id$int(i64 4)"), "got:\n{ir}");
    }

    #[test]
    fn gnumber_int_builds_a_number_of_the_type_asked_for() {
        let ir = emit("fun one(): double = gnumber_int<double>(1)").expect("emit");
        assert!(ir.contains("ret double 1.0"), "got:\n{ir}");

        let ir = emit("fun one(): int = gnumber_int<int>(1)").expect("emit");
        assert!(ir.contains("ret i64 1"), "got:\n{ir}");
    }

    #[test]
    fn an_overload_supplies_an_operator_the_types_do_not_fit() {
        // `int * double` has no native instruction; the program's own
        // `overload` declaration says which function to use instead.
        let ir = emit(
            "overload * with gmul_int_val \
             fun scale (n: int, x: double): double = n * x",
        )
        .expect("emit");
        assert!(ir.contains("sitofp i64"), "the int must be promoted:\n{ir}");
        assert!(ir.contains("fmul double"), "got:\n{ir}");
    }

    #[test]
    fn an_overload_is_not_consulted_when_the_types_already_fit() {
        let ir =
            emit("overload * with gmul_int_val fun f (a: int, b: int): int = a * b").expect("emit");
        assert!(ir.contains("mul i64"), "got:\n{ir}");
        assert!(!ir.contains("sitofp"), "no promotion should happen:\n{ir}");
    }

    #[test]
    fn a_generic_comparison_shim_accepts_either_numeric_type() {
        let ir = emit(
            "overload > with ggt_val_int \
             fun big (x: double): bool = x > 0",
        )
        .expect("emit");
        assert!(ir.contains("fcmp ogt double"), "got:\n{ir}");
    }

    #[test]
    fn an_unfitting_operator_with_no_overload_is_still_an_error() {
        // Numbers widen (see `mixing_an_int_and_a_double_widens_the_int`);
        // things that are not numbers still do not.
        let err = emit_err("fun f (s: string, x: double): double = s * x");
        assert!(
            err.message().contains("ptr") || err.message().contains("operand"),
            "{err}"
        );
    }

    // --- the prelude's functions ------------------------------------

    #[test]
    fn list0_is_nil_comes_from_the_prelude() {
        let ir =
            emit("fun f(xs: list0(int)): bool = list0_is_nil(xs) implement main0() = println!(1)")
                .expect("emit");
        assert!(ir.contains("@list0_is_nil$int"), "got:\n{ir}");
    }

    #[test]
    fn a_prelude_function_is_left_out_when_nothing_calls_it() {
        let ir = emit("implement main0() = println!(1)").expect("emit");
        assert!(!ir.contains("list0_is_nil"), "got:\n{ir}");
        assert!(!ir.contains("string_isnot_empty"), "got:\n{ir}");
    }

    #[test]
    fn a_prelude_function_may_call_another() {
        // `string_isnot_empty` is written in terms of `string_length`,
        // so pulling the first in must pull the second.
        let ir = emit("fun f(s: string): bool = string_isnot_empty(s)").expect("emit");
        assert!(ir.contains("@strlen"), "got:\n{ir}");
    }

    #[test]
    fn the_program_may_define_a_prelude_name_itself() {
        let ir = emit(
            "fun string_isnot_empty(s: string): bool = false \
             implement main0() = println!(string_isnot_empty(\"x\"))",
        )
        .expect("emit");
        assert_eq!(
            ir.matches("define i1 @string_isnot_empty").count(),
            1,
            "got:\n{ir}"
        );
    }

    #[test]
    fn reading_a_line_yields_a_string_or_nothing() {
        let ir = emit(
            "implement main0() = let val s = fileref_get_line_string(stdin_ref) in \
             println!(string_is_null(s)) end",
        )
        .expect("emit");
        assert!(
            ir.contains("@fgetc"),
            "the line is read a character at a time:\n{ir}"
        );
        assert!(
            ir.contains("icmp eq ptr"),
            "the null result must be testable:\n{ir}"
        );
    }

    #[test]
    fn the_lines_of_a_file_come_back_as_a_list() {
        let ir = emit(
            "implement main0() = let val ls = fileref_get_lines_stringlst(stdin_ref) in \
             println!(list0_is_nil(ls)) end",
        )
        .expect("emit");
        assert!(ir.contains("@fileref_get_lines_stringlst"), "got:\n{ir}");
        assert!(ir.contains("; datatype list0$string"), "got:\n{ir}");
    }

    // --- top-level values -------------------------------------------

    #[test]
    fn a_top_level_val_becomes_a_global() {
        let ir = emit("val limit = 10 implement main0() = println!(limit)").expect("emit");
        assert!(ir.contains("@limit = internal global i64"), "got:\n{ir}");
        assert!(
            ir.contains("load i64, ptr @limit"),
            "reading it is a load:\n{ir}"
        );
    }

    #[test]
    fn a_top_level_val_is_initialised_before_main_runs() {
        let ir = emit("val limit = 6 * 7 implement main0() = println!(limit)").expect("emit");
        // The arithmetic happens in `main`, before anything else.
        let main = &ir[ir.find("define i32 @main").expect("a main")..];
        let store = main.find("store i64").expect("an initialising store");
        let print = main.find("@printf").expect("the printf");
        assert!(
            store < print,
            "the global must be set before it is read:\n{ir}"
        );
    }

    #[test]
    fn a_top_level_val_is_visible_inside_functions() {
        let ir = emit("val limit = 10 fun over(n: int): bool = n > limit implement main0() = println!(over(3))")
            .expect("emit");
        assert!(ir.contains("load i64, ptr @limit"), "got:\n{ir}");
    }

    #[test]
    fn top_level_vals_are_initialised_in_order() {
        let ir = emit("val a = 2 val b = a + 1 implement main0() = println!(b)").expect("emit");
        let main = &ir[ir.find("define i32 @main").expect("a main")..];
        assert!(
            main.find("@a").expect("a") < main.find("@b").expect("b"),
            "got:\n{ir}"
        );
    }

    #[test]
    fn a_top_level_val_may_hold_a_closure() {
        let ir =
            emit("val square = lam (x: int): int => x * x implement main0() = println!(square(5))")
                .expect("emit");
        assert!(ir.contains("@square = internal global ptr"), "got:\n{ir}");
        assert!(ir.contains("call i64 %"), "calling it is indirect:\n{ir}");
    }

    #[test]
    fn a_top_level_val_cannot_be_assigned_to() {
        let err = emit_err("val limit = 10 implement main0() = limit := 3");
        assert!(err.message().contains("limit"), "{err}");
    }

    // --- closures ----------------------------------------------------

    #[test]
    fn a_lambda_becomes_a_function_and_a_record() {
        let ir = emit(
            "fun mk(): (int) -> int = lam (n: int): int => n + 1 \
             implement main0() = println!(1)",
        )
        .expect("emit");
        // The body is lifted to a function of its own, taking the
        // environment as a first parameter.
        assert!(ir.contains("define i64 @lam."), "no lifted body in:\n{ir}");
        assert!(
            ir.contains("(ptr %env"),
            "the environment must be passed:\n{ir}"
        );
    }

    #[test]
    fn a_proposition_is_not_a_type_the_emitter_has_to_know() {
        // A `dataprop` declares constructors whose result is a
        // proposition — `FACT(n, r)` — which is not a type any machine
        // has.  The checker reads them; the emitter must not be handed
        // them at all.
        let ir = emit(
            "dataprop FACT (int, int) = | FACTbas (0, 1) of () \
             | {n:pos}{r:int} FACTind (n, n*r) of FACT (n-1, r) \
             implement main0() = println!(1)",
        )
        .expect("emit");
        assert!(
            !ir.contains("FACT"),
            "a proposition reached the emitter:\n{ir}"
        );
    }

    #[test]
    fn a_proof_binding_emits_nothing_at_all() {
        // `prval () = ax{n}()` establishes a claim and occupies no
        // storage.  `ax` is an axiom: it has no body anywhere, so a call
        // to it would not link.  Emission is where the static language
        // stops.
        let ir = emit(
            "praxi ax {n:nat} (): [n >= 0] void \
             fun f {n:nat} (x: int n): int = let prval () = ax{n}() in x end \
             implement main0() = println!(f(3))",
        )
        .expect("emit");
        assert!(!ir.contains("@ax"), "the axiom reached the emitter:\n{ir}");
    }

    #[test]
    fn a_capture_free_lambda_is_a_constant_and_allocates_nothing() {
        // A lambda that reads nothing from its scope has the same record
        // on every evaluation, so there is one, in read-only memory.
        // Allocating a fresh copy per evaluation would cost a bump and,
        // worse, hide the code pointer behind a mutable store — which is
        // what stops LLVM turning the indirect call into a direct one.
        let ir = emit(
            "fun mk(): (int) -> int = lam (n: int): int => n + 1 \
             implement main0() = println!(mk()(2))",
        )
        .expect("emit");
        assert!(
            ir.contains("constant ptr @lam.0"),
            "no constant record in:\n{ir}"
        );
        let mk = &ir[ir.find("define ptr @mk").expect("a mk")..];
        let mk = &mk[..mk.find("\n}").expect("an end")];
        assert!(
            !mk.contains(".ats_alloc"),
            "capture-free lambda still allocates:\n{mk}"
        );
    }

    #[test]
    fn a_closure_captures_what_it_reads() {
        let ir = emit(
            "fun adder(m: int): (int) -> int = lam (n: int): int => m + n \
             implement main0() = println!(1)",
        )
        .expect("emit");
        // `m` belongs to `adder`, so it is copied into the record and
        // read back out inside the lambda.
        assert!(
            ir.contains("store i64 %m, ptr"),
            "the capture must be stored:\n{ir}"
        );
        assert!(ir.contains("load i64, ptr"), "and loaded inside:\n{ir}");
    }

    #[test]
    fn calling_a_closure_goes_through_its_code_pointer() {
        let ir = emit(
            "fun adder(m: int): (int) -> int = lam (n: int): int => m + n \
             implement main0() = println!(adder(1)(2))",
        )
        .expect("emit");
        assert!(
            ir.contains("load ptr, ptr"),
            "the code pointer must be loaded:\n{ir}"
        );
        assert!(
            ir.contains("call i64 %"),
            "the call must be indirect:\n{ir}"
        );
    }

    #[test]
    fn a_function_may_infer_its_return_type_from_a_lambda_body() {
        // `fun acker (m: int) = lam (n: int): int => ...` writes no return
        // type; the lambda's own annotations say what it is.
        let ir = emit(
            "fun adder(m: int) = lam (n: int): int => m + n \
             implement main0() = println!(adder(1)(2))",
        )
        .expect("emit");
        assert!(ir.contains("define ptr @adder(i64 %m)"), "got:\n{ir}");
    }

    #[test]
    fn the_closure_arrow_annotation_is_accepted() {
        // `=<cloptr1>` says how the closure is allocated, which the arena
        // settles for us.
        let ir = emit(
            "fun adder(m: int) = lam (n: int): int =<cloptr1> m + n \
             implement main0() = println!(adder(1)(2))",
        )
        .expect("emit");
        assert!(ir.contains("define ptr @adder(i64 %m)"), "got:\n{ir}");
    }

    #[test]
    fn a_curried_call_still_flattens_when_the_arity_fits() {
        // Currying without closures must keep working: this `f` takes two
        // parameters, so `f(1)(2)` is one direct call.
        let ir = emit("fun f(a: int)(b: int): int = a + b implement main0() = println!(f(1)(2))")
            .expect("emit");
        assert!(ir.contains("call i64 @f(i64 1, i64 2)"), "got:\n{ir}");
    }

    #[test]
    fn a_closure_may_be_recursive_through_its_maker() {
        let ir = emit(
            "fun countdown(m: int) = lam (n: int): int =<cloptr1> \
               if m <= 0 then n else countdown(m - 1)(n + 1) \
             implement main0() = println!(countdown(3)(0))",
        )
        .expect("emit");
        assert!(ir.contains("call ptr @countdown"), "got:\n{ir}");
    }

    #[test]
    fn calling_a_non_function_is_still_an_error() {
        let err = emit_err("implement main0() = let val x: int = 1 in println!(x(1)) end");
        assert!(
            err.message().contains("call") || err.message().contains("function"),
            "{err}"
        );
    }

    // --- characters --------------------------------------------------

    #[test]
    fn a_char_is_a_byte() {
        let ir = emit("fun f(c: char): char = c").expect("emit");
        assert!(ir.contains("define i8 @f(i8 %c)"), "got:\n{ir}");
    }

    #[test]
    fn a_character_literal_is_its_byte_value() {
        let ir = emit("fun nl(): char = '\\n' implement main0() = println!(1)").expect("emit");
        assert!(ir.contains("ret i8 10"), "got:\n{ir}");
    }

    #[test]
    fn printing_a_char_uses_the_character_placeholder() {
        let ir = emit("implement main0() = println!('a')").expect("emit");
        assert!(ir.contains("%c"), "got:\n{ir}");
    }

    #[test]
    fn print_char_writes_one_character() {
        let ir = emit("implement main0() = print_char('x')").expect("emit");
        assert!(ir.contains("@putchar") || ir.contains("%c"), "got:\n{ir}");
    }

    #[test]
    fn print_int_and_print_string_are_the_obvious_shims() {
        let ir = emit("implement main0() = { val () = print_int(7) val () = print_string(\"s\") }")
            .expect("emit");
        assert!(ir.contains("i64 7"), "got:\n{ir}");
        assert!(ir.contains(r#"c"s\00""#), "got:\n{ir}");
    }

    #[test]
    fn a_char_compares_with_a_char() {
        let ir = emit("fun is_nl(c: char): bool = c = '\\n'").expect("emit");
        assert!(ir.contains("icmp eq i8"), "got:\n{ir}");
    }

    #[test]
    fn a_char_converts_to_and_from_an_int() {
        let ir = emit(
            "fun digit(c: char): int = char2int(c) - char2int('0') \
             implement main0() = println!(digit('7'))",
        )
        .expect("emit");
        assert!(ir.contains("sext i8"), "got:\n{ir}");
    }

    #[test]
    fn a_char_widens_to_an_int_in_arithmetic() {
        // Changed deliberately: this used to be an error.  ATS treats a
        // character as a small integer, and `c - '0'` is the idiom every
        // digit-parsing loop in the corpus is built on, so arithmetic
        // widens rather than refusing.
        let ir =
            emit("fun f(c: char): int = c + 1 implement main0() = println!(f('a'))").expect("emit");
        assert!(ir.contains("sext i8"), "expected the char to widen:\n{ir}");
    }

    #[test]
    fn a_char_is_still_not_an_int_outside_arithmetic() {
        // Widening is confined to arithmetic: the two types stay
        // distinct, so a `char` cannot stand in for an `int` where a
        // signature asks for one.
        let err = emit_err("fun g(n: int): int = n fun f(c: char): int = g(c)");
        assert!(
            err.message().contains("char") || err.message().contains("i8"),
            "{err}"
        );
    }

    // --- the prelude's list -----------------------------------------

    #[test]
    fn the_prelude_list_needs_no_declaration() {
        // `list0` comes from the prelude, which real programs reach
        // through `staload`; a program may use it without declaring it.
        let ir = emit(
            "fun ints(): list0(int) = list0_cons(1, list0_nil()) \
             implement main0() = println!(1)",
        )
        .expect("emit");
        assert!(ir.contains("; datatype list0$int"), "got:\n{ir}");
    }

    #[test]
    fn nil_and_cons_are_the_prelude_names_too() {
        let ir = emit("fun ints(): list0(int) = cons(1, nil()) implement main0() = println!(1)")
            .expect("emit");
        assert!(ir.contains("; datatype list0$int"), "got:\n{ir}");
    }

    #[test]
    fn the_capitalised_spelling_names_the_same_type() {
        // `List0(t)` and `list0(t)` are one type, so a value of one may be
        // passed where the other is expected.
        let ir = emit(
            "fun mk(): List0(int) = cons(1, nil()) \
             fun take(xs: list0(int)): int = case xs of | cons(x, _) => x | nil() => 0 \
             implement main0() = println!(take(mk()))",
        )
        .expect("emit");
        assert_eq!(ir.matches("; datatype list0$int").count(), 1, "got:\n{ir}");
    }

    #[test]
    fn the_indexed_list_erases_its_length() {
        // `list(t, n)` is the length-indexed list; the length is static,
        // so it names the same runtime type as `list0(t)`.
        let ir = emit(
            "fun mk(): list(int, n) = cons(1, nil()) \
             fun take(xs: list0(int)): int = case xs of | cons(x, _) => x | nil() => 0 \
             implement main0() = println!(take(mk()))",
        )
        .expect("emit");
        assert_eq!(ir.matches("; datatype list0$int").count(), 1, "got:\n{ir}");
    }

    #[test]
    fn a_program_may_still_declare_its_own_list0() {
        // The prelude must not shadow a declaration the program made.
        let ir = emit(
            "datatype list0(a) = list0_nil of () | list0_cons of (a, list0(a)) \
             fun ints(): list0(int) = list0_cons(1, list0_nil()) \
             implement main0() = println!(1)",
        )
        .expect("emit");
        assert_eq!(ir.matches("; datatype list0$int").count(), 1, "got:\n{ir}");
    }

    #[test]
    fn the_prelude_costs_nothing_when_unused() {
        let ir = emit("implement main0() = println!(1)").expect("emit");
        assert!(!ir.contains("list0"), "got:\n{ir}");
    }

    #[test]
    fn a_template_over_the_prelude_list_infers_its_instance() {
        // This is the shape `listfuns` uses: a template whose parameter is
        // `List0(a)`, called with no instantiation.
        let ir = emit(
            "fun mk(): List0(int) = cons(1, nil()) \
             extern fun{a:t@ype} len (xs: List0(INV(a))): int \
             implement{a} len (xs) = case xs of | cons(_, r) => 1 + len(r) | nil() => 0 \
             implement main0() = println!(len(mk()))",
        )
        .expect("emit");
        assert!(ir.contains("@len$int"), "got:\n{ir}");
    }

    // --- inferring which instance a template call means -------------

    const ID: &str = "extern fun{a:t@ype} id (x: a): a implement{a} id (x) = x ";

    #[test]
    fn a_template_call_infers_its_instance_from_the_argument() {
        // `id(5)` names no instance; the argument's type settles it.
        let ir = emit(&format!("{ID} implement main0() = println!(id(5))")).expect("emit");
        assert!(ir.contains("define i64 @id$int(i64 %x)"), "got:\n{ir}");
        assert!(ir.contains("call i64 @id$int(i64 5)"), "got:\n{ir}");
    }

    #[test]
    fn the_same_template_infers_different_instances() {
        let ir = emit(&format!(
            "{ID} implement main0() = println!(id(5), id(\"s\"), id(true))"
        ))
        .expect("emit");
        assert!(ir.contains("define i64 @id$int"), "got:\n{ir}");
        assert!(ir.contains("define ptr @id$string"), "got:\n{ir}");
        assert!(ir.contains("define i1 @id$bool"), "got:\n{ir}");
    }

    #[test]
    fn inference_sees_through_a_let_binding() {
        let ir = emit(&format!(
            "{ID} implement main0() = let val n = 7 in println!(id(n)) end"
        ))
        .expect("emit");
        assert!(ir.contains("call i64 @id$int"), "got:\n{ir}");
    }

    #[test]
    fn inference_sees_through_a_function_result() {
        let ir = emit(&format!(
            "{ID} fun get(): string = \"x\" implement main0() = println!(id(get()))"
        ))
        .expect("emit");
        assert!(ir.contains("call ptr @id$string"), "got:\n{ir}");
    }

    #[test]
    fn inference_reaches_inside_a_parameterized_datatype() {
        // The interesting case: the template's parameter is `lst(a)` and
        // the argument is a `lst(int)`, so `a` is found by matching the
        // two types against each other rather than by looking at one.
        let ir = emit(
            "datatype lst(a) = Nil of () | Cons of (a, lst(a)) \
             extern fun{a:t@ype} count (xs: lst(a)): int \
             implement{a} count (xs) = case xs of | Nil() => 0 | Cons(_, r) => 1 + count<a>(r) \
             fun ints(): lst(int) = Cons(1, Nil()) \
             implement main0() = println!(count(ints()))",
        )
        .expect("emit");
        assert!(ir.contains("@count$int"), "got:\n{ir}");
    }

    #[test]
    fn an_explicit_instantiation_still_wins() {
        let ir = emit(&format!("{ID} implement main0() = println!(id<int>(5))")).expect("emit");
        assert!(ir.contains("call i64 @id$int"), "got:\n{ir}");
    }

    #[test]
    fn a_template_whose_instance_cannot_be_inferred_says_so() {
        // Nothing here mentions `a` at all, so no argument can reveal it.
        let err = emit_err(
            "extern fun{a:t@ype} mystery (n: int): int implement{a} mystery (n) = n \
             implement main0() = println!(mystery(1))",
        );
        assert!(err.message().contains("mystery"), "{err}");
    }

    // --- parameterized datatypes ------------------------------------

    const OPT: &str = "datatype opt(a) = None of () | Some of a ";

    #[test]
    fn a_parameterized_datatype_is_instantiated_per_element_type() {
        let ir = emit(&format!(
            "{OPT} fun i(): opt(int) = Some(1) fun s(): opt(string) = Some(\"x\") \
             implement main0() = let val a = i() val b = s() in println!(1) end"
        ))
        .expect("emit");
        assert!(
            ir.contains("; datatype opt$int"),
            "no int instance in:\n{ir}"
        );
        assert!(
            ir.contains("; datatype opt$string"),
            "no string instance in:\n{ir}"
        );
    }

    #[test]
    fn a_bare_constructor_is_resolved_from_the_expected_type() {
        // `None()` says nothing about which `opt` it builds; the
        // function's declared return type does.
        let ir = emit(&format!(
            "{OPT} fun none_int(): opt(int) = None() implement main0() = println!(1)"
        ))
        .expect("emit");
        assert!(ir.contains("define ptr @none_int()"), "got:\n{ir}");
    }

    #[test]
    fn an_annotation_settles_a_constructor_too() {
        let ir = emit(&format!(
            "{OPT} implement main0() = let val x: opt(int) = None() in println!(1) end"
        ))
        .expect("emit");
        assert!(
            ir.contains("store i64 0, ptr"),
            "the tag must be stored:\n{ir}"
        );
    }

    #[test]
    fn a_constructor_argument_is_checked_against_the_instance() {
        let err = emit_err(&format!("{OPT} fun f(): opt(int) = Some(\"wrong\")"));
        assert!(err.message().contains("Some"), "{err}");
    }

    #[test]
    fn an_unresolvable_constructor_says_so() {
        // Two instances exist and nothing says which is meant.
        let err = emit_err(&format!(
            "{OPT} fun i(): opt(int) = None() fun s(): opt(string) = None() \
             implement main0() = let val x = None() in println!(1) end"
        ));
        assert!(err.message().contains("None"), "{err}");
    }

    #[test]
    fn a_case_over_an_instance_binds_the_element_type() {
        let ir = emit(&format!(
            "{OPT} fun unwrap(o: opt(int)): int = case o of | Some(v) => v | None() => 0 \
             implement main0() = println!(unwrap(Some(7)))"
        ))
        .expect("emit");
        assert!(ir.contains("define i64 @unwrap(ptr %o)"), "got:\n{ir}");
        assert!(
            ir.contains("load i64, ptr"),
            "the field must load as an int:\n{ir}"
        );
    }

    #[test]
    fn a_recursive_parameterized_datatype_instantiates_once() {
        let ir = emit(
            "datatype lst(a) = Nil of () | Cons of (a, lst(a)) \
             fun total(xs: lst(int)): int = case xs of | Nil() => 0 | Cons(x, r) => x + total(r) \
             implement main0() = println!(total(Cons(1, Cons(2, Nil()))))",
        )
        .expect("emit");
        assert_eq!(ir.matches("; datatype lst$int").count(), 1, "got:\n{ir}");
    }

    #[test]
    fn an_unused_parameterized_datatype_is_not_instantiated() {
        let ir = emit(&format!("{OPT} implement main0() = println!(1)")).expect("emit");
        assert!(!ir.contains("datatype opt$"), "got:\n{ir}");
    }

    // --- templates ---------------------------------------------------

    const IDENT: &str = "extern fun{a:t@ype} ident (x: a): a implement{a} ident (x) = x ";

    #[test]
    fn a_template_is_emitted_once_per_instantiation() {
        let ir = emit(&format!(
            "{IDENT} implement main0() = println!(ident<int>(1), ident<string>(\"s\"))"
        ))
        .expect("emit");
        assert!(
            ir.contains("define i64 @ident$int(i64 %x)"),
            "no int instance in:\n{ir}"
        );
        assert!(
            ir.contains("define ptr @ident$string(ptr %x)"),
            "no string instance in:\n{ir}"
        );
    }

    #[test]
    fn a_call_names_the_instance_it_wants() {
        let ir = emit(&format!(
            "{IDENT} implement main0() = println!(ident<int>(1))"
        ))
        .expect("emit");
        assert!(ir.contains("call i64 @ident$int(i64 1)"), "got:\n{ir}");
    }

    #[test]
    fn an_unused_template_is_not_emitted_at_all() {
        // A template is a *recipe*.  With no instantiation there is no
        // function, which is also why its body is never type-checked.
        let ir = emit(&format!("{IDENT} implement main0() = println!(1)")).expect("emit");
        assert!(!ir.contains("@ident"), "got:\n{ir}");
    }

    #[test]
    fn the_same_instantiation_twice_emits_one_function() {
        let ir = emit(&format!(
            "{IDENT} implement main0() = println!(ident<int>(1), ident<int>(2))"
        ))
        .expect("emit");
        assert_eq!(ir.matches("define i64 @ident$int").count(), 1, "got:\n{ir}");
    }

    #[test]
    fn a_template_may_call_another_at_the_same_instantiation() {
        let ir = emit(
            "extern fun{a:t@ype} twice (x: a): a \
             extern fun{a:t@ype} once (x: a): a \
             implement{a} once (x) = x \
             implement{a} twice (x) = once<a>(once<a>(x)) \
             implement main0() = println!(twice<int>(3))",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @twice$int"), "got:\n{ir}");
        assert!(ir.contains("define i64 @once$int"), "got:\n{ir}");
        assert!(ir.contains("call i64 @once$int"), "got:\n{ir}");
    }

    #[test]
    fn a_recursive_template_instantiates_once() {
        let ir = emit(
            "extern fun{a:t@ype} count (n: int, x: a): int \
             implement{a} count (n, x) = if n <= 0 then 0 else 1 + count<a>(n - 1, x) \
             implement main0() = println!(count<int>(3, 0))",
        )
        .expect("emit");
        assert_eq!(ir.matches("define i64 @count$int").count(), 1, "got:\n{ir}");
    }

    #[test]
    fn instantiating_an_undeclared_template_is_an_error() {
        let err = emit_err("implement main0() = println!(nosuch<int>(1))");
        assert!(err.message().contains("nosuch"), "{err}");
    }

    #[test]
    fn a_template_with_no_implementation_is_an_error() {
        let err =
            emit_err("extern fun{a:t@ype} f (x: a): a implement main0() = println!(f<int>(1))");
        assert!(err.message().contains("f"), "{err}");
    }

    #[test]
    fn calling_a_template_without_saying_which_instance_now_infers_it() {
        // The instantiation used to have to be written out.  Inference
        // reads it off the argument instead.
        let ir = emit(&format!("{IDENT} implement main0() = println!(ident(1))")).expect("emit");
        assert!(ir.contains("call i64 @ident$int(i64 1)"), "got:\n{ir}");
    }

    // --- declarations and their definitions -------------------------

    #[test]
    fn an_implement_takes_its_types_from_the_declaration() {
        let ir = emit("extern fun twice (x: int): int implement twice (x) = x + x").expect("emit");
        assert!(ir.contains("define i64 @twice(i64 %x)"), "got:\n{ir}");
    }

    #[test]
    fn a_declared_function_can_be_called_before_it_is_defined() {
        let ir = emit(
            "extern fun twice (x: int): int implement main0() = println!(twice(21)) implement twice (x) = x + x",
        )
        .expect("emit");
        assert!(ir.contains("call i64 @twice(i64 21)"), "got:\n{ir}");
    }

    #[test]
    fn an_implement_may_still_annotate_its_parameters() {
        let ir = emit("extern fun twice (x: int): int implement twice (x: int): int = x + x")
            .expect("emit");
        assert!(ir.contains("define i64 @twice(i64 %x)"), "got:\n{ir}");
    }

    #[test]
    fn implementing_something_never_declared_is_an_error() {
        let err = emit_err("implement nowhere (x) = x");
        assert!(err.message().contains("nowhere"), "{err}");
    }

    #[test]
    fn an_implement_must_agree_with_its_declaration_on_arity() {
        let err = emit_err("extern fun twice (x: int): int implement twice (x, y) = x");
        assert!(err.message().contains("twice"), "{err}");
    }

    #[test]
    fn a_declaration_with_no_definition_emits_nothing() {
        let ir = emit("extern fun twice (x: int): int").expect("emit");
        assert!(!ir.contains("define"), "got:\n{ir}");
    }

    // --- files ------------------------------------------------------

    #[test]
    fn the_standard_streams_are_loaded_from_libc_globals() {
        // `stdin`/`stdout`/`stderr` are C *variables* holding streams, so
        // reaching one costs a load.
        let ir = emit("implement main0() = let val f = stdin_ref in fileref_close(f) end")
            .expect("emit");
        assert!(ir.contains("@stdin = external global ptr"), "got:\n{ir}");
        assert!(ir.contains("load ptr, ptr @stdin"), "got:\n{ir}");
    }

    #[test]
    fn a_fileref_parameter_is_a_pointer() {
        let ir = emit("fun f(inp: FILEref): void = fileref_close(inp)").expect("emit");
        assert!(ir.contains("define void @f(ptr %inp)"), "got:\n{ir}");
    }

    #[test]
    fn getc_and_putc_become_fgetc_and_fputc() {
        let ir = emit(
            "fun copy(i: FILEref, o: FILEref): void = let val c = fileref_getc(i) in fileref_putc(o, c) end",
        )
        .expect("emit");
        assert!(ir.contains("call i32 @fgetc(ptr"), "got:\n{ir}");
        assert!(ir.contains("call i32 @fputc(i32"), "got:\n{ir}");
    }

    #[test]
    fn getc_widens_its_result_to_the_subsets_int() {
        // `fgetc` yields a C `int`; every `int` here is an `i64`, and the
        // widening must be *signed* so EOF stays -1.
        let ir = emit("fun f(i: FILEref): int = fileref_getc(i)").expect("emit");
        assert!(ir.contains("sext i32"), "EOF must stay negative:\n{ir}");
    }

    #[test]
    fn opening_a_file_checks_the_result() {
        let ir = emit(
            "implement main0(argc, argv) = let val f = fileref_open_exn(argv[1], file_mode_r) in fileref_close(f) end",
        )
        .expect("emit");
        assert!(ir.contains("call ptr @fopen(ptr"), "got:\n{ir}");
        assert!(
            ir.contains("icmp eq ptr"),
            "a failed open must be detected:\n{ir}"
        );
    }

    #[test]
    fn the_file_modes_are_the_c_strings() {
        let ir = emit(
            "implement main0(argc, argv) = let val f = fileref_open_exn(argv[1], file_mode_w) in fileref_close(f) end",
        )
        .expect("emit");
        assert!(ir.contains(r#"c"w\00""#), "got:\n{ir}");
    }

    #[test]
    fn fprint_writes_to_the_stream_it_is_given() {
        let ir = emit("fun f(out: FILEref): void = fprintln!(out, \"x = \", 1)").expect("emit");
        assert!(
            ir.contains("call i32 (ptr, ptr, ...) @fprintf(ptr %out"),
            "got:\n{ir}"
        );
    }

    #[test]
    fn printing_a_fileref_is_an_error() {
        let err = emit_err("fun f(out: FILEref): void = println!(out)");
        assert!(
            err.message().contains("FILEref") || err.message().contains("file"),
            "{err}"
        );
    }

    #[test]
    fn fileref_load_scans_into_the_cell_it_is_given() {
        // `fileref_load<int>(f, N)` reads a value *into* `N`, so it needs
        // the cell's address rather than the value inside it.
        let ir = emit(
            "implement main0() = let var n: int val ok = fileref_load<int>(stdin_ref, n) in println!(n) end",
        )
        .expect("emit");
        assert!(
            ir.contains("call i32 (ptr, ptr, ...) @fscanf(ptr"),
            "got:\n{ir}"
        );
        assert!(
            ir.contains("ptr %n.cell"),
            "the cell's address must be passed:\n{ir}"
        );
    }

    #[test]
    fn fileref_load_reports_whether_it_succeeded() {
        // It yields a bool: `fscanf` returns how many items it converted.
        let ir = emit(
            "implement main0() = let var n: int val ok = fileref_load<int>(stdin_ref, n) in println!(ok) end",
        )
        .expect("emit");
        assert!(
            ir.contains("icmp eq i32"),
            "the count must be compared:\n{ir}"
        );
    }

    #[test]
    fn fileref_load_needs_a_var_not_a_val() {
        let err = emit_err(
            "implement main0() = let val n: int = 0 val ok = fileref_load<int>(stdin_ref, n) in println!(n) end",
        );
        assert!(err.message().contains("var"), "{err}");
    }

    // --- datatypes and pattern matching -----------------------------

    const COLOR: &str = "datatype color = Red | Green | Blue ";
    const LIST: &str = "datatype intlist = Nil | Cons(int, intlist) ";

    #[test]
    fn a_nullary_constructor_is_a_tagged_allocation() {
        let ir = emit(&format!(
            "{COLOR} implement main0() = let val c = Red() in println!(1) end"
        ))
        .expect("emit");
        // Each constructor of a datatype gets a distinct tag, stored in
        // the first word of the value.
        assert!(ir.contains("store i64 0, ptr"), "no tag stored in:\n{ir}");
    }

    #[test]
    fn constructors_are_numbered_in_declaration_order() {
        let ir = emit(&format!(
            "{COLOR} implement main0() = let val c = Blue() in println!(1) end"
        ))
        .expect("emit");
        assert!(
            ir.contains("store i64 2, ptr"),
            "Blue should carry tag 2:\n{ir}"
        );
    }

    #[test]
    fn a_constructor_with_fields_stores_them_after_the_tag() {
        let ir = emit(&format!(
            "{LIST} implement main0() = let val xs = Cons(7, Nil()) in println!(1) end"
        ))
        .expect("emit");
        assert!(
            ir.contains("store i64 7, ptr"),
            "the field must be stored:\n{ir}"
        );
    }

    #[test]
    fn a_case_switches_on_the_tag() {
        let ir = emit(&format!(
            "{COLOR} fun name(c: color): int = case c of | Red() => 0 | Green() => 1 | Blue() => 2 \
             implement main0() = println!(name(Green()))"
        ))
        .expect("emit");
        assert!(ir.contains("load i64, ptr"), "the tag must be read:\n{ir}");
        assert!(ir.contains("icmp eq i64"), "the tag must be tested:\n{ir}");
    }

    #[test]
    fn a_pattern_binds_the_fields_it_names() {
        let ir = emit(&format!(
            "{LIST} fun head(xs: intlist): int = case xs of | Cons(x, r) => x | Nil() => 0 \
             implement main0() = println!(head(Cons(9, Nil())))"
        ))
        .expect("emit");
        assert!(
            ir.contains("getelementptr"),
            "fields are reached by address:\n{ir}"
        );
    }

    #[test]
    fn a_variable_pattern_matches_anything() {
        let ir = emit(&format!(
            "{COLOR} fun f(c: color): int = case c of | Red() => 0 | other => 1 \
             implement main0() = println!(f(Blue()))"
        ))
        .expect("emit");
        assert!(ir.contains("define i64 @f(ptr %c)"), "got:\n{ir}");
    }

    #[test]
    fn an_unknown_constructor_is_an_error() {
        let err = emit_err(&format!(
            "{COLOR} fun f(c: color): int = case c of | Purple() => 0"
        ));
        assert!(err.message().contains("Purple"), "{err}");
    }

    #[test]
    fn a_constructor_from_another_datatype_is_an_error() {
        let err = emit_err(&format!(
            "{COLOR} {LIST} fun f(c: color): int = case c of | Nil() => 0 | _ => 1"
        ));
        assert!(
            err.message().contains("intlist") || err.message().contains("color"),
            "{err}"
        );
    }

    #[test]
    fn a_constructor_checks_its_argument_count() {
        let err = emit_err(&format!(
            "{LIST} implement main0() = let val xs = Cons(1) in println!(1) end"
        ));
        assert!(err.message().contains("Cons"), "{err}");
    }

    #[test]
    fn case_arms_must_agree_on_a_type() {
        let err = emit_err(&format!(
            "{COLOR} fun f(c: color): int = case c of | Red() => 0 | _ => true"
        ));
        assert!(err.message().contains("type"), "{err}");
    }

    #[test]
    fn allocation_starts_in_a_static_arena() {
        // The common case allocates a few hundred bytes and should not
        // touch the allocator at all: a bump pointer into a static
        // buffer is both faster and impossible to leak.
        let ir = emit(&format!(
            "{COLOR} implement main0() = let val c = Red() in println!(1) end"
        ))
        .expect("emit");
        assert!(
            ir.contains("@.heap = internal global"),
            "expected a static arena:\n{ir}"
        );
    }

    #[test]
    fn an_exhausted_arena_grows_and_gives_the_growth_back() {
        // No fixed size is the right one for every program: a lazy
        // stream allocates for as long as it is walked, and the sieve
        // walks a long way.  So the arena grows rather than giving up —
        // and hands every chunk back before `main` returns, which is
        // what keeps "nothing leaks" true rather than merely intended.
        let ir = emit(&format!(
            "{COLOR} implement main0() = let val c = Red() in println!(1) end"
        ))
        .expect("emit");
        assert!(
            ir.contains("call ptr @malloc"),
            "the arena cannot grow:\n{ir}"
        );
        assert!(
            ir.contains("call void @free"),
            "the growth is never returned:\n{ir}"
        );
    }

    // --- `exit`, and the type of an expression that never returns ---

    #[test]
    fn exit_terminates_the_block() {
        let ir = emit("implement main0() = exit(1)").expect("emit");
        // The status narrows from the subset's i64 to the i32 C wants.
        assert!(ir.contains("trunc i64 1 to i32"), "got:\n{ir}");
        assert!(ir.contains("call void @exit(i32 %"), "got:\n{ir}");
        assert!(
            ir.contains("unreachable"),
            "control must not fall through:\n{ir}"
        );
    }

    #[test]
    fn a_branch_that_exits_takes_the_type_of_the_other_one() {
        // `exit` never returns, so it is compatible with any branch it
        // shares an `if` with — the classic bottom type.
        let ir = emit("fun f(n: int): int = if n > 0 then n else exit(1)").expect("emit");
        assert!(ir.contains("define i64 @f(i64 %n)"), "got:\n{ir}");
    }

    #[test]
    fn the_phi_skips_a_branch_that_never_arrives() {
        // A branch ending in `unreachable` is not a predecessor of the
        // merge block, so naming it in the phi would be invalid IR.
        let ir = emit("fun f(n: int): int = if n > 0 then n else exit(1)").expect("emit");
        let phi = ir.lines().find(|l| l.contains("phi")).unwrap_or("");
        assert_eq!(
            phi.matches('[').count(),
            1,
            "expected one incoming edge, got: {phi}"
        );
    }

    #[test]
    fn a_function_may_end_in_exit_whatever_it_returns() {
        let ir = emit("fun f(): string = exit(2)").expect("emit");
        assert!(ir.contains("define ptr @f()"), "got:\n{ir}");
    }

    #[test]
    fn exit_wants_an_int() {
        let err = emit_err("implement main0() = exit(\"nope\")");
        assert!(err.message().contains("int"), "{err}");
    }

    // --- the two entry points ---------------------------------------

    #[test]
    fn main0_ignores_its_body_and_exits_zero() {
        // `main0` is the "no exit code" entry: whatever it evaluates to
        // is discarded and the process reports success.
        let ir = emit("implement main0() = println!(1)").expect("emit");
        assert!(ir.contains("ret i32 0"), "got:\n{ir}");
    }

    #[test]
    fn main_returns_its_value_as_the_exit_code() {
        // `main` is the "with exit code" entry: its `int` result is the
        // status the process exits with, narrowed to C's `int`.
        let ir = emit("implement main(argc, argv): int = 0").expect("emit");
        assert!(
            ir.contains("define i32 @main(i32 %argc.raw, ptr %argv)"),
            "got:\n{ir}"
        );
        assert!(
            ir.contains("trunc i64 0 to i32"),
            "the code must narrow to C's int:\n{ir}"
        );
        assert!(
            !ir.contains("ret i32 0\n}"),
            "the exit code must not be hardcoded:\n{ir}"
        );
    }

    #[test]
    fn main_must_produce_an_int() {
        let err = emit_err("implement main(argc, argv): int = println!(1)");
        assert!(err.message().contains("exit code"), "{err}");
    }

    #[test]
    fn implementing_without_a_declaration_says_what_is_missing() {
        let err = emit_err("implement something_else() = 1");
        assert!(err.message().contains("extern fun"), "{err}");
    }

    // --- indexed types erase to the type underneath -----------------

    #[test]
    fn an_indexed_int_is_an_int() {
        // `int(n)` is "the int whose value is n".  The index is a fact for
        // the type checker; at runtime it is an ordinary machine integer,
        // so the type erases to its base.
        let ir = emit("fun f(n: int(n)): int(n) = n").expect("emit");
        assert!(ir.contains("define i64 @f(i64 %n)"), "got:\n{ir}");
    }

    #[test]
    fn a_bounded_int_is_an_int() {
        let ir = emit("fun f(n: intGte(0)): intGte(0) = n").expect("emit");
        assert!(ir.contains("define i64 @f(i64 %n)"), "got:\n{ir}");
    }

    #[test]
    fn an_indexed_string_is_a_string() {
        let ir = emit("fun f(s: string(n)): string(n) = s").expect("emit");
        assert!(ir.contains("define ptr @f(ptr %s)"), "got:\n{ir}");
    }

    #[test]
    fn an_opaque_applied_type_is_a_boxed_pointer() {
        // A datatype nobody declared is an opaque applied type, like the
        // type families ATS's own signatures lean on (`fprint_type(t)`,
        // `cfun(...)`, `List_vt(a)`): whatever its shape, nothing here
        // may take it apart, so a pointer is what it is.  The checker is
        // the wall for a head that is truly nothing.
        let ir = emit("fun f(xs: bag(int, n)): int = 0").expect("opaque applied type");
        assert!(ir.contains("define i64 @f(ptr %xs)"), "got:\n{ir}");
    }

    // --- the prelude shims -----------------------------------------

    #[test]
    fn g0string2int_becomes_a_call_to_atoi() {
        let ir =
            emit("implement main0(argc, argv) = println!(g0string2int(argv[1]))").expect("emit");
        assert!(ir.contains("call i64 @atoi(ptr"), "got:\n{ir}");
        assert!(
            ir.contains("declare i64 @atoi(ptr)"),
            "atoi must be declared:\n{ir}"
        );
    }

    #[test]
    fn the_int_suffixed_spelling_is_the_same_shim() {
        let ir = emit("implement main0(argc, argv) = println!(g0string2int_int(argv[1]))")
            .expect("emit");
        assert!(ir.contains("call i64 @atoi(ptr"), "got:\n{ir}");
    }

    #[test]
    fn appending_two_strings_makes_a_third() {
        // ATS strings are NUL-terminated bytes somebody else owns, so
        // joining two means asking the arena for room and copying both
        // in.  There is nowhere else for the result to live.
        let ir = emit(r#"implement main0() = println!(string_append("ab", "cd"))"#).expect("emit");
        assert!(ir.contains("@memcpy"), "nothing was copied:\n{ir}");
        assert!(
            ir.contains("@.ats_alloc"),
            "the result has nowhere to live:\n{ir}"
        );
    }

    #[test]
    fn a_substring_is_copied_out_and_terminated() {
        let ir = emit(r#"implement main0() = println!(string_make_substring("hello", 1, 3))"#)
            .expect("emit");
        assert!(ir.contains("@memcpy"), "nothing was copied:\n{ir}");
        // The copy is not NUL-terminated by itself: a substring ends
        // where it is told to, not where the original did.
        assert!(ir.contains("store i8 0"), "the result never ends:\n{ir}");
    }

    #[test]
    fn string_length_becomes_a_call_to_strlen() {
        let ir = emit("implement main0() = println!(string_length(\"abc\"))").expect("emit");
        assert!(ir.contains("call i64 @strlen(ptr"), "got:\n{ir}");
    }

    #[test]
    fn the_representation_changing_shims_are_the_identity() {
        // `g1ofg0` moves a value between ATS's two integer *sorts*.  The
        // sorts differ only in what the type checker knows about them, so
        // at the level of machine values the conversion is a no-op.
        let ir = emit("implement main0() = let val n = g1ofg0(41) in println!(n + 1) end")
            .expect("emit");
        assert!(
            !ir.contains("call i64 @g1ofg0"),
            "the shim must vanish, not be called:\n{ir}"
        );
        assert!(ir.contains("add i64 41, 1"), "got:\n{ir}");
    }

    #[test]
    fn a_shim_checks_the_type_of_its_argument() {
        let err = emit_err("implement main0() = println!(g0string2int(1))");
        // Not merely "unknown function": the shim exists and refuses the
        // argument it was handed.
        assert!(err.message().contains("expects a ptr argument"), "{err}");
    }

    // --- the command line ------------------------------------------

    #[test]
    fn main_with_arguments_takes_the_c_entry_signature() {
        let ir = emit("implement main0(argc, argv) = println!(argc)").expect("emit");
        assert!(
            ir.contains("define i32 @main(i32 %argc.raw, ptr %argv)"),
            "got:\n{ir}"
        );
    }

    #[test]
    fn argc_widens_to_the_subsets_integer_width() {
        // C hands over an `i32`; every `int` here is an `i64`.
        let ir = emit("implement main0(argc, argv) = println!(argc)").expect("emit");
        assert!(
            ir.contains("%argc = sext i32 %argc.raw to i64"),
            "got:\n{ir}"
        );
    }

    #[test]
    fn main_without_arguments_still_takes_none() {
        let ir = emit("implement main0() = println!(1)").expect("emit");
        assert!(ir.contains("define i32 @main()"), "got:\n{ir}");
    }

    #[test]
    fn indexing_argv_loads_a_string() {
        let ir = emit("implement main0(argc, argv) = println!(argv[1])").expect("emit");
        assert!(
            ir.contains("getelementptr ptr, ptr %argv"),
            "no address computation in:\n{ir}"
        );
        assert!(ir.contains("load ptr, ptr"), "no load in:\n{ir}");
    }

    #[test]
    fn indexing_something_that_is_not_indexable_is_an_error() {
        let err = emit_err("implement main0() = let val x: int = 1 in println!(x[0]) end");
        assert!(err.message().contains("index"), "{err}");
    }

    // --- mutable state: cells, assignment, and the loop forms ------

    #[test]
    fn a_var_binding_allocates_a_cell_and_stores_into_it() {
        // A `val` is an SSA value and needs no storage; a `var` is a cell,
        // so it costs exactly one alloca and one store.
        let ir = emit("implement main0() = let var x: int = 7 in println!(x) end").expect("emit");
        assert!(ir.contains("= alloca i64"), "no alloca in:\n{ir}");
        assert!(
            ir.contains("store i64 7, ptr %x.cell"),
            "no initializing store in:\n{ir}"
        );
    }

    #[test]
    fn reading_a_var_is_a_load() {
        let ir = emit("implement main0() = let var x: int = 7 in println!(x) end").expect("emit");
        assert!(ir.contains("load i64, ptr %x.cell"), "no load in:\n{ir}");
    }

    #[test]
    fn a_val_binding_still_allocates_nothing() {
        let ir = emit("implement main0() = let val x: int = 7 in println!(x) end").expect("emit");
        assert!(!ir.contains("alloca"), "a `val` must not allocate:\n{ir}");
    }

    #[test]
    fn an_implement_with_template_parameters_is_a_template_even_undeclared() {
        // No `extern fun{x}` declares it, so nothing but the `{x}` says
        // this is a template — and that has to be enough, or `x` reaches
        // the emitter as if it were a real type.
        let ir = emit(
            "implement{x}\nmyforeach (xs: list0(x)): int = 0\nimplement main0() = println!(1)",
        )
        .expect("emit");
        assert!(
            !ir.contains("@myforeach"),
            "an uninstantiated template was emitted:\n{ir}"
        );
    }

    #[test]
    fn raising_names_the_exception_and_leaves() {
        // There is no handler to reach, so the honest lowering of a
        // raise is to say what happened and stop.
        let ir = emit("implement main0() = $raise StreamSubscriptExn").expect("emit");
        assert!(ir.contains("StreamSubscriptExn"), "the name is lost:\n{ir}");
        assert!(
            ir.contains("call void @exit"),
            "the program carries on:\n{ir}"
        );
    }

    #[test]
    fn a_raise_can_stand_where_a_value_is_wanted() {
        // A branch that never returns agrees with any type the other
        // branch has, which is what lets a lookup say "or fail".
        let ir = emit(
            "fun get (n: int): int = if n = 0 then 1 else $raise SubscriptExn\n\
             implement main0() = println!(get(0))",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @get(i64 %n)"), "got:\n{ir}");
    }

    #[test]
    fn an_unannotated_lambda_parameter_takes_its_type_from_the_context() {
        // `lam x => x > 0` says nothing about `x`.  The parameter it is
        // being passed as does, and that is the only thing that can.
        let ir = emit(
            "extern fun apply (f: (int) -<cloref1> bool): bool\n\
             implement apply (f) = f(1)\n\
             implement main0() = println!(apply(lam x => x > 0))",
        )
        .expect("emit");
        assert!(ir.contains("i64 %x"), "the parameter is not an int:\n{ir}");
    }

    #[test]
    fn a_tilde_on_a_linear_value_frees_it_rather_than_negating_it() {
        // ATS spells "negate" and "consume this linear value" with the
        // same character, and only the operand's type tells them apart.
        // With an arena there is nothing to free, so the consuming one
        // is a statement that does nothing.
        let ir = emit(
            "implement main0() = let val xs: list0(int) = list0_cons(1, list0_nil()) in (~xs; ()) end",
        )
        .expect("emit");
        assert!(!ir.contains("sub i64 0, "), "a list was negated:\n{ir}");
    }

    #[test]
    fn implementing_a_prelude_template_does_not_hide_its_declaration() {
        // The prelude fills gaps and never shadows — but an `implement`
        // is not a declaration, it is a *body* for one.  Counting it as
        // a declaration took the prelude's away and left the body with
        // nothing to be the body of.
        let ir = emit(
            "implement fprint_val<int> (out, x) = fprint!(out, x)\n\
             implement main0() = fprint_val<int> (stdout_ref, 1)",
        )
        .expect("emit");
        assert!(ir.contains("%ld"), "the instance never printed:\n{ir}");
    }

    #[test]
    fn an_implement_may_supply_one_instance_of_a_template() {
        // `implement show<int> (x) = ...` fills in *that* instance and
        // says nothing about the others.  It is how ATS's printing
        // protocol works: a program supplies `fprint_val` for its own
        // types and the compiler keeps the ones it already knows.
        let ir = emit(
            "extern fun{a:t@ype} show (x: a): void\n\
             implement show<int> (x) = println!(x)\n\
             implement main0() = show<int> (1)",
        )
        .expect("emit");
        assert!(
            ir.contains("define void @show"),
            "the instance was not built:\n{ir}"
        );
    }

    #[test]
    fn an_instance_implement_does_not_answer_for_other_instances() {
        let err = emit_err(
            "extern fun{a:t@ype} show (x: a): void\n\
             implement show<int> (x) = println!(x)\n\
             implement main0() = show<bool> (true)",
        );
        assert!(err.message().contains("show"), "{err}");
    }

    #[test]
    fn a_hole_sees_the_lifted_form_of_a_function_it_calls() {
        // A `$`-hole is inlined into the scope it was written in, so its
        // body may call a nested function of that scope.  Lifting gives
        // such a function extra parameters for what it captured, and the
        // hole's call has to gain those arguments too — it is the same
        // call, written in the same place.
        let ir = emit(
            "fun run (xs: list0(int)): list0(int) = let\n\
               fn pick (i: int): int = list_nth<int> (xs, i)\n\
               implement list_tabulate$fopr<int> (i) = pick (i)\n\
             in list_tabulate<int> (3) end\n\
             implement main0() = println!(run(list_make_intrange(0, 5)))",
        )
        .expect("emit");
        assert!(ir.contains("tabulate.head"), "no tabulate loop:\n{ir}");
    }

    #[test]
    fn a_declared_function_with_no_definition_falls_to_the_shim() {
        // `extern fun srand48_with_time (): void = \"ext#\"` says the
        // definition lives outside ATS — in the `%{ ... %}` block this
        // compiler skips, because it emits LLVM IR and never runs a C
        // compiler.  Declaring it must therefore not stop the compiler
        // answering it, or the program links against a symbol nobody
        // ever defined.
        let ir =
            emit("extern fun srand48_with_time (): void\nimplement main0() = srand48_with_time()")
                .expect("emit");
        assert!(ir.contains("@srand48("), "the shim did not answer:\n{ir}");
        assert!(
            !ir.contains("call void @srand48_with_time"),
            "called a symbol nobody defines:\n{ir}"
        );
    }

    #[test]
    fn a_declared_function_with_no_definition_or_shim_is_declared_to_c() {
        // Nothing here knows `my_c_helper`, and `ext#` says it is C's.
        // Emitting a declaration for it is what makes an ATS program
        // able to call out at all.
        let ir = emit(
            "extern fun my_c_helper (x: int): int\nimplement main0() = println!(my_c_helper(1))",
        )
        .expect("emit");
        assert!(
            ir.contains("declare i64 @my_c_helper(i64)"),
            "no C declaration:\n{ir}"
        );
    }

    #[test]
    fn a_byte_buffer_is_a_pointer_and_dereferencing_it_changes_nothing() {
        // `b0ytes(n)` is `n` uninitialized bytes, and a pointer to them
        // is all there is at run time.  `!p` *views* those bytes as the
        // buffer rather than loading anything — there is no element type
        // to load.
        let ir = emit(
            "fun take (buf: &b0ytes(8), n: int): int = n\n\
             implement main0() = let val p = malloc_gc(8) in println!(take(!p, 8)) end",
        )
        .expect("emit");
        assert!(
            ir.contains("define i64 @take(ptr %buf, i64 %n)"),
            "got:\n{ir}"
        );
    }

    #[test]
    fn a_pointer_compared_against_zero_is_a_null_test() {
        // ATS writes `p > 0` for "the call gave me something".  A
        // pointer is not a number, so the comparison is the null test it
        // means rather than an ordering.
        let ir = emit(
            "implement main0() = let val p = malloc_gc(8) in if p > 0 then println!(1) else println!(0) end",
        )
        .expect("emit");
        assert!(ir.contains("icmp ne ptr"), "not a null test:\n{ir}");
    }

    #[test]
    fn matching_a_value_held_by_reference_names_its_cells() {
        // Taking apart a value you hold *by reference* gives references
        // to its parts: that is what lets the recursion in `intrange`
        // fill in the tail of the cons it just built.  No `@` is written
        // — in ATS the linearity of the value is what says so, and here
        // it is that the scrutinee is a cell.
        let ir = emit(
            "datatype box = Box of (int, box)\n\
             fun fill (b: &box): void = let\n\
               val () = b := Box (1, _)\n\
               val Box (_, rest) = b\n\
             in rest := b end\n\
             implement main0() = let var b: box = Box(1, _) val () = fill(b) in println!(1) end",
        )
        .expect("emit");
        assert!(
            ir.contains("define void @fill(ptr %b)"),
            "not by reference:\n{ir}"
        );
    }

    #[test]
    fn a_constructor_field_may_be_left_to_be_filled_in() {
        // `list_vt_cons(m, _)` builds a cons whose tail is not known
        // yet: the recursion writes it through the cell the match hands
        // back.  ATS's linear types are what promise nothing reads the
        // hole first, so the only job here is to leave it well-defined.
        let ir = emit(
            "datatype box = Box of (int, box)\n\
             implement main0() = let val b: box = Box(1, _) in println!(1) end",
        )
        .expect("emit");
        assert!(
            ir.contains("store ptr null, ptr %t."),
            "the hole is not defined:\n{ir}"
        );
    }

    #[test]
    fn a_parameter_the_body_assigns_to_is_passed_by_reference() {
        // `r: &int` where the body writes `r := 7` is an *out*
        // parameter: the write has to land in the caller's cell, so the
        // parameter is the address of that cell rather than a copy of
        // what it held.
        let ir = emit(
            "fun setit (r: &int): void = r := 7\n\
             implement main0() = let var x: int = 0 val () = setit(x) in println!(x) end",
        )
        .expect("emit");
        assert!(
            ir.contains("define void @setit(ptr %r)"),
            "not by reference:\n{ir}"
        );
        assert!(
            ir.contains("call void @setit(ptr %x.cell)"),
            "the cell was not passed:\n{ir}"
        );
    }

    #[test]
    fn a_parameter_only_read_is_still_passed_by_value() {
        // `&` on an aggregate says "the caller's array, not a copy", and
        // an array already *is* its storage.  Nothing is gained by
        // adding a level of indirection, so nothing is added.
        let ir = emit("fun peek (r: &int): int = r + 1\nimplement main0() = println!(peek(1))")
            .expect("emit");
        assert!(
            ir.contains("define i64 @peek(i64 %r)"),
            "needless indirection:\n{ir}"
        );
    }

    #[test]
    fn a_by_reference_argument_must_be_something_with_an_address() {
        let err = emit_err("fun setit (r: &int): void = r := 7\nimplement main0() = setit(1)");
        assert!(err.message().contains("var"), "{err}");
    }

    #[test]
    fn an_at_pattern_names_the_cells_of_a_value_not_copies_of_them() {
        // `val-@Box(n) = b` takes `b` apart *in place*: `n` names the
        // field itself, so assigning to it writes into `b`.  That is
        // what lets ATS build a list by filling in its own tail, and it
        // is the whole difference from an ordinary pattern.
        let ir = emit(
            "datatype box = Box of (int)\n\
             implement main0() = let val b = Box(1) val-@Box(n) = b in (n := 2; println!(n)) end",
        )
        .expect("emit");
        assert!(
            !ir.contains("%n.cell = alloca"),
            "the field was copied:\n{ir}"
        );
        assert!(
            ir.contains("store i64 2, ptr %t."),
            "no write into the value:\n{ir}"
        );
    }

    // --- records --------------------------------------------------

    #[test]
    fn printing_a_list_walks_it_and_separates_with_commas() {
        // ATS prints a list as its elements, comma-separated.  No format
        // string can say that — the length is not known until the list
        // is walked — so the print becomes a loop.
        let ir = emit(
            "implement main0() = let val xs: list0(int) = list0_cons(0, list0_nil()) in println!(\"xs = \", xs) end",
        )
        .expect("emit");
        assert!(ir.contains("print.list"), "no walk over the list:\n{ir}");
        assert!(ir.contains("c\", \\00\""), "no separator:\n{ir}");
    }

    #[test]
    fn a_top_level_val_with_no_name_still_runs() {
        // `val () = println! (...)` is how ATS writes a statement at the
        // top level.  It binds nothing, but it is the whole point of the
        // line, and dropping it loses the program's output.
        let ir = emit("implement main0() = ()\nval () = println!(\"hi\")").expect("emit");
        assert!(ir.contains("@.fmt"), "the statement was dropped:\n{ir}");
    }

    #[test]
    fn compare_yields_the_sign_of_the_difference() {
        // Not `x - y`: that overflows, and ATS promises the *sign*, not
        // the difference.
        let ir = emit("implement main0() = println!(compare(1, 2))").expect("emit");
        assert!(ir.contains("icmp sgt i64"), "no greater-than test:\n{ir}");
        assert!(ir.contains("icmp slt i64"), "no less-than test:\n{ir}");
    }

    #[test]
    fn a_record_allocates_one_slot_per_field() {
        let ir = emit(
            "implement main0() = let val p: '{ x= int, y= int } = '{ x= 1, y= 2 } in println!(1) end",
        )
        .expect("emit");
        assert!(
            ir.contains("call ptr @.ats_alloc(i64 16)"),
            "wrong width:\n{ir}"
        );
    }

    #[test]
    fn a_field_is_reached_by_the_slot_its_name_holds() {
        // `.y` is the second field, so it is one slot in — and which
        // slot a name means comes from the record's type, which is the
        // whole difference between a record and a tuple.
        let ir = emit(
            "implement main0() = let val p: '{ x= int, y= int } = '{ x= 1, y= 2 } in println!(p.y) end",
        )
        .expect("emit");
        // Two geps at offset 8 off the record: one to store `y`, one to
        // read it back.
        assert_eq!(
            ir.matches("getelementptr i8, ptr %t.0, i64 8").count(),
            2,
            "wrong slot:\n{ir}"
        );
    }

    #[test]
    fn a_field_a_record_does_not_have_is_an_error() {
        let err =
            emit_err("implement main0() = let val p: '{ x= int } = '{ x= 1 } in println!(p.z) end");
        assert!(err.message().contains("z"), "{err}");
    }

    #[test]
    fn a_record_field_may_hold_a_function() {
        // The point of a record in ATS is usually a *module*: a bundle of
        // functions passed around as one value.
        let ir = emit(
            "implement main0() = let\n\
               val m: '{ add= (int, int) -> int } = '{ add= lam (x: int, y: int): int => x + y }\n\
             in println!(m.add(1, 2)) end",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @lam.0"), "no lambda:\n{ir}");
    }

    // --- lazy streams ---------------------------------------------

    const ONES: &str = "fun ones(): stream(int) = $delay(stream_cons(1, ones()))\n";

    #[test]
    fn a_global_stream_starts_from_a_null_pointer() {
        // A global's declared initializer is a placeholder — `main`
        // overwrites it before anything runs — but it still has to be a
        // constant of the right type, and a stream is a pointer.
        let ir = emit(&format!(
            "{ONES}val first: stream(int) = ones()\nimplement main0() = ()"
        ))
        .expect("emit");
        assert!(
            ir.contains("@first = internal global ptr null"),
            "got:\n{ir}"
        );
    }

    #[test]
    fn a_delayed_stream_is_a_two_word_memo_cell() {
        // One word for the thunk, one for the answer it will produce.
        // The answer slot starts null, which is also what says the
        // stream has not been forced.
        let ir = emit(&format!("{ONES}implement main0() = ()")).expect("emit");
        assert!(
            ir.contains("store ptr null, ptr"),
            "no empty answer slot in:\n{ir}"
        );
    }

    #[test]
    fn forcing_a_stream_tests_whether_it_was_forced_before() {
        let ir = emit(&format!(
            "{ONES}implement main0() = let val s = ones() in case+ !s of | stream_cons(x, _) => println!(x) | stream_nil() => () end"
        ))
        .expect("emit");
        assert!(ir.contains("icmp eq ptr"), "no forced-yet test in:\n{ir}");
        assert!(ir.contains("stream.forced"), "no forced path in:\n{ir}");
    }

    #[test]
    fn a_linear_stream_has_the_same_representation_as_a_lazy_one() {
        // `stream_vt` is linear and `stream` is not, which is a
        // difference the type checker cares about and the machine does
        // not: both are a thunk and the answer it caches.
        let plain = emit(&format!("{ONES}implement main0() = ()")).expect("emit");
        let linear = emit(
            "fun ones(): stream_vt(int) = $ldelay(stream_vt_cons(1, ones()))\nimplement main0() = ()",
        )
        .expect("emit");
        assert_eq!(
            plain.matches("store ptr null, ptr").count(),
            linear.matches("store ptr null, ptr").count(),
            "different shapes:\n{plain}\n---\n{linear}"
        );
    }

    #[test]
    fn fprint_tupval_prints_a_tuple_in_ats_notation() {
        let ir = emit("implement main0() = fprint_tupval2<int,char> (stdout_ref, @(0, 'a'))")
            .expect("emit");
        assert!(ir.contains("(%ld, %c)"), "wrong format in:\n{ir}");
    }

    #[test]
    fn fprint_tupval_recurses_into_a_nested_tuple() {
        let ir = emit(
            "implement main0() = fprint_tupval2<int,tup(bool,char)> (stdout_ref, @(0, (true, 'a')))",
        )
        .expect("emit");
        assert!(ir.contains("(%ld, (%s, %c))"), "wrong format in:\n{ir}");
    }

    #[test]
    fn a_template_hole_stays_a_definition_even_with_template_parameters() {
        // `implement{env} f$hole (...)` is filled in by whoever
        // instantiates `f`, so it must not be mistaken for a template
        // waiting to be instantiated on its own.
        let ir = emit(
            "extern fun{a:t@ype} each (n: int): void\n\
             extern fun{a:t@ype} each$work (i: int): void\n\
             implement{a} each (n) = each$work<a> (n)\n\
             implement{a} each$work (i) = println!(i)\n\
             implement main0() = each<int> (3)",
        )
        .expect("emit");
        assert!(
            ir.contains("define void @each"),
            "the instance is missing:\n{ir}"
        );
    }

    #[test]
    fn an_uninitialized_var_of_a_datatype_starts_from_null() {
        let ir = emit("implement main0() = let var xs: list0(int) in xs := list0_nil() end")
            .expect("emit");
        assert!(ir.contains("store ptr null, ptr %xs.cell"), "got:\n{ir}");
    }

    #[test]
    fn assignment_stores_into_the_cell() {
        let ir = emit("implement main0() = let var x: int = 1 in x := 9 end").expect("emit");
        assert!(
            ir.contains("store i64 9, ptr %x.cell"),
            "no store in:\n{ir}"
        );
    }

    #[test]
    fn assigning_to_an_immutable_binding_is_an_error() {
        let err = emit_err("implement main0() = let val x: int = 1 in x := 9 end");
        assert!(err.message().contains("val"), "{err}");
    }

    #[test]
    fn assigning_an_unknown_name_is_an_error() {
        let err = emit_err("implement main0() = nosuch := 1");
        assert!(err.message().contains("nosuch"), "{err}");
    }

    #[test]
    fn assigning_the_wrong_type_is_an_error() {
        let err = emit_err("implement main0() = let var x: int = 1 in x := true end");
        assert!(err.message().contains("type"), "{err}");
    }

    #[test]
    fn a_while_loop_emits_a_header_body_and_exit() {
        let ir = emit("implement main0() = let var i: int = 0 in while (i < 3) i :=+ 1 end")
            .expect("emit");
        // The condition must live in its own block so it is re-evaluated
        // on every turn — a loop whose test sits in the entry block runs
        // at most once.
        assert!(ir.contains("while.cond."), "no condition block in:\n{ir}");
        assert!(ir.contains("while.body."), "no body block in:\n{ir}");
        assert!(ir.contains("while.end."), "no exit block in:\n{ir}");
        assert!(
            ir.contains("br label %while.cond."),
            "the body must jump back:\n{ir}"
        );
    }

    #[test]
    fn a_while_loop_has_type_void() {
        // A loop runs for its effects; it produces nothing.
        let err = emit_err("fun f(): int = let var i: int = 0 in while (i < 3) i :=+ 1 end");
        assert!(err.message().contains("void"), "{err}");
    }

    #[test]
    fn a_for_loop_puts_its_step_in_its_own_block() {
        let ir = emit(
            "implement main0() = let var i: int = 0 in for (i := 0; i < 3; i :=+ 1) println!(i) end",
        )
        .expect("emit");
        assert!(ir.contains("for.cond."), "no condition block in:\n{ir}");
        assert!(ir.contains("for.body."), "no body block in:\n{ir}");
        assert!(ir.contains("for.step."), "no step block in:\n{ir}");
        assert!(ir.contains("for.end."), "no exit block in:\n{ir}");
    }

    #[test]
    fn a_loop_condition_must_be_a_bool() {
        let err = emit_err("implement main0() = let var i: int = 0 in while (i) i :=+ 1 end");
        assert!(err.message().contains("bool"), "{err}");
    }

    // --- unsupported constructs -----------------------------------

    #[test]
    fn an_opaque_type_is_a_boxed_pointer_and_a_generic_list_is_too() {
        // A name no one declared is an *opaque* type: the record from a
        // signature file this compilation did not load, the abstraction
        // whose body no one may see, the `$rec` a program only passes
        // around.  Nothing here may take it apart, so a pointer is what
        // it is — the same box a type variable gets.  `Frobnicate` is a
        // spellcheck away from being one of those, and the checker is
        // the wall that catches a name that is truly nothing.
        let ir = emit("fun len(xs: Frobnicate): int = 0").expect("opaque type");
        assert!(ir.contains("define i64 @len(ptr %xs)"), "got:\n{ir}");
        // And a generic `list(a)` is a boxed datatype, with `a` its
        // boxed element: both lower to a pointer.
        let ir = emit("fun len(xs: list(a)): int = 0").expect("list(a) supports");
        assert!(ir.contains("define i64 @len(ptr %xs)"), "got:\n{ir}");
    }

    #[test]
    fn a_function_may_be_taken_as_an_argument() {
        // A function type is a closure type, so a parameter may hold one
        // and be applied like any other function.
        let ir = emit("fun apply(f: (int, int) -> int, x: int): int = f(x, x)").expect("emit");
        assert!(
            ir.contains("define i64 @apply(ptr %f, i64 %x)"),
            "got:\n{ir}"
        );
        assert!(
            ir.contains("call i64 %"),
            "the call must be indirect:\n{ir}"
        );
    }

    #[test]
    fn a_lambda_is_not_an_int() {
        // Lambdas work now, but one is still a closure and not a number.
        let err = emit_err("fun f(): int = lam (x: int) => x");
        assert!(err.message().contains("body has type"), "{}", err);
    }

    #[test]
    fn undefined_variables_are_errors() {
        let err = emit_err("fun f(x: int): int = y");
        assert!(err.message().contains("undefined variable"), "{}", err);
    }

    #[test]
    fn arithmetic_on_bools_is_an_error() {
        let err = emit_err("fun f(a: bool): int = a + 1");
        assert!(err.message().contains("arithmetic"), "{}", err);
    }

    // --- datatypes ------------------------------------------------

    #[test]
    fn a_datatype_declaration_emits_no_code_of_its_own() {
        // A datatype describes a *shape*.  Nothing is emitted for the
        // declaration itself: the code lives in the constructors that
        // build values and the `case`s that take them apart.
        let ir = emit("datatype intlist = Nil | Cons(int, intlist)").expect("emit");
        assert!(ir.contains("; datatype intlist"), "got:\n{ir}");
        assert!(!ir.contains("define"), "got:\n{ir}");
        // With nothing allocating, the arena is not emitted either.
        assert!(
            !ir.contains("@.heap"),
            "an unused arena should not appear:\n{ir}"
        );
    }

    // --- end-to-end demo program ----------------------------------

    #[test]
    fn compiles_the_factorial_demo_end_to_end() {
        let src = "\n(* factorial, in the ATS spirit *)\nfun fact(n: int): int = if n = 0 then 1 else n * fact(n - 1)\n\nimplement main0() = println!(\"fact(5) = \", fact(5))\n";
        let ir = emit(src).expect("emit");
        assert!(ir.contains("define i64 @fact(i64 %n)"), "got:\n{ir}");
        assert!(ir.contains("define i32 @main()"), "got:\n{ir}");
        assert!(ir.contains("call i64 @fact(i64 5)"), "got:\n{ir}");
        assert!(ir.contains("call i32 (ptr, ...) @printf"), "got:\n{ir}");
        assert!(ir.contains("fact(5) = %ld"), "got:\n{ir}");
    }

