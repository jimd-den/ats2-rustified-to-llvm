//! # Checking real ATS, prelude and all
//!
//! *Literate note.*  The unit tests in `ats2-application` build syntax
//! trees by hand, which is the right way to pin a typing rule down: the
//! rule is the subject, and a parser between the test and the rule is
//! noise.  These tests are the other half.  They start from *source*,
//! because the questions here are about what a real program means —
//! whether `string_length` returns the length it was given, whether
//! `A[i]` is inside `A` — and those questions are only asked properly by
//! a program somebody could have written.
//!
//! The prelude is the reason this file exists.  Nearly every claim a real
//! ATS program makes rests on a declaration the program never wrote, and
//! a checker that cannot see those declarations cannot check anything but
//! toy code.

use ats2_application::checking::{Strictness, check_program};
use ats2_infrastructure::parser::Parser;

/// Parse `source` and check it strictly, returning the complaints.
fn check(source: &str) -> Vec<String> {
    let program = Parser::parse(source).expect("the source should parse");
    let mut defs = Vec::new();
    for text in [
        ats2_infrastructure::prelude::PRELUDE_SOURCE,
        ats2_infrastructure::prelude::PRELUDE_STATIC_SOURCE,
    ] {
        defs.extend(
            Parser::parse(text)
                .expect("the prelude should parse")
                .defs()
                .to_vec(),
        );
    }
    let prelude = ats2_domain::ast::Program::new(defs);
    check_program(&program, &prelude, Strictness::Strict)
        .into_iter()
        .map(|e| e.message)
        .collect()
}

#[test]
fn a_prelude_signature_is_in_scope_for_the_checker() {
    // `string_length` is the prelude's, and its result is the length of
    // the string it was given.  A program relying on that is checkable
    // only if the checker can see a declaration the program never wrote
    // — which is nearly every claim a real ATS program makes.
    let errs = check("fun f {n:nat} (s: string n): int n = string_length(s)");
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_program_may_still_declare_a_name_the_prelude_also_has() {
    // The prelude fills gaps; it does not shadow.  What the program
    // declares is the program's, and it is what its calls are checked
    // against.
    let errs = check(
        "extern fun string_length {n:nat} (s: string n): int (n+1) \
         fun f {n:nat} (s: string n): int (n+1) = string_length(s)",
    );
    assert!(
        errs.is_empty(),
        "the program's own declaration should win: {errs:?}"
    );
}

#[test]
fn a_prelude_signature_can_refuse_a_program() {
    // Seeing the prelude has to cut both ways, or it is not a check.
    let errs = check("fun f {n:nat} (s: string n): int (n+1) = string_length(s)");
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains("the result of `f`"), "{}", errs[0]);
}

#[test]
fn an_expected_result_determines_an_implicit_static_argument() {
    // There is no dynamic argument from which to infer `n`.  The promised
    // result determines it instead, before the callee's `nat` obligation is
    // checked: this call is the instance `choose{3}()`.
    let errs = check(
        "extern fun choose {n:nat} (): int n \
         fun three (): int 3 = choose()",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn an_expected_result_cannot_infer_an_instance_outside_its_sort() {
    // Bidirectional inference determines `n = ~1`, but it must not erase
    // the callee's `{n:nat}` requirement.  The chosen instance is invalid.
    let errs = check(
        "extern fun choose {n:nat} (): int n \
         fun negative (): int (~1) = choose()",
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains("call to `choose`"), "{}", errs[0]);
}

#[test]
fn a_cast_function_preserves_its_dependent_signature() {
    // `castfn` is a checked signature for an intentionally representation-
    // changing operation. Its result and an indexed top-level value both
    // retain their addresses, so the comparison establishes the promised
    // `bool(l == null)` rather than becoming an unknown boolean.
    let errs = check(
        "val the_null_ptr: ptr(null) = 0 \
         castfn preserve {l:addr} (x: ptr l): ptr l \
         fun is_null {l:addr} (x: ptr l): bool(l == null) = preserve(x) = the_null_ptr",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn an_unconstrained_implicit_static_argument_keeps_its_sort() {
    // The omitted indices are inference metavariables rather than arbitrary
    // caller-owned integers. Their sorts constrain the fresh instances, so
    // these calls do not owe `n%0 >= 0` or `p%0 > 0` from an empty context.
    let errs = check(
        "extern fun consume_nat {n:nat} (): void \
         extern fun consume_pos {p:pos} (): void \
         fun run_nat (): void = consume_nat() \
         fun run_pos (): void = consume_pos()",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn an_unconstrained_guarded_static_argument_is_not_invented() {
    // Intrinsic sort bounds have canonical inhabitants; an arbitrary guard
    // does not. In particular the checker must not assume that this
    // contradictory quantifier has a witness.
    let errs = check(
        "extern fun impossible {n:nat | n < 0} (): void \
         fun run (): void = impossible()",
    );
    assert!(!errs.is_empty(), "{errs:?}");
    assert!(errs.iter().all(|e| e.contains("call to `impossible`")));
}

#[test]
fn a_compile_time_constant_is_a_number_the_checker_knows() {
    // `#define N 1024` is not a variable: every mention of `N` *is*
    // 1024, decided before the program runs.  A checker that treated it
    // as an unknown could not prove the one thing it is written to make
    // obvious.
    let errs = check(
        "#define N 1024 \
         fun f {n:pos} (x: int n): int = x \
         implement main0() = f(N)",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_compile_time_constant_can_refuse_a_program_too() {
    let errs = check(
        "#define ZERO 0 \
         fun f {n:pos} (x: int n): int = x \
         implement main0() = f(ZERO)",
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains("is false"), "{}", errs[0]);
}

#[test]
fn a_bare_refinement_type_still_refines() {
    // `Nat` is `[i:nat] int i` — an integer nobody has named, known to
    // be non-negative.  No index is written, and the refinement is the
    // whole content of the name: collapsing it to `int` throws away the
    // only thing `Nat` says.
    for spelling in ["Nat", "nat"] {
        let errs = check(&format!(
            "fun f {{n:nat}} (x: int n): int = x \
             fun g (k: {spelling}): int = f(k)"
        ));
        assert!(errs.is_empty(), "{spelling}: {errs:?}");
    }
}

#[test]
fn a_bare_pos_is_stronger_than_a_bare_nat() {
    for spelling in ["Pos", "pos"] {
        let errs = check(&format!(
            "fun f {{n:pos}} (x: int n): int = x \
             fun g (k: {spelling}): int = f(k)"
        ));
        assert!(errs.is_empty(), "{spelling}: {errs:?}");
    }
    // ...and a `nat` is not a `pos`.
    let errs = check(
        "fun f {n:pos} (x: int n): int = x \
         fun g (k: Nat): int = f(k)",
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
}

#[test]
fn a_bare_refinement_is_still_an_ordinary_integer_to_the_emitter() {
    // Nothing about `Nat` changes what it is: an `int` in a register.
    let program = Parser::parse("fun g (k: Nat): int = k \n implement main0() = println!(g(3))")
        .expect("parse");
    ats2_infrastructure::llvm_ir::LlvmIrEmitter::emit(&program).expect("emit");
}

#[test]
fn an_index_buried_in_a_type_argument_is_still_found() {
    // `list0(list(int, n))` carries its index a level down, inside the
    // element type.  Matching only the outermost index leaves `n`
    // undetermined and every promise about the result unprovable —
    // which is how a list of lists goes unchecked.
    let errs = check(
        "extern fun g {n:nat} (xs: list0(list(int, n))): int n \
         fun f {k:nat} (xs: list0(list(int, k))): int k = g(xs)",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_buried_index_that_disagrees_is_still_owed() {
    // The depth must not cost the *check*, only the effort of reaching
    // it: a call that gets the nested length wrong is still wrong.
    let errs = check(
        "extern fun g {n:nat} (xs: list0(list(int, n))): int n \
         fun f {k:nat} (xs: list0(list(int, k))): int (k+1) = g(xs)",
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
}

#[test]
fn a_top_level_size_is_the_same_rule_read_at_depth_nought() {
    // `string(n)` was matched by a rule of its own before; it is the
    // shallowest case of this one, and must stay working.
    let errs = check("fun f {n:nat} (s: string n): int n = string_length(s)");
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_constructor_pattern_gives_its_fields_the_types_they_have() {
    // `case xs of list0_cons (x, rest) => ...` — the tail is a list of
    // the same thing the head came out of, and its length is the length
    // the scrutinee was carrying.  Binding the fields as unknowns is
    // what leaves every recursion over an indexed list unchecked.
    let errs = check(
        "extern fun g {n:nat} (xs: list0(list(int, n))): int \
         fun f {k:nat} (xss: list0(list(int, k))): int = \
           case+ xss of | list0_cons (x, rest) => g(rest) | list0_nil () => 0",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_field_of_a_constructor_pattern_carries_its_own_refinement() {
    // The head of a `list0(Nat)` is a `Nat`, and knowing so is what
    // lets the arm hand it to something that demands one.
    let errs = check(
        "fun needs_nat {n:nat} (x: int n): int = x \
         fun f (xs: list0(Nat)): int = \
           case+ xs of | list0_cons (x, rest) => needs_nat(x) | list0_nil () => 0",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_pattern_field_of_the_wrong_shape_still_claims_nothing() {
    // A scrutinee whose type nobody knows binds unknowns, as before —
    // the rule adds knowledge where there is some, and invents none.
    let errs = check(
        "fun needs_nat {n:nat} (x: int n): int = x \
         fun f (xs: list0(int)): int = \
           case+ xs of | list0_cons (x, rest) => needs_nat(x) | list0_nil () => 0",
    );
    assert_eq!(
        errs.len(),
        1,
        "an `int` is not known to be a `nat`: {errs:?}"
    );
}

#[test]
fn a_constructor_written_by_one_of_its_other_names_still_takes_the_value_apart() {
    // ATS spells the list constructors several ways — `cons`,
    // `list_cons`, `list_vt_cons` — and a program mixes them freely.
    // Which one was written says nothing about what the value is made
    // of, so it must not decide whether the pieces have types.
    for spelling in ["cons", "list_cons", "list0_cons"] {
        let errs = check(&format!(
            "extern fun g {{n:nat}} (xs: list0(list(int, n))): int \
             fun f {{k:nat}} (xss: list0(list(int, k))): int = \
               case+ xss of | {spelling} (x, rest) => g(rest) | _ => 0"
        ));
        assert!(errs.is_empty(), "{spelling}: {errs:?}");
    }
}

#[test]
fn an_indexed_constructor_pattern_refines_its_fields_and_result() {
    // Postiats declares `list_cons(a, k+1) of (a, list(a, k))`.
    // Matching it against `list(a, n)` introduces `k:nat`, establishes
    // `n == k+1`, and gives the tail type `list(a, k)`. Those are exactly
    // the facts that justify the structurally recursive call.
    let errs = check(
        "datatype list(a:t@ype, int) = \
           list_nil(a, 0) of () | \
           {k:nat} list_cons(a, k+1) of (a, list(a, k)) \
         fun drain {n:nat} .<n>. (xs: list(int, n)): int = \
           case+ xs of \
           | list_nil() => 0 \
           | list_cons(_, tail) => drain(tail)",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn each_indexed_constructor_arm_knows_which_result_it_matched() {
    // Result indices refine the scrutinee in both directions: `nil` proves
    // `n == 0`, while `cons` proves `n == k+1` for a fresh `k:nat`, hence
    // `n > 0`. Each arm spends exactly the fact its constructor introduced.
    let errs = check(
        "datatype list(a:t@ype, int) = \
           list_nil(a, 0) of () | \
           {k:nat} list_cons(a, k+1) of (a, list(a, k)) \
         extern fun needs_zero {n:int | n == 0} (): int \
         extern fun needs_positive {n:pos} (): int \
         fun classify {n:nat} (xs: list(int, n)): int = \
           case+ xs of \
           | list_nil() => needs_zero{n}() \
           | list_cons(_, _) => needs_positive{n}()",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_call_hands_on_the_type_of_what_it_returned() {
    // `g(mk(x))` — the argument is not a name, it is what another call
    // produced.  Its indices are in its *type*, and a checker that only
    // learns types from names cannot follow a value that was never
    // given one.
    let errs = check(
        "extern fun mk {k:nat} (x: int k): list0(list(int, k)) \
         extern fun g {n:nat} (xs: list0(list(int, n))): int n \
         fun f {k:nat} (x: int k): int k = g(mk(x))",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_binding_remembers_the_type_of_what_it_bound() {
    // The same value, given a name on the way past.
    let errs = check(
        "extern fun mk {k:nat} (x: int k): list0(list(int, k)) \
         extern fun g {n:nat} (xs: list0(list(int, n))): int n \
         fun f {k:nat} (x: int k): int k = let val ys = mk(x) in g(ys) end",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_templates_type_argument_reaches_its_result_type() {
    // `nth<N2>(...)` returns an `N2`, and `N2` is `intGte(2)` — an
    // integer known to be at least two.  A checker that read the result
    // as the bare parameter `a` would learn nothing from a call that
    // says precisely what it produces.
    let errs = check(
        "typedef N2 = intGte(2) \
         extern fun{a:t@ype} nth (xs: int, i: int): a \
         fun f (n: Nat): Nat = nth<N2>(0, n)",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_templates_type_argument_can_refuse_a_program_too() {
    // The substitution has to cut both ways: an instance that produces
    // something the caller's promise excludes is a call that is wrong.
    let errs = check(
        "typedef Neg = intLte(~1) \
         extern fun{a:t@ype} nth (xs: int, i: int): a \
         fun f (n: Nat): Nat = nth<Neg>(0, n)",
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains("is false"), "{}", errs[0]);
}

#[test]
fn a_template_called_without_naming_an_instance_claims_nothing_new() {
    // No type argument, nothing to substitute — and nothing invented.
    let errs = check(
        "extern fun{a:t@ype} nth (xs: int, i: int): a \
         fun f (n: Nat): Nat = nth(0, n)",
    );
    assert_eq!(
        errs.len(),
        1,
        "an unknown result cannot be shown to be a nat: {errs:?}"
    );
}

#[test]
fn an_arrays_size_survives_being_made_taken_apart_and_read_through() {
    // The corpus builds an array, takes a pointer out of it, and hands
    // that pointer on: `arrayptr_make_elt (asz, ~1)`, then
    // `arrayptr_takeout_viewptr`, then `!p`.  The length has to reach
    // the far end of that, or a function demanding `m > n` cannot be
    // called with the array that was built to satisfy it.
    let errs = check(
        "extern fun use {m,n:nat | m > n} (a: &(@[int][m]), i: int n): int \
         fun f {n:nat} (n: int n): int = let \
           val asz = g1i2u (n+1) \
           val arrp = arrayptr_make_elt<int> (asz, ~1) \
           val (pf | p) = arrayptr_takeout_viewptr (arrp) \
         in use (!p, n) end",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn an_array_too_short_for_what_it_is_handed_to_is_refused() {
    // The same chain, one element short: the promise `m > n` is then
    // false rather than merely unproved.
    let errs = check(
        "extern fun use {m,n:nat | m > n} (a: &(@[int][m]), i: int n): int \
         fun f {n:nat} (n: int n): int = let \
           val asz = g1i2u (n) \
           val arrp = arrayptr_make_elt<int> (asz, ~1) \
           val (pf | p) = arrayptr_takeout_viewptr (arrp) \
         in use (!p, n) end",
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains("is false"), "{}", errs[0]);
}

#[test]
fn taking_an_element_out_of_a_list_leaves_one_fewer() {
    // `list_takeout_at (xs, i, x)` removes the element at `i` and hands
    // back the rest — a list exactly one shorter.  Without that, every
    // recursion that shrinks a list by taking something out of it has a
    // length nobody can bound.
    let errs = check(
        "extern fun{a:t@ype} g {n:nat} (xs: list(a, n)): int \
         fun f {n:int} (xs: list(int, n), i: natLt(n)): int = let \
           var x: int \
           val xs1 = list_takeout_at<int> (xs, i, x) \
         in g<int>(xs1) end",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn the_length_of_a_list_is_the_length_it_carries() {
    let errs = check("fun f {n:nat} (xs: list(int, n)): int n = length<int>(xs)");
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_nested_function_can_see_what_it_captured() {
    // `fn fopr (i) = ... xs ...` reads `xs` from the function it is
    // written inside.  Checking it in a scope of its own makes every
    // captured value an unknown, and a nested loop — which is how ATS
    // writes nearly every one — goes unchecked.
    let errs = check(
        "extern fun{a:t@ype} g {n:nat} (xs: list(a, n)): int \
         fun outer {n:nat} (xs: list(int, n)): int = \
           let fun inner (): int = g<int>(xs) in inner() end",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_nested_functions_own_parameters_win_over_what_it_captured() {
    // Capturing must not overwrite: a parameter named like something
    // outside is the parameter.
    let errs = check(
        "fun f {n:pos} (x: int n): int = x \
         fun outer {k:pos} (x: int k): int = \
           let fun inner {m:pos} (x: int m): int = f(x) in inner(x) end",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn an_unsafe_cast_is_the_programmers_word_and_is_taken() {
    // `$UN.cast{T}(e)` is ATS's escape hatch: the programmer asserts a
    // type the checker cannot derive, and takes responsibility for it.
    // That is what `$UNSAFE` means, and a checker that argued with it
    // would reject every program that reaches for the hatch on purpose.
    let errs = check("fun f {n:int} (x: int n): intGte(0) = $UN.cast{intGte(0)}(x)");
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn without_the_cast_the_same_program_is_not_believed() {
    // The hatch has to be doing the work, or the test above proves
    // nothing about the hatch.
    let errs = check("fun f {n:int} (x: int n): intGte(0) = x");
    assert_eq!(errs.len(), 1, "{errs:?}");
}

#[test]
fn a_cast_demands_nothing_of_what_it_is_handed() {
    // The point of an unchecked cast is that it is unchecked: the value
    // going in owes nothing.
    let errs = check(
        "fun f {n:nat} (x: int n): int = x \
         fun g {n:int} (x: int n): int = f($UN.cast{intGte(0)}(x))",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn an_annotated_binding_records_the_type_it_was_annotated_with() {
    // `val xs: list(int, 5) = ...` says how long `xs` is.  The
    // annotation is the only place that says so for a list built out of
    // constructors, and a binding that kept only the value's index
    // would throw it away.
    let errs = check(
        "extern fun{a:t@ype} g {n:nat | n > 2} (xs: list(a, n)): int \
         extern fun mk (): int \
         fun f (): int = let val xs: list(int, 5) = mk() in g<int>(xs) end",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_length_is_known_to_be_a_length() {
    // A value of type `list(a, n)` exists, so `n` counted something:
    // lengths are not negative.  ATS makes a program ask for this with
    // `prval () = lemma_list_param (xs)`; it follows from the value
    // being there at all, so it is simply known.
    let errs = check(
        "extern fun{a:t@ype} g {n:nat} (xs: list(a, n)): int \
         fun f {n:int} (xs: list(int, n)): int = g<int>(xs)",
    );
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn measuring_something_owes_nothing() {
    // `string_length(s)` for a string nobody has measured is not a
    // claim about `s`; it is how the length is found out in the first
    // place.
    let errs = check("fun f (s: string): int = string_length(s)");
    assert!(errs.is_empty(), "{errs:?}");
}

/// Factorial as a proposition: the shape every ATS proof tutorial opens
/// with, and the smallest thing that is a *derivation* rather than a
/// claim.
const FACT: &str = "\
dataprop FACT (int, int) = \
| FACTbas (0, 1) of () \
| {n:pos} {r:int} FACTind (n, n*r) of (FACT (n-1, r)) \
";

#[test]
fn a_proof_whose_derivation_holds_is_accepted() {
    let errs = check(&format!("{FACT} prfun base (): FACT(0, 1) = FACTbas ()"));
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_proof_whose_derivation_does_not_hold_is_refused() {
    // `FACTbas` witnesses `FACT(0, 1)` and nothing else.  Offering it as
    // a proof of `FACT(0, 2)` is a false proof, and a proof language
    // that accepts one is decoration.
    let errs = check(&format!("{FACT} prfun bogus (): FACT(0, 2) = FACTbas ()"));
    assert!(!errs.is_empty(), "a false proof was accepted");
}

#[test]
fn an_axiom_is_still_taken_on_its_word() {
    // `praxi` has no derivation behind it — that is what an axiom *is*.
    // The checker must not invent an obligation it has no body to
    // discharge, or every ATS program that states a lemma stops
    // compiling.
    let errs = check(&format!("{FACT} praxi assumed (): FACT(3, 6)"));
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_proposition_keeps_the_indices_it_was_written_with() {
    // The gap this closes is upstream of the checker: `FACT(0, 1)` and
    // `list(int)` are the same shape on the page, so a proposition's
    // arguments were being read as *types* and the numbers dropped.
    // Every proposition became the bare name `FACT`, which every
    // derivation proved equally well.
    let program = Parser::parse(&format!("{FACT} prfun p (): FACT(0, 1) = FACTbas ()"))
        .expect("the source should parse");
    let found = program.defs().iter().any(|d| match d {
        ats2_domain::ast::Def::Fun(f) => {
            matches!(&f.ret, ats2_domain::ast::Ty::Index(_, idx) if idx.len() == 2)
        }
        _ => false,
    });
    assert!(found, "the proposition lost its indices");
}

#[test]
fn a_proof_by_induction_is_a_proof() {
    // The inductive step, which is what a `dataprop` is *for*: given a
    // proof about `n-1`, `FACTind` builds one about `n`.  It failed for
    // a reason worth stating — matching the constructor's `FACT(n-1, r)`
    // against the caller's identically-written `FACT(n-1, r)` returned
    // early on the two being equal, leaving `n` undetermined and so
    // renamed out of the caller's scope.  Every proof by induction sits
    // on that case, because an inductive step is exactly where the two
    // sides are written the same way.
    let errs = check(&format!(
        "{FACT} prfun step {{n:pos}} {{r:int}} (pf: FACT(n-1, r)): FACT(n, n*r) = FACTind (pf)"
    ));
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn an_inductive_step_that_claims_too_much_is_refused() {
    // The same derivation, promising `n*r+1` where it establishes `n*r`.
    let errs = check(&format!(
        "{FACT} prfun step {{n:pos}} {{r:int}} (pf: FACT(n-1, r)): FACT(n, n*r+1) = FACTind (pf)"
    ));
    assert!(!errs.is_empty(), "a false inductive step was accepted");
}

/// Multiplication as a proposition — `MUL(m, n, p)` for `m * n == p`.
///
/// The point of it is the inductive constructor: it establishes
/// `MUL(m+1, n, p+n)`, so a caller who wants `MUL(m+1, n, (m+1)*n)` owes
/// the equation `p + n == (m+1)*n` with `p` standing for `m*n`. That is
/// multiplying out, and nothing else.
const MUL: &str = "\
dataprop MUL (int, int, int) = \
| {n:int} MULbas (0, n, 0) of () \
| {m:nat} {n:int} {p:int} MULind (m+1, n, p+n) of (MUL (m, n, p)) \
";

#[test]
fn an_induction_over_a_product_is_a_proof() {
    // The obligation is `m*n + n == (m+1)*n`, which is true of every
    // integer pair and needs no arithmetic beyond multiplying out. It
    // was `Unknown` before, because `m*n` and `(m+1)*n` were abstracted
    // to two variables named after their printed forms and nothing
    // related them — so under the strict reading, which is the default,
    // this proof was refused.
    let errs = check(&format!(
        "{MUL} prfun step {{m:nat}} {{n:int}} \
         (pf: MUL (m, n, m*n)): MUL (m+1, n, (m+1)*n) = MULind (pf)"
    ));
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn an_induction_over_a_product_that_claims_too_much_is_refused() {
    // The same derivation, promising `(m+1)*n + 1`.  Multiplying out
    // has to make false claims *more* visible, not fewer: a solver that
    // proved this one would be worse than the abstraction it replaced.
    let errs = check(&format!(
        "{MUL} prfun step {{m:nat}} {{n:int}} \
         (pf: MUL (m, n, m*n)): MUL (m+1, n, (m+1)*n+1) = MULind (pf)"
    ));
    assert!(!errs.is_empty(), "a false inductive step was accepted");
}

#[test]
fn a_product_written_the_other_way_round_is_the_same_product() {
    // `MULbas` establishes `MUL(0, n, 0)`.  Asking it for `MUL(0, n, 0)`
    // with the zero spelled `n*0` is the same request, and used to be a
    // different one.
    let errs = check(&format!(
        "{MUL} prfun base {{n:int}} (): MUL (0, n, n*0) = MULbas ()"
    ));
    assert!(errs.is_empty(), "{errs:?}");
}
#[test]
fn a_product_of_nonnegative_indices_is_nonnegative() {
    // The sign rule for products, reached through the checker rather
    // than the solver alone: `m >= 0` and `n >= 0` force `m*n >= 0`, so
    // a proof whose only obligation is that bound goes through.
    let src = "\
dataprop GE0 (int) = | {k:int | k >= 0} GE0c (k) of () \
prfun lem {m:nat} {n:nat} (): GE0 (m*n) = GE0c {m*n} ()";
    let errs = check(src);
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_square_index_is_nonnegative_without_a_sign() {
    // `n*n >= 0` for any integer `n`, with no hypothesis about `n`'s
    // sign at all.  A lemma about magnitude cannot be stated without it.
    let src = "\
dataprop GE0 (int) = | {k:int | k >= 0} GE0c (k) of () \
prfun sq {n:int} (): GE0 (n*n) = GE0c {n*n} ()";
    let errs = check(src);
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_product_is_bounded_by_the_product_of_its_factors_bounds() {
    // `m >= 2` and `n >= 3` force `m*n >= 6`: the bound is the product
    // of the bounds, which only the McCormick envelope reads off.
    let src = "\
dataprop GE6 (int) = | {k:int | k >= 6} GE6c (k) of () \
prfun lem {m:int | m >= 2} {n:int | n >= 3} (): GE6 (m*n) = GE6c {m*n} ()";
    let errs = check(src);
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_product_claim_the_factors_do_not_force_is_refused() {
    // `m >= 0` and `n >= 0` do *not* force `m*n >= 1` — nought times
    // nought is nought.  The envelope stays inside the facts.
    let src = "\
dataprop GE1 (int) = | {k:int | k >= 1} GE1c (k) of () \
prfun lem {m:nat} {n:nat} (): GE1 (m*n) = GE1c {m*n} ()";
    let errs = check(src);
    assert!(!errs.is_empty(), "a product claim the factors do not force was accepted");
}

#[test]
fn nested_functions_with_the_same_name_keep_lexical_signatures() {
    // Local helper names are reused throughout Postiats. A global signature
    // table lets the second `aux` overwrite the first, making one valid call
    // answer to an unrelated refinement from another lexical scope.
    let src = "\
fun nonnegative (x: int): int = let
  fun aux {i:nat} (i: int i): int = i
in
  if x >= 0 then aux(x) else 0
end
fun negative (x: int): int = let
  fun aux {i:int | i < 0} (i: int i): int = i
in
  if x < 0 then aux(x) else 0
end";
    let errs = check(src);
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_refined_result_keeps_a_local_callees_signature() {
    // Result-directed checking walks through `let fun` independently of the
    // ordinary expression walk. The local signature must be in scope there
    // too, or the call returns an unknown `%self` despite its `Nat` result.
    let src = "\
fun answer (): Nat = let
  fun loop (): Nat = 0
in
  loop()
end";
    let errs = check(src);
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn the_empty_list_determines_a_dependent_call_length() {
    // `list_nil()` is not merely an opaque pointer: its indexed list length
    // is zero, which determines `j` in the callee instead of skolemising it.
    let src = "\
extern fun{a:t@ype} build {i,j:nat}
  (n: int i, xs: list(a, j)): list(a, i+j)
fun make {n:nat} (n: int n): list(int, n) =
  build<int>(n, list_nil())";
    let errs = check(src);
    assert!(errs.is_empty(), "{errs:?}");
}
