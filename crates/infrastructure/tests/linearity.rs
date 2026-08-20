//! # Resource checking, on programs somebody could have written
//!
//! *Literate note.*  ATS is two disciplines, not one.  The index language
//! says what a value *is*; the linear language says whose it is and for
//! how long.  A `datavtype` value must be consumed exactly once: used
//! twice it is a use-after-free, never used it is a leak, and neither is
//! anything an arithmetic solver could have an opinion about.
//!
//! These tests are written in source because the mistakes they describe
//! are mistakes of *shape* — a value handed over in one branch and kept
//! in the other — and a hand-built tree makes those hard to see.

use ats2_application::linearity::check_linearity;
use ats2_infrastructure::parser::Parser;

/// The declarations every test here shares: a linear box, something to
/// make one with, and something that takes one away.
const SETUP: &str = "\
datavtype box_vt (a) = mk_vt of (a) \
extern fun make_vt (): box_vt(int) \
extern fun free_vt (b: box_vt(int)): void \
extern fun peek_vt (b: !box_vt(int)): int \
";

fn faults(source: &str) -> Vec<String> {
    let program = Parser::parse(&format!("{SETUP}{source}")).expect("the source should parse");
    let prelude = Parser::parse(ats2_infrastructure::prelude::PRELUDE_SOURCE).expect("prelude");
    check_linearity(&program, &prelude).into_iter().map(|e| e.message).collect()
}

#[test]
fn giving_a_resource_away_once_is_what_it_is_for() {
    assert!(faults("fun f (b: box_vt(int)): void = free_vt(b)").is_empty());
}

#[test]
fn giving_the_same_resource_away_twice_is_refused() {
    // The second `free_vt(b)` is reaching for something that is not
    // there any more.  This is the mistake the whole discipline exists
    // to catch, and no amount of arithmetic would have found it.
    let errs = faults(
        "fun f (b: box_vt(int)): void = let val () = free_vt(b) in free_vt(b) end",
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains('b'), "{}", errs[0]);
    assert!(errs[0].contains("already"), "{}", errs[0]);
}

#[test]
fn a_resource_nobody_gives_away_is_refused() {
    let errs = faults("fun f (b: box_vt(int)): void = ()");
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains("never"), "{}", errs[0]);
}

#[test]
fn a_borrowed_resource_is_not_the_bodys_to_give_away() {
    // `!b` is lent.  The body may look at it and must not free it — and
    // must not be told it leaked something that was never its own.
    assert!(faults("fun f (b: !box_vt(int)): int = peek_vt(b)").is_empty());
}

#[test]
fn borrowing_does_not_use_a_resource_up() {
    assert!(faults(
        "fun f (b: box_vt(int)): void = let val _ = peek_vt(b) in free_vt(b) end"
    )
    .is_empty());
}

#[test]
fn branches_must_agree_about_what_they_gave_away() {
    // After the `if`, whether `b` is still there depends on which way it
    // went — and then nothing after it can be checked at all.
    let errs = faults(
        "fun f (c: bool, b: box_vt(int)): void = if c then free_vt(b) else ()",
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains("branch") || errs[0].contains("path"), "{}", errs[0]);
}

#[test]
fn branches_that_agree_are_accepted() {
    assert!(faults(
        "fun f (c: bool, b: box_vt(int)): void = if c then free_vt(b) else free_vt(b)"
    )
    .is_empty());
}

#[test]
fn an_ordinary_value_is_not_policed() {
    // Everything that is not declared linear is used as often as it
    // likes.  A check that said otherwise would be one nobody keeps on.
    assert!(faults(
        "datatype box (a) = mk of (a) \
         extern fun use_box (b: box(int)): void \
         fun f (b: box(int)): void = let val () = use_box(b) in use_box(b) end"
    )
    .is_empty());
}

#[test]
fn a_resource_a_body_made_is_a_resource_the_body_owes() {
    let errs = faults("fun f (): void = let val b = make_vt () in () end");
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains("never"), "{}", errs[0]);
}

#[test]
fn a_resource_a_body_made_and_gave_away_is_settled() {
    assert!(faults("fun f (): void = let val b = make_vt () in free_vt(b) end").is_empty());
}

#[test]
fn a_resource_the_body_made_and_gave_away_twice_is_refused() {
    // The same mistake as `giving_the_same_resource_away_twice`, but on
    // a resource the body made rather than one it was handed.  The two
    // `free_vt(b)` calls sit in separate statements of one block, which
    // is the shape a person actually writes — and the shape the earlier
    // tests, all phrased on a parameter, never put the walk through.
    let errs = faults(
        "fun f (): void = let val b = make_vt () val () = free_vt(b) in free_vt(b) end",
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains('b'), "{}", errs[0]);
    assert!(errs[0].contains("already"), "{}", errs[0]);
}

#[test]
fn a_resource_a_constructor_built_is_still_a_resource() {
    // `mk_vt(3)` has no signature to look up — the `datavtype`
    // declaration is the only thing that says it hands back something
    // owed.  Before the walk read that declaration, a value built this
    // way was invisible: freed twice without complaint, and dropped
    // without complaint either.
    let errs = faults("fun f (): void = let val b = mk_vt(3) in free_vt(b) end");
    assert!(errs.is_empty(), "{errs:?}");
}

#[test]
fn a_constructor_built_resource_given_away_twice_is_refused() {
    let errs = faults(
        "fun f (): void = let val b = mk_vt(3) val () = free_vt(b) in free_vt(b) end",
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains('b'), "{}", errs[0]);
    assert!(errs[0].contains("already"), "{}", errs[0]);
}

#[test]
fn a_constructor_built_resource_nobody_gives_away_is_refused() {
    let errs = faults("fun f (): void = let val b = mk_vt(3) in () end");
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains("never"), "{}", errs[0]);
}

#[test]
fn building_with_a_resource_hands_it_to_the_structure() {
    // `b` goes into the box and is the box's from then on.  The body
    // owes the box, not `b` — and must not be told it leaked `b`.
    let errs = faults(
        "fun f (b: box_vt(int)): void = let val outer = mk_vt(b) in free_vt(outer) end",
    );
    assert!(errs.is_empty(), "{errs:?}");
}
