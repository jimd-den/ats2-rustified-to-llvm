//! # The Static Prelude — proof, prop and sort declarations
//!
//! *Literate note.*  Declarations of dataprops, praxis, prfuns, and sort
//! constraints that are ambiently present in every ATS2 compilation unit.

pub const PRELUDE_STATIC_SOURCE: &str = r#"
//
// An array knows how long it is, and the length has to survive being
// built, taken apart and read through — `arrayptr_make_elt`, then
// `arrayptr_takeout_viewptr`, then `!p`.  Who owns the cells and who
// may free them is a question of *views*, which this compiler does not
// track; how many cells there are is not, and it is the only thing a
// bounds check can be made against.
//
// Every one of these hands back a *pointer*, which is what it is and
// what the emitter builds.  `ptr(n)` says both halves at once: the name
// is the truth about the representation, the index the truth about the
// length.  Naming an `array` here would be neater to read and a lie to
// the emitter, which would then intern two types where there is one.
//
extern fun{a:t@ype} arrayptr_make_elt {n:nat} (asz: size_t n, x: a): ptr(n)
extern fun{a:t@ype} array_ptr_alloc {n:nat} (asz: size_t n): ptr(n)
extern fun{a:t@ype} arrayref_make_elt {n:nat} (asz: size_t n, x: a): ptr(n)
//
// Taking the view out of an array pointer hands back a *pointer* —
// which is what it is, and what the emitter builds — to cells that are
// as many as they ever were.  `ptr(n)` says both halves of that: the
// name is the truth about the representation, the index the truth
// about the length.
//
extern fun arrayptr_takeout_viewptr {n:nat} (arr: ptr(n)): ptr(n)
extern fun arrayptr2ptr {n:nat} (arr: ptr(n)): ptr(n)
//
// A list carries its length, and every library function that changes
// the length says by how much.  This is what lets a recursion that
// shrinks a list be checked at all: `list_takeout_at` hands back one
// fewer, and nothing else in the file says so.
//
extern fun{a:t@ype} length {n:int} (xs: list(a, n)): size_t n
extern fun{a:t@ype} list_length {n:int} (xs: list(a, n)): size_t n
extern fun{a:t@ype} list_takeout_at {n:int}{i:nat | i < n}
  (xs: list(a, n), i: size_t i, x: &a): list(a, n-1)
extern fun{a:t@ype} list_nil (): list(a, 0)
extern fun{a:t@ype} list_cons {n:int} (x: a, xs: list(a, n)): list(a, n+1)
extern fun{a:t@ype} list_tail {n:pos} (xs: list(a, n)): list(a, n-1)
//
// The shims, declared.
//
// These have no body here: the emitter implements each of them
// directly, in one or two LLVM instructions.  What they lack is a
// *signature*, and without one the checker learns nothing from a call
// — `pred j` is an integer nobody can bound, and every loop written
// with it goes unchecked.  So the shape is written down, indexed, and
// the emitter goes on doing what it did.
//
// Measuring something owes nothing: `string_length(s)` is not a claim
// about `s`, it is how the length is found out in the first place.  A
// `{n:nat}` here would make every call prove what the call was for.
extern fun string_length {n:int} (s: string n): size_t n
extern fun string0_length {n:int} (s: string n): size_t n
extern fun string1_length {n:int} (s: string n): size_t n
extern fun strlen {n:int} (s: string n): size_t n
//
// `succ` and `pred` are what a loop counts with, and the whole reason
// a loop can be checked at all: `pred j` is `j-1`, and saying so is
// the difference between an invariant that survives an iteration and
// one that does not.
//
extern fun succ {i:int} (x: int i): int (i+1)
extern fun pred {i:int} (x: int i): int (i-1)
extern fun isucc {i:int} (x: int i): int (i+1)
extern fun ipred {i:int} (x: int i): int (i-1)
extern fun succ1 {i:int} (x: int i): int (i+1)
extern fun pred1 {i:int} (x: int i): int (i-1)
extern fun g1int_succ {i:int} (x: int i): int (i+1)
extern fun g1int_pred {i:int} (x: int i): int (i-1)
//
// The conversions move no bits and change no index: `g1i2u` is how a
// program says "this integer is a size now", and a checker that lost
// the index there would lose the bound with it.
//
extern fun g1i2u {i:int} (x: int i): size_t i
extern fun g0i2u {i:int} (x: int i): size_t i
extern fun g1int2uint {i:int} (x: int i): size_t i
extern fun g1u2i {i:int} (x: size_t i): int i
extern fun g0u2i {i:int} (x: size_t i): int i
extern fun g1uint2int {i:int} (x: size_t i): int i
extern fun g1ofg0 {i:int} (x: int i): int i
extern fun g1int_of_g0int {i:int} (x: int i): int i
//
"#;
