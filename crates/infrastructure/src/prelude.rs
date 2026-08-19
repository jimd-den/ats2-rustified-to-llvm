//! # The prelude — the declarations every ATS program assumes
//!
//! *Literate note.*  A real ATS program does not declare the list it uses.
//! It writes `#include "share/atspre_staload.hats"` and gets `list0`,
//! `List0`, `list`, and their constructors from the prelude sources — tens
//! of thousands of lines this compiler cannot yet read.
//!
//! Rather than fail on names every program uses, the handful that matter
//! are supplied here, written in ATS itself.  They are parsed by the same
//! parser as user code and prepended to the program, so nothing downstream
//! knows the difference — and because datatypes are instantiated on
//! demand, a prelude declaration nobody uses costs exactly nothing.
//!
//! A program that declares a name for itself keeps its own version: the
//! prelude fills gaps, it does not shadow.
//!
//! The aliases are the other half.  ATS spells the same list three ways —
//! `list0(t)` plain, `List0(t)` capitalised, and `list(t, n)` carrying its
//! length — and a program mixes them freely.  The length is *static*, so
//! all three describe one runtime type, and canonicalising them is what
//! lets a value built as one be consumed as another.

/// The prelude declarations, in ATS.
///
/// Written in the language itself rather than built into the emitter, so
/// that the parts of the prelude that *can* be expressed this way stay
/// readable as ATS.  Only the primitives underneath them —
/// `string_length`, `fileref_get_line_string` — are shims in the emitter.
pub const PRELUDE_SOURCE: &str = r#"
datatype list0(a) = list0_nil of () | list0_cons of (a, list0(a))

datatype stream_con(a) = stream_nil of () | stream_cons of (a, stream(a))

extern fun{a:t@ype} list0_is_nil (xs: list0(a)): bool
implement{a} list0_is_nil (xs) =
  case xs of | list0_nil() => true | list0_cons(_, _) => false

extern fun{a:t@ype} list0_is_cons (xs: list0(a)): bool
implement{a} list0_is_cons (xs) =
  case xs of | list0_nil() => false | list0_cons(_, _) => true

extern fun{a:t@ype} list0_length (xs: list0(a)): int
implement{a} list0_length (xs) =
  case xs of | list0_nil() => 0 | list0_cons(_, r) => 1 + list0_length(r)

// --- printing ----------------------------------------------------
//
// ATS prints through a *protocol*: `fprint_val<t>` says how a `t` is
// written, and a program supplies it for its own types.  The compiler
// answers for the ones it already knows — every primitive, and a list —
// so only the declaration lives here; the instances the program does not
// supply are filled in by the emitter.

extern fun{a:t@ype} fprint_val (out: FILEref, x: a): void

extern fun{a:t@ype}
fprint_list0_sep (out: FILEref, xs: list0(a), sep: string): void
extern fun{a:t@ype}
fprint_list0_rest (out: FILEref, xs: list0(a), sep: string): void

implement{a} fprint_list0_sep (out, xs, sep) =
  case+ xs of
  | list0_nil () => ()
  | list0_cons (x, r) => let
      val () = fprint_val<a> (out, x)
    in
      fprint_list0_rest<a> (out, r, sep)
    end

// The separator goes *before* every element but the first, which is why
// the walk splits in two rather than carrying a flag.
implement{a} fprint_list0_rest (out, xs, sep) =
  case+ xs of
  | list0_nil () => ()
  | list0_cons (x, r) => let
      val () = fprint! (out, sep)
      val () = fprint_val<a> (out, x)
    in
      fprint_list0_rest<a> (out, r, sep)
    end

// The singly-linked list library, in the terms of the list above.

extern fun{a:t@ype} sllist_length (xs: list0(a)): int
implement{a} sllist_length (xs) = list0_length<a> (xs)

extern fun{a:t@ype} sllist_free (xs: list0(a)): void
implement{a} sllist_free (xs) = ()

extern fun{a:t@ype} fprint_sllist (out: FILEref, xs: list0(a)): void
implement{a} fprint_sllist (out, xs) = fprint_list0_sep<a> (out, xs, ", ")

// --- lazy streams ------------------------------------------------
//
// A stream is a suspended `stream_con`, and every operation on one has
// the same two halves: a `$delay` that builds the suspension, and a
// function over the forced `stream_con` that says what one step is.
// Splitting them is what keeps the recursion productive — the delayed
// half returns immediately, so a stream can be infinite.

extern fun{a:t@ype} stream_nth_exn (xs: stream(a), n: int): a
implement{a} stream_nth_exn (xs, n) =
  case+ !xs of
  | stream_cons (x, xs1) => if n = 0 then x else stream_nth_exn<a> (xs1, n-1)
  | stream_nil () => $raise StreamSubscriptExn

extern fun{a:t@ype} stream_filter_cloref (xs: stream(a), p: (a) -> bool): stream(a)
extern fun{a:t@ype} stream_filter_con (c: stream_con(a), p: (a) -> bool): stream_con(a)

implement{a} stream_filter_cloref (xs, p) = $delay (stream_filter_con<a> (!xs, p))
implement{a} stream_filter_con (c, p) =
  case+ c of
  | stream_cons (x, xs1) =>
      if p (x)
        then stream_cons (x, stream_filter_cloref<a> (xs1, p))
        else stream_filter_con<a> (!xs1, p)
  | stream_nil () => stream_nil ()

extern fun{a,b:t@ype}{c:t@ype}
stream_map2_fun (xs: stream(a), ys: stream(b), f: (a, b) -> c): stream(c)
extern fun{a,b:t@ype}{c:t@ype}
stream_map2_fun_con (xs: stream_con(a), ys: stream_con(b), f: (a, b) -> c): stream_con(c)

implement{a,b}{c} stream_map2_fun (xs, ys, f) =
  $delay (stream_map2_fun_con<a,b><c> (!xs, !ys, f))
implement{a,b}{c} stream_map2_fun_con (xs, ys, f) =
  case+ xs of
  | stream_cons (x, xs1) =>
    (
      case+ ys of
      | stream_cons (y, ys1) =>
          stream_cons (f (x, y), stream_map2_fun<a,b><c> (xs1, ys1, f))
      | stream_nil () => stream_nil ()
    )
  | stream_nil () => stream_nil ()

// The linear spellings.  A linear stream may be forced once and a lazy
// one any number of times, which is a difference in what the type
// checker permits and in nothing else, so each is the other under a
// different name.

extern fun{a:t@ype} stream_vt_nth_exn (xs: stream(a), n: int): a
implement{a} stream_vt_nth_exn (xs, n) = stream_nth_exn<a> (xs, n)

extern fun{a:t@ype} stream_vt_filter_cloptr (xs: stream(a), p: (a) -> bool): stream(a)
implement{a} stream_vt_filter_cloptr (xs, p) = stream_filter_cloref<a> (xs, p)

extern fun{a:t@ype} stream_vt_filter_cloref (xs: stream(a), p: (a) -> bool): stream(a)
implement{a} stream_vt_filter_cloref (xs, p) = stream_filter_cloref<a> (xs, p)

extern fun{a,b:t@ype}{c:t@ype}
stream_vt_map2_fun (xs: stream(a), ys: stream(b), f: (a, b) -> c): stream(c)
implement{a,b}{c} stream_vt_map2_fun (xs, ys, f) =
  stream_map2_fun<a,b><c> (xs, ys, f)

// --- strings -----------------------------------------------------

fun string_is_empty (s: string): bool = string_length(s) = 0
fun string_isnot_empty (s: string): bool = string_length(s) > 0

fun fileref_get_lines_stringlst (f: FILEref): list0(string) =
  let
    val line = fileref_get_line_string(f)
  in
    if string_is_null(line)
      then list0_nil()
      else list0_cons(line, fileref_get_lines_stringlst(f))
  end
"#;

/// The datatypes the prelude declares.
pub const PRELUDE_DATATYPES: &[&str] = &["list0", "stream_con"];

/// Resolve a type name to the one the prelude actually declares, together
/// with how many of its arguments are *types* rather than static indices.
///
/// `list(int, n)` has two arguments but one type parameter: the `n` is a
/// length, which exists for the type checker and not at runtime.  Knowing
/// the declared arity is the only thing that can tell them apart, which is
/// why it is settled here rather than in the parser.
pub fn canonical_type(name: &str) -> Option<(&'static str, usize)> {
    match name {
        "list0" | "List0" | "list" | "List" | "list_vt" | "List0_vt" => Some(("list0", 1)),
        // A singly-linked list is the list this compiler already has:
        // the library that declares it differs in who owns the nodes,
        // which is a question of views and not of representation.
        "Sllist" | "sllist" | "sllist_vt" | "List1" | "list1" => Some(("list0", 1)),
        // A linear stream differs from a lazy one in who may force it
        // and how often — a question for the type checker.  Both are a
        // thunk and the cell that remembers what it produced, so they
        // share a name here.
        "stream_con" | "stream_vt_con" | "lazy_con" => Some(("stream_con", 1)),
        _ => None,
    }
}

/// Whether a type former names a suspended value — one that `!` forces.
///
/// ATS has four spellings for the same shape: lazy and linear, each with
/// its own word.  What separates them is who may force one and how
/// often, which is a question for the type checker.
pub fn is_a_suspension(name: &str) -> bool {
    matches!(name, "stream" | "stream_vt" | "lazy" | "llazy")
}

/// Whether a type former's first juxtaposed argument is a *type*.
///
/// ATS writes `stream N2` and `int n` the same way, and only the
/// former's declared sort says that one argument is a type and the
/// other a static index.  With no sort information to consult, the
/// formers whose argument is a type are listed — the list is short
/// because most of what a program juxtaposes really is an index.
pub fn takes_a_type_argument(name: &str) -> bool {
    matches!(name, "stream" | "stream_vt" | "lazy" | "llazy" | "stream_con" | "list0")
}

/// Every constructor alias the prelude provides, as (alias, declared).
pub const CTOR_ALIASES: &[(&str, &str)] = &[
    ("nil", "list0_nil"),
    ("cons", "list0_cons"),
    ("list_nil", "list0_nil"),
    ("list_cons", "list0_cons"),
    ("nil0", "list0_nil"),
    ("cons0", "list0_cons"),
    ("list_vt_nil", "list0_nil"),
    ("list_vt_cons", "list0_cons"),
    ("stream_vt_nil", "stream_nil"),
    ("stream_vt_cons", "stream_cons"),
];

/// The constructor a prelude alias names.
///
/// `nil`/`cons` are the overloaded shorthands ATS programs actually write;
/// `list0_nil`/`list0_cons` are what the datatype declares.
pub fn canonical_ctor(name: &str) -> Option<&'static str> {
    match name {
        "nil" | "list_nil" | "nil0" | "list_vt_nil" => Some("list0_nil"),
        "cons" | "list_cons" | "cons0" | "list_vt_cons" => Some("list0_cons"),
        "stream_vt_nil" => Some("stream_nil"),
        "stream_vt_cons" => Some("stream_cons"),
        _ => None,
    }
}
