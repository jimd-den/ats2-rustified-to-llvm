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

// --- lists -------------------------------------------------------
//
// The list library, in ATS.  Every function here is a template over an
// element type it never inspects, which is exactly what makes writing
// them in the language rather than in the emitter worth doing: a shim
// would have to be written once per element type, and these are written
// once.
//
// Nothing here costs a program that does not use it: the prelude is
// filtered down to the names a program mentions, and a template with no
// instantiation is never emitted.

extern fun{a:t@ype} list_length (xs: list0(a)): int
implement{a} list_length (xs) =
  case+ xs of
  | list0_nil () => 0
  | list0_cons (_, r) => 1 + list_length<a> (r)

extern fun{a:t@ype} list_append (xs: list0(a), ys: list0(a)): list0(a)
implement{a} list_append (xs, ys) =
  case+ xs of
  | list0_nil () => ys
  | list0_cons (x, r) => list0_cons (x, list_append<a> (r, ys))

// Reversing is the accumulating loop, not append-in-a-loop: the naive
// spelling walks the whole list again for every element.
extern fun{a:t@ype} list_reverse_append (xs: list0(a), acc: list0(a)): list0(a)
implement{a} list_reverse_append (xs, acc) =
  case+ xs of
  | list0_nil () => acc
  | list0_cons (x, r) => list_reverse_append<a> (r, list0_cons (x, acc))

extern fun{a:t@ype} list_reverse (xs: list0(a)): list0(a)
implement{a} list_reverse (xs) = list_reverse_append<a> (xs, list0_nil ())

extern fun{a:t@ype} list_nth (xs: list0(a), n: int): a
implement{a} list_nth (xs, n) =
  case+ xs of
  | list0_cons (x, r) => if n = 0 then x else list_nth<a> (r, n-1)
  | list0_nil () => $raise ListSubscriptExn

extern fun{a:t@ype} list_last (xs: list0(a)): a
implement{a} list_last (xs) =
  case+ xs of
  | list0_cons (x, r) =>
      (case+ r of list0_nil () => x | list0_cons (_, _) => list_last<a> (r))
  | list0_nil () => $raise ListSubscriptExn

extern fun{a:t@ype} list_head (xs: list0(a)): a
implement{a} list_head (xs) =
  case+ xs of
  | list0_cons (x, _) => x
  | list0_nil () => $raise ListSubscriptExn

extern fun{a:t@ype} list_tail (xs: list0(a)): list0(a)
implement{a} list_tail (xs) =
  case+ xs of
  | list0_cons (_, r) => r
  | list0_nil () => $raise ListSubscriptExn

extern fun{a:t@ype} list_take (xs: list0(a), n: int): list0(a)
implement{a} list_take (xs, n) =
  if n <= 0 then list0_nil ()
  else
    case+ xs of
    | list0_nil () => list0_nil ()
    | list0_cons (x, r) => list0_cons (x, list_take<a> (r, n-1))

extern fun{a:t@ype} list_drop (xs: list0(a), n: int): list0(a)
implement{a} list_drop (xs, n) =
  if n <= 0 then xs
  else
    case+ xs of
    | list0_nil () => list0_nil ()
    | list0_cons (_, r) => list_drop<a> (r, n-1)

// `list_make_intrange (m, n)` is [m, m+1, ..., n-1] — half-open, as
// every range in ATS is.
extern fun list_make_intrange (m: int, n: int): list0(int)
implement list_make_intrange (m, n) =
  if m >= n then list0_nil () else list0_cons (m, list_make_intrange (m+1, n))

extern fun{a:t@ype} list_concat (xss: list0(list0(a))): list0(a)
implement{a} list_concat (xss) =
  case+ xss of
  | list0_nil () => list0_nil ()
  | list0_cons (xs, r) => list_append<a> (xs, list_concat<a> (r))

// --- the higher-order half ---------------------------------------
//
// ATS gives each of these two spellings: one taking a closure, and one
// with a `$`-hole the caller fills in.  The closure form is the one
// that can be written in ATS, so it is the one written here.

extern fun{a:t@ype}{b:t@ype}
list_map_cloref (xs: list0(a), f: (a) -> b): list0(b)
implement{a}{b} list_map_cloref (xs, f) =
  case+ xs of
  | list0_nil () => list0_nil ()
  | list0_cons (x, r) => list0_cons (f (x), list_map_cloref<a><b> (r, f))

extern fun{a:t@ype}
list_filter_cloref (xs: list0(a), p: (a) -> bool): list0(a)
implement{a} list_filter_cloref (xs, p) =
  case+ xs of
  | list0_nil () => list0_nil ()
  | list0_cons (x, r) =>
      if p (x)
        then list0_cons (x, list_filter_cloref<a> (r, p))
        else list_filter_cloref<a> (r, p)

extern fun{a:t@ype}{b:t@ype}
list_foldleft_cloref (xs: list0(a), init: b, f: (b, a) -> b): b
implement{a}{b} list_foldleft_cloref (xs, init, f) =
  case+ xs of
  | list0_nil () => init
  | list0_cons (x, r) => list_foldleft_cloref<a><b> (r, f (init, x), f)

extern fun{a:t@ype}{b:t@ype}
list_foldright_cloref (xs: list0(a), f: (a, b) -> b, init: b): b
implement{a}{b} list_foldright_cloref (xs, f, init) =
  case+ xs of
  | list0_nil () => init
  | list0_cons (x, r) => f (x, list_foldright_cloref<a><b> (r, f, init))

extern fun{a:t@ype} list_foreach_cloref (xs: list0(a), f: (a) -> void): void
implement{a} list_foreach_cloref (xs, f) =
  case+ xs of
  | list0_nil () => ()
  | list0_cons (x, r) => let val () = f (x) in list_foreach_cloref<a> (r, f) end

extern fun{a:t@ype} list_exists_cloref (xs: list0(a), p: (a) -> bool): bool
implement{a} list_exists_cloref (xs, p) =
  case+ xs of
  | list0_nil () => false
  | list0_cons (x, r) => if p (x) then true else list_exists_cloref<a> (r, p)

extern fun{a:t@ype} list_forall_cloref (xs: list0(a), p: (a) -> bool): bool
implement{a} list_forall_cloref (xs, p) =
  case+ xs of
  | list0_nil () => true
  | list0_cons (x, r) => if p (x) then list_forall_cloref<a> (r, p) else false

extern fun{a:t@ype} list_tabulate_cloref (n: int, f: (int) -> a): list0(a)
extern fun{a:t@ype} list_tabulate_from (i: int, n: int, f: (int) -> a): list0(a)
implement{a} list_tabulate_cloref (n, f) = list_tabulate_from<a> (0, n, f)
implement{a} list_tabulate_from (i, n, f) =
  if i >= n then list0_nil ()
  else list0_cons (f (i), list_tabulate_from<a> (i+1, n, f))

// --- taking a list apart at an index -----------------------------

// The element at `i` is written back through `x`, and what is returned
// is the list without it.  ATS spells the out-parameter `&a`, and here
// it is the assignment in the body that makes it one.
extern fun{a:t@ype}
list_takeout_at (xs: list0(a), i: int, x: &a): list0(a)
implement{a} list_takeout_at (xs, i, x) =
  case+ xs of
  | list0_nil () => list0_nil ()
  | list0_cons (y, r) =>
      if i = 0
        then let val () = x := y in r end
        else list0_cons (y, list_takeout_at<a> (r, i-1, x))

extern fun{a:t@ype} list_insert_at (xs: list0(a), i: int, x: a): list0(a)
implement{a} list_insert_at (xs, i, x) =
  if i <= 0 then list0_cons (x, xs)
  else
    case+ xs of
    | list0_nil () => list0_cons (x, list0_nil ())
    | list0_cons (y, r) => list0_cons (y, list_insert_at<a> (r, i-1, x))

extern fun{a:t@ype} list_remove_at (xs: list0(a), i: int): list0(a)
implement{a} list_remove_at (xs, i) =
  case+ xs of
  | list0_nil () => list0_nil ()
  | list0_cons (y, r) =>
      if i = 0 then r else list0_cons (y, list_remove_at<a> (r, i-1))

// --- sorting -----------------------------------------------------
//
// A merge sort, in ATS.  The ordering arrives as a closure rather than
// as a `$`-hole because a closure is what the language can express, and
// `<=` on the caller's own type is the one thing the library cannot
// know.  Merge sort rather than quicksort: it is stable, and its worst
// case is its average case, which matters more in a library than the
// constant factor does.

extern fun{a:t@ype}
list_merge_cloref (xs: list0(a), ys: list0(a), le: (a, a) -> bool): list0(a)
implement{a} list_merge_cloref (xs, ys, le) =
  case+ xs of
  | list0_nil () => ys
  | list0_cons (x, xr) =>
    (
      case+ ys of
      | list0_nil () => xs
      | list0_cons (y, yr) =>
          // `le` rather than `lt`, and the left side taken when they are
          // equal: that is what makes the sort stable.
          if le (x, y)
            then list0_cons (x, list_merge_cloref<a> (xr, ys, le))
            else list0_cons (y, list_merge_cloref<a> (xs, yr, le))
    )

extern fun{a:t@ype}
list_mergesort_cloref (xs: list0(a), le: (a, a) -> bool): list0(a)
implement{a} list_mergesort_cloref (xs, le) = let
  val n = list_length<a> (xs)
in
  if n <= 1 then xs
  else let
    val half = n / 2
  in
    list_merge_cloref<a> (
      list_mergesort_cloref<a> (list_take<a> (xs, half), le)
    , list_mergesort_cloref<a> (list_drop<a> (xs, half), le)
    , le
    )
  end
end

extern fun{a:t@ype} list_min_cloref (xs: list0(a), le: (a, a) -> bool): a
implement{a} list_min_cloref (xs, le) =
  case+ xs of
  | list0_nil () => $raise ListEmptyExn
  | list0_cons (x, r) =>
    (
      case+ r of
      | list0_nil () => x
      | list0_cons (_, _) => let
          val rest = list_min_cloref<a> (r, le)
        in
          if le (x, rest) then x else rest
        end
    )

extern fun{a:t@ype} list_max_cloref (xs: list0(a), le: (a, a) -> bool): a
implement{a} list_max_cloref (xs, le) =
  list_min_cloref<a> (xs, lam (p, q) => le (q, p))

// --- pairing and searching ---------------------------------------

extern fun{a:t@ype}{b:t@ype}{c:t@ype}
list_zip_with_cloref (xs: list0(a), ys: list0(b), f: (a, b) -> c): list0(c)
implement{a,b}{c} list_zip_with_cloref (xs, ys, f) =
  case+ xs of
  | list0_nil () => list0_nil ()
  | list0_cons (x, xr) =>
    (
      case+ ys of
      | list0_nil () => list0_nil ()
      | list0_cons (y, yr) =>
          list0_cons (f (x, y), list_zip_with_cloref<a,b><c> (xr, yr, f))
    )

// The position of the first element satisfying `p`, or -1.  ATS returns
// an option from `find` and an index from `index`; both are here,
// because a caller that wants the position gains nothing from being
// handed the element.
extern fun{a:t@ype} list_index_cloref (xs: list0(a), p: (a) -> bool): int
extern fun{a:t@ype} list_index_from (xs: list0(a), i: int, p: (a) -> bool): int
implement{a} list_index_cloref (xs, p) = list_index_from<a> (xs, 0, p)
implement{a} list_index_from (xs, i, p) =
  case+ xs of
  | list0_nil () => ~1
  | list0_cons (x, r) => if p (x) then i else list_index_from<a> (r, i+1, p)

// --- option ------------------------------------------------------
//
// The answer to \"there may not be one\".  A datatype rather than a
// sentinel, so that `None` is a value the type system can see and a
// caller cannot forget to check.

datatype option0(a) = option0_none of () | option0_some of (a)

extern fun{a:t@ype} option_is_some (o: option0(a)): bool
implement{a} option_is_some (o) =
  case+ o of option0_some (_) => true | option0_none () => false

extern fun{a:t@ype} option_is_none (o: option0(a)): bool
implement{a} option_is_none (o) =
  case+ o of option0_some (_) => false | option0_none () => true

extern fun{a:t@ype} option_unwrap_or (o: option0(a), fallback: a): a
implement{a} option_unwrap_or (o, fallback) =
  case+ o of option0_some (x) => x | option0_none () => fallback

extern fun{a:t@ype} option_unwrap_exn (o: option0(a)): a
implement{a} option_unwrap_exn (o) =
  case+ o of
  | option0_some (x) => x
  | option0_none () => $raise OptionNoneExn

extern fun{a:t@ype}{b:t@ype}
option_map_cloref (o: option0(a), f: (a) -> b): option0(b)
implement{a}{b} option_map_cloref (o, f) =
  case+ o of
  | option0_some (x) => option0_some (f (x))
  | option0_none () => option0_none ()

extern fun{a:t@ype}
list_find_cloref (xs: list0(a), p: (a) -> bool): option0(a)
implement{a} list_find_cloref (xs, p) =
  case+ xs of
  | list0_nil () => option0_none ()
  | list0_cons (x, r) =>
      if p (x) then option0_some (x) else list_find_cloref<a> (r, p)

// --- arrays ------------------------------------------------------
//
// The array primitives — allocating one, taking the pointer out of one —
// are shims, because they are about storage and storage is the
// emitter's business.  Everything built *on* them is here, in ATS, for
// the same reason the list library is.

extern fun{a:t@ype} array_copy (dst: arrayptr(a), src: arrayptr(a), n: int): void
extern fun{a:t@ype} array_copy_from (dst: arrayptr(a), src: arrayptr(a), i: int, n: int): void
implement{a} array_copy (dst, src, n) = array_copy_from<a> (dst, src, 0, n)
implement{a} array_copy_from (dst, src, i, n) =
  if i >= n then ()
  else let
    val () = dst.[i] := src.[i]
  in
    array_copy_from<a> (dst, src, i+1, n)
  end

// --- generic printing --------------------------------------------
//
// The `gprint` family writes a value without saying what it is; which
// one it is comes from `fprint_val`, the same protocol the list printer
// uses.

extern fun gprint_string (s: string): void
implement gprint_string (s) = print! (s)

extern fun gprint_newline (): void
implement gprint_newline () = print_newline ()

extern fun{a:t@ype} gprint_arrayptr (A: arrayptr(a), n: int): void
extern fun{a:t@ype} gprint_arrayptr_from (A: arrayptr(a), i: int, n: int): void
implement{a} gprint_arrayptr (A, n) = gprint_arrayptr_from<a> (A, 0, n)
implement{a} gprint_arrayptr_from (A, i, n) =
  if i >= n then ()
  else let
    val () = if i > 0 then print! (", ")
    val () = print_val<a> (A.[i])
  in
    gprint_arrayptr_from<a> (A, i+1, n)
  end

// --- random values -----------------------------------------------
//
// `randgen_val` is a protocol, not a function: the library cannot know
// what a random value of the caller's type looks like, so the caller
// says.  Only the array-filling half can be written here.

extern fun{a:t@ype} randgen_val (): a
extern fun{a:t@ype} randgen_arrayptr (n: int): arrayptr(a)
extern fun{a:t@ype} randgen_arrayptr_fill (A: arrayptr(a), i: int, n: int): void

implement{a} randgen_arrayptr (n) = let
  val A = arrayptr_make_elt<a> (n, randgen_val<a> ())
in
  let val () = randgen_arrayptr_fill<a> (A, 0, n) in A end
end
implement{a} randgen_arrayptr_fill (A, i, n) =
  if i >= n then ()
  else let
    val () = A.[i] := randgen_val<a> ()
  in
    randgen_arrayptr_fill<a> (A, i+1, n)
  end

// `length` is what ATS programs actually write; `list_length` is what the
// library calls it.
extern fun{a:t@ype} length (xs: list0(a)): int
implement{a} length (xs) = list_length<a> (xs)

// The linear spellings.  A linear list differs from this one in who may
// keep it and for how long, which is a question for the type checker and
// not for the machine, so each is the other under a different name.
extern fun{a:t@ype} list_vt_length (xs: list0(a)): int
implement{a} list_vt_length (xs) = list_length<a> (xs)

extern fun{a:t@ype} list_vt_concat (xss: list0(list0(a))): list0(a)
implement{a} list_vt_concat (xss) = list_concat<a> (xss)

extern fun{a:t@ype} list_vt_append (xs: list0(a), ys: list0(a)): list0(a)
implement{a} list_vt_append (xs, ys) = list_append<a> (xs, ys)

extern fun{a:t@ype} list_vt_reverse (xs: list0(a)): list0(a)
implement{a} list_vt_reverse (xs) = list_reverse<a> (xs)

extern fun{a:t@ype} list_vt_free (xs: list0(a)): void
implement{a} list_vt_free (xs) = ()

// `list_tabulate (n)` is the list [f 0, ..., f (n-1)], where `f` is the
// `$fopr` the caller fills in.  It is *not* here: a routine built around
// a `$`-hole cannot be written in ATS by this compiler, because a hole
// is inlined into the caller\'s scope rather than called, and its body
// reads the caller\'s own bindings.  Writing it in ATS would turn the
// inlining into a call and lose exactly that.  It is a shim; the
// closure-taking `list_tabulate_cloref` above is the half that *can* be
// written here, and is the one to prefer.

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
pub const PRELUDE_DATATYPES: &[&str] = &["list0", "stream_con", "option0"];

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
        // `array`, `arrayptr` and `arrayref` differ in who owns the
        // cells and who may free them — views, all of it, and all erased
        // before anything runs.  One name here is what lets a function
        // declared over `&array(a, n)` be matched against an argument
        // whose type says `arrayptr(a)`.  The length is a static index,
        // so only the element type survives.
        "array" | "arrayptr" | "arrayref" | "arrszref" | "Array" | "Arrayptr" => {
            Some(("array", 1))
        }
        // ATS spells the option several ways, and the linear one differs
        // only in who may keep it.  `opt` is deliberately not among them:
        // it is a name a program is as likely to want for itself, and an
        // alias here would rename the program's own datatype out from
        // under it.
        "option" | "Option" | "option0" | "option_vt" | "Option_vt" => {
            Some(("option0", 1))
        }
        // A linear stream differs from a lazy one in who may force it
        // and how often — a question for the type checker.  Both are a
        // thunk and the cell that remembers what it produced, so they
        // share a name here.
        "stream_con" | "stream_vt_con" | "lazy_con" => Some(("stream_con", 1)),
        _ => None,
    }
}

/// Whether a call hands its argument straight back, unchanged.
///
/// These are the casts and re-viewings ATS writes between types that
/// share one machine representation: `ptrcast` turns an `arrayptr` into
/// a `ptr`, `arrayptr_takeout` hands out the array inside one.  Each
/// moves no bits, and in ATS what it *does* move — which type the value
/// may now be read at — travels separately, in a proof.
///
/// Proofs are erased here, so a cast that inference could not see
/// through would take the element type with it and never give it back.
/// Treating these as transparent is what keeps `revarr (!p, n)` able to
/// say which instance it means, and it is honest: they are transparent
/// to the machine as well.
pub fn preserves_its_argument_type(name: &str) -> bool {
    matches!(
        name,
        "ptrcast"
            | "arrayptr2ptr"
            | "ptr2arrayptr"
            | "arrayptr_takeout"
            | "arrayptr_takeout_viewptr"
            | "arrayptr_refize"
            | "g0ofg1"
            | "g1ofg0"
            | "list_vt2t"
            | "list_t2vt"
            | "g0ofg1_list"
            | "unsafe_cast"
    )
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
    ("nil_vt", "list0_nil"),
    ("cons_vt", "list0_cons"),
    ("list_vt_nil", "list0_nil"),
    ("list_vt_cons", "list0_cons"),
    ("cons0", "list0_cons"),
    ("list_vt_nil", "list0_nil"),
    ("list_vt_cons", "list0_cons"),
    ("None", "option0_none"),
    ("Some", "option0_some"),
    ("None_vt", "option0_none"),
    ("Some_vt", "option0_some"),
    ("option_none", "option0_none"),
    ("option_some", "option0_some"),
    ("stream_vt_nil", "stream_nil"),
    ("stream_vt_cons", "stream_cons"),
];

/// The constructor a prelude alias names.
///
/// `nil`/`cons` are the overloaded shorthands ATS programs actually write;
/// `list0_nil`/`list0_cons` are what the datatype declares.
pub fn canonical_ctor(name: &str) -> Option<&'static str> {
    match name {
        "nil" | "list_nil" | "nil0" | "list_vt_nil" | "nil_vt" => Some("list0_nil"),
        "cons" | "list_cons" | "cons0" | "list_vt_cons" | "cons_vt" => Some("list0_cons"),
        "None" | "None_vt" | "option_none" => Some("option0_none"),
        "Some" | "Some_vt" | "option_some" => Some("option0_some"),
        "stream_vt_nil" => Some("stream_nil"),
        "stream_vt_cons" => Some("stream_cons"),
        _ => None,
    }
}
