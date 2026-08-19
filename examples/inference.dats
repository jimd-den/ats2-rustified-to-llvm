(*
   inference.dats — the prelude's list, and instances nobody wrote down.

   Two things here are not declared anywhere in this file.

   The first is the list.  `list0` comes from the ATS prelude, which real
   programs reach through `#include "share/atspre_staload.hats"`; the
   handful of declarations that matter are built in, written in ATS and
   parsed like any other source.  ATS spells the same list three ways —
   `list0(t)`, `List0(t)`, and `list(t, n)` carrying its length — and
   since the length is static, all three name one runtime type.  `nil`
   and `cons` are the shorthands for its constructors.

   The second is the *instantiation*.  `len(xs)` names no instance, and
   `length` is a template: choosing between `len$int` and `len$char` means
   knowing the type of the argument, which no substitution can tell you.
   So the argument's type is worked out and matched against the
   parameter's declared type — `list0(a)` against `list0(int)` — and `a`
   falls out of the two lining up.

   Note that nothing here is checked so much as *found*: a type the
   compiler cannot work out simply stays unknown, and the call is left for
   the emitter to complain about. This pass can only turn a program that
   failed into one that works.
*)

fun digits (): List0(char) = cons('4', cons('2', nil()))

fun numbers (n: int): list0(int) =
  if n <= 0 then nil() else cons(n, numbers(n - 1))

extern fun{a:t@ype} len (xs: List0(INV(a))): int
implement{a} len (xs) =
  case xs of
  | cons(_, rest) => 1 + len(rest)
  | nil() => 0

extern fun{a:t@ype} first (xs: List0(a), fallback: a): a
implement{a} first (xs, fallback) =
  case xs of
  | cons(x, _) => x
  | nil() => fallback

fun total (xs: list0(int)): int =
  case xs of
  | cons(x, rest) => x + total(rest)
  | nil() => 0

implement main0 () =
  let
    val ds = digits()
    val ns = numbers(4)
  in
    println! ("len(chars) = ", len(ds),
              ", len(ints) = ", len(ns),
              ", first char = ", first(ds, '?'),
              ", first int = ", first(ns, ~1),
              ", total = ", total(ns))
  end
