(*
   lists.dats — parameterized datatypes, tuples, and nested patterns.

   This is the shape the ATS prelude's list has: `datatype list0(a)`, a
   datatype with a type *parameter*.  LLVM has no such thing, so each
   element type the program actually uses becomes its own instance —
   `list0$int`, `list0$string` — by the same demand-driven rule that
   expands function templates.  An instance nobody asks for is never
   built.

   That raises a question a monomorphic datatype never does: `list0_nil()`
   names a constructor *every* instance has, and nothing in the expression
   says which one is meant.  The answer comes from the context — the
   function's declared return type, or the annotation on a binding — which
   is the checking direction of bidirectional typing, added exactly where
   inference runs out.

   Patterns may nest.  That is not free: reading the tail of a list is
   only safe once the value is known to be a `list0_cons`, since a
   `list0_nil` never wrote anything there.  So each test gets its own
   block and its own early exit, and every constructor of a datatype
   reserves the width of the widest, so that reading field `i` always
   lands inside the value.
*)

datatype list0(a) = list0_nil of () | list0_cons of (a, list0(a))

fun upto (n: int): list0(int) =
  if n <= 0 then list0_nil() else list0_cons(n, upto(n - 1))

fun sum (xs: list0(int)): int =
  case xs of
  | list0_nil() => 0
  | list0_cons(x, rest) => x + sum(rest)

fun length_int (xs: list0(int)): int =
  case xs of
  | list0_nil() => 0
  | list0_cons(_, rest) => 1 + length_int(rest)

(* a nested pattern: the second element, or ~1 when there isn't one *)
fun second (xs: list0(int)): int =
  case xs of
  | list0_cons(_, list0_cons(y, _)) => y
  | _ => ~1

(* a different element type builds a different instance *)
fun first_word (xs: list0(string)): string =
  case xs of
  | list0_nil() => "(none)"
  | list0_cons(w, _) => w

(* tuples, and a tuple pattern holding constructors *)
fun heads (p: (list0(int), list0(int))): int =
  case p of
  | (list0_cons(x, _), list0_cons(y, _)) => x + y
  | _ => 0

fun swap (p: (int, int)): (int, int) = case p of | (a, b) => (b, a)

fun fst (p: (int, int)): int = case p of | (a, b) => a

implement main0 () =
  let
    val ns = upto(5)
    val ws: list0(string) = list0_cons("hello", list0_nil())
  in
    println! ("sum = ", sum(ns),
              ", length = ", length_int(ns),
              ", second = ", second(ns),
              ", second [] = ", second(list0_nil()),
              ", word = ", first_word(ws),
              ", heads = ", heads((upto(3), upto(4))),
              ", swap = ", fst(swap((7, 9))))
  end
