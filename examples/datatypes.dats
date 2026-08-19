(*
   datatypes.dats — tagged unions and pattern matching.

   A `datatype` names a shape with several forms.  Every value of one is a
   pointer to a record whose first word is the constructor's *tag* — its
   position in the declaration — and whose remaining words are its fields.
   One uniform shape is what lets `case` read a tag without knowing yet
   which constructor built the value.

   `case` tries its arms in order.  A constructor pattern tests the tag
   and, on a match, names the fields; a bare name matches anything and
   binds it; `_` matches anything and binds nothing.

   Allocation comes from a fixed arena rather than from `malloc`.  The
   subset has no way to free anything, so a real heap would simply be an
   unbounded leak; a bump pointer into a static buffer costs the same,
   cannot leak, and reports honestly when it runs out.
*)

datatype color = Red | Green | Blue

datatype intlist = Nil | Cons(int, intlist)

fun name_of (c: color): string =
  case c of
  | Red() => "red"
  | Green() => "green"
  | Blue() => "blue"

fun sum (xs: intlist): int =
  case xs of
  | Nil() => 0
  | Cons(x, rest) => x + sum(rest)

fun length (xs: intlist): int =
  case xs of
  | Cons(_, rest) => 1 + length(rest)
  | _ => 0

fun upto (n: int): intlist =
  if n <= 0 then Nil() else Cons(n, upto(n - 1))

implement main0 () =
  let
    val xs = upto(5)
  in
    println! (name_of(Red()), " ", name_of(Green()), " ", name_of(Blue()),
              " | sum = ", sum(xs), ", length = ", length(xs))
  end
