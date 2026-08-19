(*
   compare.dats — comparisons, booleans, and short-circuit evaluation.

   `andalso` and `orelse` are not strict in ATS: the right operand is
   evaluated only when the left one fails to settle the answer.  They are
   lowered to branches rather than to `and`/`or` instructions, so this
   program also checks that the merge points pick the right value.

   A bool prints as the word `true` or `false`, chosen with a `select`.
*)

fun is_even (n: int): bool = n mod 2 = 0

fun both_small (a: int, b: int): bool = a < 10 andalso b < 10

implement main0 () = {
  val () = println! ("3 = 3   -> ", 3 = 3)
  val () = println! ("3 <> 3  -> ", 3 <> 3)
  val () = println! ("3 < 4   -> ", 3 < 4)
  val () = println! ("3 <= 3  -> ", 3 <= 3)
  val () = println! ("4 > 3   -> ", 4 > 3)
  val () = println! ("3 >= 4  -> ", 3 >= 4)
  val () = println! ("is_even(10)      -> ", is_even (10))
  val () = println! ("both_small(2,3)  -> ", both_small (2, 3))
  val () = println! ("both_small(2,30) -> ", both_small (2, 30))
  val () = println! ("false orelse true -> ", is_even (7) orelse 7 > 5)
}
