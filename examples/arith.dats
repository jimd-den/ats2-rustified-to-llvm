(*
   arith.dats — the arithmetic operator family.

   Exercises +, -, *, /, mod and unary ~, and the precedence climbing that
   binds them: `*`, `/`, `mod` tighter than `+`, `-`; unary `~` tightest of
   all.  Integer division truncates toward zero and `mod` follows the sign
   of the dividend, which is exactly what LLVM's sdiv/srem give us.
*)

fun square (n: int): int = n * n

fun average (a: int, b: int): int = (a + b) / 2

implement main0 () = {
  val () = println! ("7 + 3 = ", 7 + 3)
  val () = println! ("7 - 3 = ", 7 - 3)
  val () = println! ("7 * 3 = ", 7 * 3)
  val () = println! ("7 / 3 = ", 7 / 3)
  val () = println! ("7 mod 3 = ", 7 mod 3)
  val () = println! ("~7 = ", ~7)
  val () = println! ("2 + 3 * 4 = ", 2 + 3 * 4)
  val () = println! ("(2 + 3) * 4 = ", (2 + 3) * 4)
  val () = println! ("square(9) = ", square (9))
  val () = println! ("average(10, 21) = ", average (10, 21))
}
