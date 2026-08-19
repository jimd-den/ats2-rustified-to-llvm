(*
   gcd.dats — Euclid's algorithm, the classic recursion on `mod`.

   `gcd` is tail recursive and `lcm` is built on top of it, so the two
   together exercise a call graph deeper than a single level resolving
   through the emitter's function registry.
*)

staload "prelude/DATS/integer.dats"

fun gcd (a: int, b: int): int = if b = 0 then a else gcd (b, a mod b)

fun lcm (a: int, b: int): int = a / gcd (a, b) * b

implement main0 () = {
  val () = println! ("gcd(48, 18) = ", gcd (48, 18))
  val () = println! ("gcd(17, 5)  = ", gcd (17, 5))
  val () = println! ("gcd(270, 0) = ", gcd (270, 0))
  val () = println! ("lcm(4, 6)   = ", lcm (4, 6))
}
