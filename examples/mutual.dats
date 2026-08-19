(*
   mutual.dats — mutual recursion, and functions used before they are
   defined.

   `even` calls `odd`, which is not defined until afterwards.  The emitter
   collects every signature in a first pass, so definition order never
   matters — the same property that lets a recursive function call itself.
*)

fun even (n: int): bool = if n = 0 then true else odd (n - 1)

and odd (n: int): bool = if n = 0 then false else even (n - 1)

fun collatz_steps (n: int): int =
  if n <= 1 then 0
  else if even (n) then 1 + collatz_steps (n / 2)
  else 1 + collatz_steps (3 * n + 1)

implement main0 () = {
  val () = println! ("even(10) = ", even (10))
  val () = println! ("odd(10)  = ", odd (10))
  val () = println! ("collatz_steps(27) = ", collatz_steps (27))
}
