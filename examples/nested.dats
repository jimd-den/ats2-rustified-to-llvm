(*
   nested.dats — functions defined inside functions.

   `step` reads `base`, a parameter of its enclosing `scaled_sum`.  LLVM
   has no nested functions and no closures, so the compiler *lifts* `step`
   to the top level, turning each captured variable into an extra
   parameter and rewriting the call sites to pass it.

   `where { ... }` opens the same kind of scope as `let`, written after
   the expression that uses it rather than before.
*)

fun scaled_sum (base: int, n: int): int =
  let
    fun step (i: int): int =
      if i > n then 0 else base * i + step (i + 1)
  in
    step (1)
  end

fun describe (n: int): int = doubled (n) + 1 where {
  fun doubled (k: int): int = 2 * k
}

implement main0 () = {
  val () = println! ("scaled_sum(10, 4) = ", scaled_sum (10, 4))
  val () = println! ("scaled_sum(1, 5)  = ", scaled_sum (1, 5))
  val () = println! ("describe(20) = ", describe (20))
}
