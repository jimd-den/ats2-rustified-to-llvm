//
// Mutable aggregates: a tuple in a `var` cell, mutated through a
// function that was handed it.  A tuple is a pointer to its slots, so
// `xx.0 := ...` inside `step` is visible to the caller — which is what
// makes ATS's `&T` by-reference parameters work.
//
typedef T2 = (int, int)

fun step (xx: T2): void = let
  val x0 = xx.0 and x1 = xx.1
  val () = xx.0 := x1 and () = xx.1 := x0 + x1
in
end

fun fib (n: int): int = let
  var xx: T2 = (0, 1)
  fun loop (xx: T2, n: int): void =
    if n > 0 then let val () = step (xx) in loop (xx, n-1) end else ()
  val () = loop (xx, n)
in
  xx.0
end

implement main0 () = println! (fib (10))
