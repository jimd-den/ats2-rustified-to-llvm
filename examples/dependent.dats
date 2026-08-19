//
// The static language, checked rather than skipped.
//
// `{n:nat}` is a promise about every call site: `fact` is never handed
// a negative number.  The compiler checks it before erasing it — a call
// `fact(~1)` is refused with a constraint error, while `fact(5)` is
// compiled, because the index is proved non-negative.
//
fun fact {n:nat} (x: int n): int =
  if x > 0 then x * fact (x-1) else 1

fun clamp {m:int | m >= 0} (x: int m): int = x

implement main0 () = println! (fact (5), " ", clamp (7))
