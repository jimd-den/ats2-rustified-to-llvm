//
// Arrays: a pointer to a run of cells, indexed with `.[i]`.
//
// An array's *length* is a static index, erased before emission, so the
// value here is only ever a pointer — which is why a bound is checked by
// the constraint checker rather than at run time.
//
fun sum {n:nat} (A: arrayptr(int), n: int n): int = let
  fun loop (A: arrayptr(int), i: int, n: int, acc: int): int =
    if i < n then loop (A, succ i, n, acc + A.[i]) else acc
in
  loop (A, 0, n, 0)
end

implement main0 () = let
  val A = arrayptr_make_elt<int> (5, 3)
  val () = A.[2] := 10
  val B = arrayptr_make_intrange (0, 4)
  val () = println! (sum (A, 5), " ", sum (B, 4))
  val () = arrayptr_free (A)
  val () = arrayptr_free (B)
in
end
