(*
   curried.dats — curried parameter lists.

   ATS lets a function be written `fun f (a: int) (b: int): int`.  The
   subset has no partial application, so the definition's lists are
   flattened into one and every call site is flattened to match.  Fully
   applied curried calls therefore work; partially applied ones would need
   closures and are rejected rather than silently mis-lowered.
*)

fun acker (m: int) (n: int): int =
  if m <= 0 then n + 1
  else if n <= 0 then acker (m - 1) (1)
  else acker (m - 1) (acker (m) (n - 1))

implement main0 () = {
  val () = println! ("acker(2)(3) = ", acker (2) (3))
  val () = println! ("acker(3)(3) = ", acker (3) (3))
}
