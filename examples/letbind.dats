(*
   letbind.dats — `let val ... in ... end`, the ATS binding form.

   A binding may carry a type annotation, which is checked against the type
   actually inferred for its right-hand side.  `val () = e` runs `e` purely
   for its effect.  Lets nest, and an inner binding shadows an outer one of
   the same name.  A `{ ... }` block is the same construct with the `let`,
   `in`, and `end` left out.
*)

fun hypot_squared (a: int, b: int): int =
  let
    val a2: int = a * a
    val b2: int = b * b
  in
    a2 + b2
  end

implement main0 () =
  let
    val x: int = 10
    val y = 32
    val () = println! ("x = ", x, ", y = ", y)
    val sum = x + y
    val shadowed = let val x = 100 in x + 1 end
  in
    println! ("x + y = ", sum, "; shadowed = ", shadowed, "; hypot2(3,4) = ", hypot_squared (3, 4))
  end
