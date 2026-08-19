(*
   loops.dats — mutable cells and the two loop forms.

   ATS has two binding keywords and they are not interchangeable.  `val`
   names a *value*: it never changes, it needs no storage, and it lowers
   to an SSA register.  `var` names a *cell*: it is allocated on the
   stack, it can be the target of `:=`, and every mention of it is a load.

   A cell declared without an initializer (`var j: int`) is legal — ATS's
   type system tracks initialization and forbids reading one before it is
   written.

   `:=+` is compound assignment: `x :=+ e` means `x := x + e`.

   Both loops put their condition in a block of its own, so it is
   re-evaluated on every turn; the `for` loop additionally keeps its step
   apart from its body.  Every `alloca` is hoisted into the entry block,
   so a cell declared inside a loop costs stack space once rather than
   once per iteration.
*)

fun sum_to (n: int): int =
  let
    var i: int = 1
    var total: int = 0
    val () = while (i <= n) {
      val () = total :=+ i
      val () = i :=+ 1
    }
  in
    total
  end

fun factorial (n: int): int =
  let
    var acc: int = 1
    var k: int
    val () = for (k := 2; k <= n; k :=+ 1) acc :=* k
  in
    acc
  end

implement main0 () =
  let
    var countdown: int = 3
    val () = while (countdown > 0) {
      val () = print! (countdown, "... ")
      val () = countdown :=- 1
    }
    val () = println! ("liftoff")
  in
    println! ("sum_to(10) = ", sum_to (10), ", factorial(6) = ", factorial (6))
  end
