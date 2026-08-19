(*
   statements.dats — void, the one-armed `if`, and `assertloc`.

   Not every ATS expression produces a value.  `println!` has type void, a
   `fun` may be annotated `: void`, `let ... in end` evaluates to unit, and
   `if c then e` without an `else` is a statement whose missing arm is
   unit.  `assertloc` is not a call at all: it lowers to a branch that
   leaves through `exit(1)` when the condition is false, so the success
   path costs one well-predicted jump.

   `#define` names a constant, which is substituted at each use rather
   than stored anywhere.
*)

#define LIMIT 5

fun announce (n: int): void =
  if n > LIMIT then println! (n, " is over the limit")

fun clamp (n: int): int = if n > LIMIT then LIMIT else n

implement main0 () =
  let
    val () = announce (3)
    val () = announce (9)
    val () = assertloc (clamp (100) = LIMIT)
    val () = assertloc (clamp (2) = 2)
    val () = println! ("clamped: ", clamp (100), " and ", clamp (2))
  in
  end
