(*
   closures.dats — functions that carry part of their scope with them.

   Lambda *lifting* already handles a named nested function: whatever it
   reads from around it becomes an extra parameter, and the call sites are
   rewritten to pass it.  A `lam` cannot be treated that way, because it
   may outlive the scope it was written in and its callers have no idea
   what it captured.

   So a closure is a *record*: the first word is the lifted body, and the
   rest are the values it read from around it, copied in when the closure
   was built.  Calling one loads the code out of the record and jumps
   through it, handing the record back as the environment.  That is the
   price of the feature — one load and an indirect call — and it is paid
   only where a closure is actually used.

   A function type like `(int) -> int` is therefore a closure type, and
   `f(1)(2)` has two readings: a *curried* call when `f` takes two
   parameters, and an application of the result when `f` returns a
   closure.  Which one it is depends on how many parameters `f` actually
   has, so the spine is flattened only when the count comes out right.

   The `=<cloptr1>` on a lambda says how the closure should be allocated.
   The arena settles that for us, so the annotation is read and dropped.
*)

fun adder (m: int): (int) -> int = lam (n: int): int => m + n

fun scaler (k: int) = lam (n: int): int =<cloptr1> k * n

(* the closure is recursive through the function that builds it *)
fun countdown (m: int) = lam (n: int): int =<cloptr1>
  if m <= 0 then n else countdown(m - 1)(n + 1)

(* a closure passed as an argument, and applied there *)
fun twice (f: (int) -> int, x: int): int = f(f(x))

(* currying without closures still flattens into one direct call *)
fun plus (a: int) (b: int): int = a + b

implement main0 () =
  let
    val add10 = adder(10)
    val triple = scaler(3)
  in
    println! ("adder(10)(5)   = ", add10(5), "\n",
              "scaler(3)(7)   = ", triple(7), "\n",
              "countdown(4)(0)= ", countdown(4)(0), "\n",
              "twice(add10,1) = ", twice(add10, 1), "\n",
              "plus(3)(4)     = ", plus(3)(4))
  end
