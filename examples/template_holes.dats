//
// Template holes: the parts of a library routine its caller supplies.
//
// `array_foreach$fwork` is not a function — it is inlined where the
// routine is used, which is what makes `env := ...` inside it write the
// caller's own cell.  That by-reference behaviour is the library's
// signature, and a call could not deliver it.
//
fun product (n: int): int = let
  typedef tenv = int
  implement array_foreach$fwork<int><tenv> (x, env) = env := env * (x+1)
  val A = arrayptr_make_intrange (0, n)
  var env: tenv = 1
  val _ = arrayptr_foreach_env<int><tenv> (A, n, env)
  val () = arrayptr_free (A)
in
  env
end

fun digits (str: string): int = let
  var env: int = 0
  implement string_foreach$cont (c, env) = isdigit (c)
  implement string_foreach$fwork<int> (c, env) = env := 10 * env + (c - '0')
  val _ = string_foreach_env<int> (str, env)
in
  env
end

implement main0 () = println! (product (5), " ", digits ("2718z"))
