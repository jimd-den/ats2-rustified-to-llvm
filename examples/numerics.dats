(*
   numerics.dats — doubles, and code that is generic over the number type.

   `double` is a type of its own, not a wide int: it has its own
   arithmetic (`fadd`, `fmul`) and its own comparisons (the *ordered*
   predicates, so that anything involving NaN is false).  Mixing an `int`
   and a `double` is refused, exactly as ATS refuses it.

   Which raises the question this file is really about: how do you write
   `x * f(x - 1)` once, when `x` is an `int` and the result may be either?

   ATS's answer is three declarations working together.  `macdef` names an
   expression — here a *template instance*, so `gint` means "the number
   one, at whatever type this instantiation is for".  `overload` names the
   function to fall back on when an operator's operands do not fit it, and
   the generic shims it points at widen the narrower side.  Neither is a
   silent promotion: ordinary arithmetic still refuses to mix the two, and
   the widening happens only where the program asked for it.

   The prelude's list functions are here too.  They are written in ATS in
   the prelude and pulled in only when something calls them, so a program
   that never mentions a list pays nothing for one.
*)

extern fun{a:t@ype} gfact (x: int): a
implement{a} gfact (x) =
  let
    macdef gint = gnumber_int<a>
    overload * with gmul_int_val
  in
    if x > 0 then x * gfact<a>(x - 1) else gint(1)
  end

fun area (r: double): double = 3.14159 * r * r

fun steeper (a: double, b: double): bool = a > b

fun words (): list0(string) = cons("alpha", cons("beta", cons("gamma", nil())))

implement main0 () =
  let
    val ws = words()
  in
    println! ("gfact<int>(12)    = ", gfact<int>(12), "\n",
              "gfact<double>(12) = ", gfact<double>(12), "\n",
              "area(2.0)         = ", area(2.0), "\n",
              "2.5 > 1.5         = ", steeper(2.5, 1.5), "\n",
              "length            = ", list0_length(ws), "\n",
              "is_nil            = ", list0_is_nil(ws), "\n",
              "first isnot empty = ", string_isnot_empty("alpha"))
  end
