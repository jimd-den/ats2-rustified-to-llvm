(*
   templates.dats — one definition, many functions.

   ATS writes a generic function as a *template*: `{a:t@ype}` introduces a
   hole where a type will go.  A declaration states the shape and an
   `implement` fills it in, which is why the definition can leave its
   parameters unannotated — the types were already given above.

   LLVM has no such hole, so before emission each template becomes one
   ordinary function per type it is actually used at.  Nothing is emitted
   for a template that is never instantiated, and asking for the same
   instantiation twice produces one function, not two.  The instances are
   named by mangling the type into the symbol — `ident<int>` becomes
   `ident$int` — and a `$` cannot collide with a name the source could
   have written.

   The instantiation has to be written out.  ATS infers it; this compiler
   does not, and would rather say so than guess.
*)

extern fun{a:t@ype} ident (x: a): a
implement{a} ident (x) = x

extern fun{a:t@ype} thrice (x: a): a
implement{a} thrice (x) = ident<a>(ident<a>(ident<a>(x)))

extern fun{a:t@ype} count_down (n: int, x: a): int
implement{a} count_down (n, x) =
  if n <= 0 then 0 else 1 + count_down<a>(n - 1, x)

implement main0 () = {
  val () = println! ("ident<int>(42)      = ", ident<int>(42))
  val () = println! ("ident<string>(\"hi\") = ", ident<string>("hi"))
  val () = println! ("ident<bool>(true)   = ", ident<bool>(true))
  val () = println! ("thrice<int>(7)      = ", thrice<int>(7))
  val () = println! ("count_down<string>  = ", count_down<string>(4, "x"))
}
