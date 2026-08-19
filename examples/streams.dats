(*
   streams.dats — the `print` family.

   ATS spells the destination and the trailing newline into the macro's
   name: `print!`/`println!` go to standard output, `prerr!`/`prerrln!` to
   standard error, and the `f`-prefixed forms name the stream as their
   first argument.  Whatever the form, the arguments collapse into a
   single synthesized format string and one `printf`/`fprintf` call.

   String literals become format text; `int`, `bool`, and `string` values
   become the placeholder their type calls for.
*)

fun greet (who: string): string = who

implement main0 () = {
  val () = print! ("no newline here; ")
  val () = println! ("...and now one")
  val () = println! ("a string: ", greet ("world"))
  val () = println! ("mixed: ", 42, " ", true, " ", greet ("ok"))
  val () = fprintln! (stdout_ref, "explicitly to stdout")
  val () = prerrln! ("this line goes to stderr")
}
