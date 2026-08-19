(*
   files.dats — streams, and reading the command line.

   A `FILEref` is C's `FILE *`.  The three standard streams are kept in
   libc *globals*, so naming one costs a load; `fprint!`/`fprintln!` take
   the stream as their first argument and lower to `fprintf`.

   `fileref_getc` yields the subset's `int`, widened from C's with the
   sign kept so that EOF stays -1 rather than becoming four billion.

   `main` (as opposed to `main0`) hands its `int` result back as the
   process's exit code, and `argv` may be indexed for the arguments.
*)

fun echo_upto (out: FILEref, n: int): void =
  if n > 0 then
    let
      val () = fprintln! (out, "  line ", n)
    in
      echo_upto (out, n - 1)
    end

implement main (argc, argv): int =
  let
    val out = stdout_ref
    // `argv` is indexable; `argv[0]` is deliberately not printed here,
    // since the program's own path depends on where it was built.
    val () = fprintln! (out, "argc = ", argc)
    val () = fprintln! (out, "named a file = ", argc >= 2)
    val () = echo_upto (out, 3)
    val () = prerrln! ("(this line went to stderr)")
  in
    0
  end
