(*
   hello.dats — the ATS2 demo for the ats2llvm compiler foundation.

   Compile to LLVM IR, or all the way to a runnable binary:

       cargo run -- examples/hello.dats --ir /tmp/hello.ll
       cargo run -- examples/hello.dats --bin /tmp/hello && /tmp/hello
*)

(* a recursive function, in the ATS spirit *)
fun fact(n: int): int = if n = 0 then 1 else n * fact(n - 1)

(* the program entry point *)
implement main0() = println!("fact(5) = ", fact(5))
