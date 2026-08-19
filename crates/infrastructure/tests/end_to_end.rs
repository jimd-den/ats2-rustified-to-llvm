//! # End-to-end — the pipeline they will remember
//!
//! *Literate note.*  Unit tests guard each component; these tests guard
//! the *assembly*.  One of them goes further than reading text: it hands
//! the emitted IR to `lli`, the LLVM interpreter, and checks the program
//! actually computes.  If the emitter ever produces IR that is valid
//! Rustin' but not valid LLVM, this is where it gets caught.

use std::process::Command;

use ats2_infrastructure::llvm_ir::LlvmIrEmitter;
use ats2_infrastructure::parser::Parser;

/// The canonical demo: a recursive factorial plus a `println!` main.
const DEMO: &str = "\
(* factorial, in the ATS spirit *)\
fun fact(n: int): int = if n = 0 then 1 else n * fact(n - 1)\
\
implement main0() = println!(\"fact(5) = \", fact(5))\
";

fn compile_demo() -> String {
    let program = Parser::parse(DEMO).expect("parse the demo");
    LlvmIrEmitter::emit(&program).expect("emit the demo")
}

#[test]
fn the_full_pipeline_parses_emits_and_reads_back() {
    let ir = compile_demo();
    assert!(ir.contains("define i64 @fact(i64 %n)"), "got:\n{ir}");
    assert!(ir.contains("define i32 @main()"), "got:\n{ir}");
    assert!(ir.contains("call i64 @fact(i64 5)"), "got:\n{ir}");
    assert!(ir.contains("call i32 (ptr, ...) @printf"), "got:\n{ir}");
    // The format constant carries the literal text, the %ld placeholder,
    // and the trailing newline.
    assert!(ir.contains("fact(5) = %ld\\0A\\00"), "got:\n{ir}");
}

#[test]
fn lexer_errors_surface_through_the_pipeline() {
    let program = Parser::parse("fun f(): int = \"unterminated").expect_err("should fail");
    assert_eq!(program.len(), 1);
    assert_eq!(program[0].kind(), ats2_domain::errors::ErrorKind::Lex);
}

#[test]
fn parser_errors_surface_through_the_pipeline() {
    // A `let` that never closes.  (`if ... then` without `else` used to
    // serve here, but the one-armed `if` is a legal ATS statement now.)
    let program = Parser::parse("fun f(): int = let val x = 1 in x").expect_err("should fail");
    assert_eq!(program[0].kind(), ats2_domain::errors::ErrorKind::Parse);
    assert!(program[0].message().contains("end"), "{}", program[0]);
}

#[test]
fn emitter_errors_surface_through_the_pipeline() {
    // A lambda is a closure, and a closure is not an int.  (This used to
    // fail because lambdas were unsupported outright.)
    let program = Parser::parse("fun f(x: int): int = lam (y: int) => y").expect("parse");
    let err = LlvmIrEmitter::emit(&program).expect_err("should fail");
    assert!(err.message().contains("body has type"), "{}", err);
}

/// The ultimate test: the emitted IR must *run*.  `lli` interprets the IR
/// directly (no compilation), so any structural defect in our output shows
/// up here.  Skipped when `lli` is not installed.
#[test]
fn the_emitted_ir_executes_under_lli() {
    if Command::new("lli").arg("--version").output().is_err() {
        eprintln!("skipping: lli not on PATH");
        return;
    }
    let ir = compile_demo();
    let dir = std::env::temp_dir();
    let ir_path = dir.join(format!("ats2llvm-e2e-{}.ll", std::process::id()));
    std::fs::write(&ir_path, &ir).expect("write ir");
    let out = Command::new("lli").arg(&ir_path).output().expect("run lli");
    let _ = std::fs::remove_file(&ir_path);
    assert!(out.status.success(), "lli failed:\n{}\nstderr: {}", ir, String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(stdout, "fact(5) = 120\n", "unexpected output: {stdout:?}");
}
