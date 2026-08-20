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

/// Whether the host has a C toolchain to link with.
fn clang_available() -> bool {
    Command::new("clang").arg("--version").output().is_ok()
}

#[test]
fn a_program_that_brought_its_own_c_is_compiled_with_it() {
    // `%{ ... %}` is the body of some `extern fun` declared beside it.
    // The block used to be thrown away at the lexer, so a program like
    // this compiled and then failed to link, naming a symbol whose
    // definition had been discarded three stages earlier.  Now the C is
    // written next to the IR and both go to the toolchain together.
    //
    // This lives here rather than in `examples/` because the suite there
    // runs each sample under `lli`, which sees the IR alone: a program
    // with foreign code is one that has to be *linked* to mean anything.
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    let dir = std::env::temp_dir().join("ats2llvm-inline-c");
    std::fs::create_dir_all(&dir).expect("a place to work");
    let source = "%{^\nint triple (int n) { return 3 * n; }\n%}\n\
                  extern fun triple (n: int): int = \"ext#triple\"\n\
                  implement main0 () = println! (\"triple 14 = \", triple (14))";

    use ats2_application::use_cases::CompileExecutableUseCase;
    use ats2_infrastructure::io::FileOutput;
    use ats2_infrastructure::toolchain::ClangToolchain;

    let ir = dir.join("foreign.ll");
    let bin = dir.join("foreign");
    let uc = CompileExecutableUseCase::new(Parser, LlvmIrEmitter, ClangToolchain, FileOutput);
    uc.execute(source, &ir, &bin).expect("the program should build");

    // The C was written where the IR is, because that is where the other
    // half of the program already is.
    assert!(ir.with_extension("c").exists(), "the C block was not written out");

    let out = Command::new(&bin).output().expect("run the linked program");
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "triple 14 = 42");
}
