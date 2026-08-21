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
    assert!(
        out.status.success(),
        "lli failed:\n{}\nstderr: {}",
        ir,
        String::from_utf8_lossy(&out.stderr)
    );
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
    uc.execute(source, &ir, &bin)
        .expect("the program should build");

    // The C was written where the IR is, because that is where the other
    // half of the program already is.
    assert!(
        ir.with_extension("c").exists(),
        "the C block was not written out"
    );

    let out = Command::new(&bin).output().expect("run the linked program");
    assert_eq!(
        String::from_utf8_lossy(&out.stdout).trim(),
        "triple 14 = 42"
    );
}

#[test]
fn a_proof_reaches_the_emitter_and_leaves_no_trace() {
    // A `prfun` is a definition now, so it arrives at the emitter as one
    // — and a proof occupies no storage and runs at no time.  Emitting
    // it would put a function in the object file whose body is a
    // derivation, which is not code.
    let source = "\
dataprop FACT (int, int) = | FACTbas (0, 1) of () \
prfun base (): FACT(0, 1) = FACTbas () \
implement main0() = println!(\"ok\")\
";
    let program = Parser::parse(source).expect("parse");
    let ir = LlvmIrEmitter::emit(&program).expect("emit");
    assert!(!ir.contains("@base"), "the proof was emitted:\n{ir}");
    assert!(ir.contains("define i32 @main()"), "got:\n{ir}");
}

#[test]
fn a_program_written_in_three_files_builds_and_runs() {
    // The point of `staload`.  `main.dats` names `math.sats` for the
    // declaration and `math.dats` for the definition, and `math.dats`
    // reaches one directory down for a helper of its own — so the walk
    // has to resolve relative to the file that asked rather than to the
    // root, and has to fold `math.sats` in once even though two files
    // named it.
    //
    // It lives here rather than in `examples/` for the same reason the
    // inline-C test does: the suite there hands one `.dats` to `lli`,
    // and a program in three files is one the *front end* has to
    // assemble before there is any IR to interpret.
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    let dir = std::env::temp_dir().join(format!("ats2llvm-modules-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("lib")).expect("a place to work");

    std::fs::write(
        dir.join("lib/double.dats"),
        "fun double (n: int): int = n + n\n",
    )
    .expect("write lib/double.dats");
    std::fs::write(
        dir.join("math.sats"),
        "extern fun quadruple (n: int): int\n",
    )
    .expect("write math.sats");
    std::fs::write(
        dir.join("math.dats"),
        "staload \"math.sats\"\n\
         staload \"lib/double.dats\"\n\
         implement quadruple (n) = double (double (n))\n",
    )
    .expect("write math.dats");
    let main = dir.join("main.dats");
    std::fs::write(
        &main,
        "staload \"math.sats\"\n\
         staload _ = \"math.dats\"\n\
         implement main0 () = println! (\"quadruple 7 = \", quadruple (7))\n",
    )
    .expect("write main.dats");

    use ats2_application::use_cases::CompileExecutableUseCase;
    use ats2_infrastructure::io::FileOutput;
    use ats2_infrastructure::sources::FileSources;
    use ats2_infrastructure::toolchain::ClangToolchain;

    let source = std::fs::read_to_string(&main).expect("read main.dats");
    let ir = dir.join("main.ll");
    let bin = dir.join("main");
    let uc = CompileExecutableUseCase::new(Parser, LlvmIrEmitter, ClangToolchain, FileOutput)
        .loading(FileSources::at(&main));
    uc.execute(&source, &ir, &bin)
        .expect("the program should build");

    let out = Command::new(&bin).output().expect("run the linked program");
    assert_eq!(
        String::from_utf8_lossy(&out.stdout).trim(),
        "quadruple 7 = 28"
    );

    // `math.sats` was named by both files and defined `quadruple` once.
    // Twice would be a duplicate symbol, and the link above would have
    // said so — but the IR is where it reads plainly.
    let text = std::fs::read_to_string(&ir).expect("read the IR");
    assert_eq!(
        text.matches("define i64 @quadruple(").count(),
        1,
        "got:\n{text}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_staload_naming_no_file_is_refused_rather_than_skipped() {
    // The old behaviour was to skip every `staload`, which turned a
    // misspelt filename into a missing symbol at link time named after
    // something the user never typed.
    use ats2_application::use_cases::CompileToIrUseCase;
    use ats2_infrastructure::sources::FileSources;

    let dir = std::env::temp_dir().join(format!("ats2llvm-missing-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a place to work");
    let main = dir.join("main.dats");
    let source = "staload \"hlper.sats\"\nimplement main0 () = ()\n";
    std::fs::write(&main, source).expect("write main.dats");

    let uc = CompileToIrUseCase::new(Parser, LlvmIrEmitter).loading(FileSources::at(&main));
    let errs = uc.execute(source).expect_err("should fail");
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].message().contains("hlper.sats"), "{}", errs[0]);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_staload_into_the_ats_distribution_is_still_answered_by_the_prelude() {
    // Every `staload` in the corpus names something under `prelude/` or
    // `libats/`.  Those must stay silent with a loader wired in, or
    // multi-file support arrives by breaking all 36 samples.
    use ats2_application::use_cases::CompileToIrUseCase;
    use ats2_infrastructure::sources::FileSources;

    let main = std::env::temp_dir().join("ats2llvm-dist-main.dats");
    let source = "staload \"prelude/DATS/integer.dats\"\n\
                  staload UN = \"prelude/SATS/unsafe.sats\"\n\
                  staload _ = \"libats/ML/DATS/list0.dats\"\n\
                  implement main0 () = println! (\"ok\")\n";
    let uc = CompileToIrUseCase::new(Parser, LlvmIrEmitter).loading(FileSources::at(&main));
    let ir = uc.execute(source).expect("the program should compile");
    assert!(ir.contains("define i32 @main()"), "got:\n{ir}");
}

#[test]
fn an_extval_reaches_a_c_function() {
    // `$extval(T, "c_fn", args...)` is ATS's bridge to C.  Lowering it
    // means declaring the C function and asking the host toolchain to
    // link it — libc's `strlen`, here, which clang links by default.
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    let dir = std::env::temp_dir().join(format!("ats2llvm-extval-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a place to work");
    let source =
        "implement main0 () = println! (\"strlen(hi) = \", $extval(int, \"strlen\", \"hi\"))";

    use ats2_application::use_cases::CompileExecutableUseCase;
    use ats2_infrastructure::io::FileOutput;
    use ats2_infrastructure::toolchain::ClangToolchain;

    let ir = dir.join("ext.ll");
    let bin = dir.join("ext");
    let uc = CompileExecutableUseCase::new(Parser, LlvmIrEmitter, ClangToolchain, FileOutput);
    uc.execute(source, &ir, &bin)
        .expect("the program should build");

    let out = Command::new(&bin).output().expect("run the linked program");
    assert_eq!(
        String::from_utf8_lossy(&out.stdout).trim(),
        "strlen(hi) = 2"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn an_extfcall_lowers_to_a_call() {
    // `$extfcall(T, "f", args...)` is the same reach into C, through a
    // function pointer.  The two spellings lower alike today; the pointer
    // indirection is a refinement of the C side, not of the call.
    let source = "fun f (): int = $extfcall(int, \"atoi\", \"7\")";
    let program = Parser::parse(source).expect("parse");
    let ir = LlvmIrEmitter::emit(&program).expect("emit");
    assert!(ir.contains("declare i64 @atoi"), "got:\n{ir}");
    assert!(ir.contains("call i64 @atoi"), "got:\n{ir}");
}

#[test]
fn an_extval_reads_a_c_global() {
    // `$extval(T, "CONST")` with no arguments names a C *value* — a
    // global the host side defines — rather than a function to call.  It
    // is declared and read, so a name the source never defined still
    // answers at link time.
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    let dir = std::env::temp_dir().join(format!("ats2llvm-extval-global-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a place to work");
    // ATS `int` is a machine word, so the C side names a `long`.
    let source = "%{^\nlong the_answer = 42;\n%}\n\
                  implement main0 () = println! (\"answer = \", $extval(int, \"the_answer\"))";

    use ats2_application::use_cases::CompileExecutableUseCase;
    use ats2_infrastructure::io::FileOutput;
    use ats2_infrastructure::toolchain::ClangToolchain;

    let ir = dir.join("g.ll");
    let bin = dir.join("g");
    let uc = CompileExecutableUseCase::new(Parser, LlvmIrEmitter, ClangToolchain, FileOutput);
    uc.execute(source, &ir, &bin)
        .expect("the program should build");

    let out = Command::new(&bin).output().expect("run the linked program");
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "answer = 42");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn an_extval_reads_a_c_macro() {
    // `$extval(int, "MACRO")` names a C macro, which has no symbol of its
    // own.  The compiler generates a shim beside the program's C — where
    // the `#include` that defines the macro lives — and reads that.
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    let dir = std::env::temp_dir().join(format!("ats2llvm-extval-macro-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a place to work");
    let source = "%{^\n#define THE_ANSWER 42\n%}\n\
                  implement main0 () = println! (\"answer = \", $extval(int, \"THE_ANSWER\"))";

    use ats2_application::use_cases::CompileExecutableUseCase;
    use ats2_infrastructure::io::FileOutput;
    use ats2_infrastructure::toolchain::ClangToolchain;

    let ir = dir.join("m.ll");
    let bin = dir.join("m");
    let uc = CompileExecutableUseCase::new(Parser, LlvmIrEmitter, ClangToolchain, FileOutput);
    uc.execute(source, &ir, &bin)
        .expect("the program should build");

    let out = Command::new(&bin).output().expect("run the linked program");
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "answer = 42");
    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Exceptions, end to end.
//
// A `try` must catch what a `$raise` throws — in the same frame, from a
// deeper frame, or through a handler that raises again.  These link
// through clang because `setjmp`/`longjmp` are libc, and run the binary,
// because an exception is only handled when the program says so on the
// way out.

use std::sync::atomic::{AtomicUsize, Ordering};
static EXN_WORKDIR: AtomicUsize = AtomicUsize::new(0);

/// Build `source` with the full pipeline and run the resulting binary.
fn build_and_run(source: &str) -> std::process::Output {
    use ats2_application::use_cases::CompileExecutableUseCase;
    use ats2_infrastructure::io::FileOutput;
    use ats2_infrastructure::toolchain::ClangToolchain;

    let n = EXN_WORKDIR.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "ats2llvm-exn-{}-{}",
        std::process::id(),
        n
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a place to work");
    let ir = dir.join("exn.ll");
    let bin = dir.join("exn");
    let uc = CompileExecutableUseCase::new(Parser, LlvmIrEmitter, ClangToolchain, FileOutput);
    uc.execute(source, &ir, &bin)
        .expect("the program should build");
    let out = Command::new(&bin).output().expect("run the linked program");
    let _ = std::fs::remove_dir_all(&dir);
    out
}

/// As `build_and_run`, but a program that loops forever must fail the
/// test instead of hanging it: a raise inside a handler that re-enters
/// its own `try` is exactly that program.
fn build_and_run_timed(source: &str, secs: u64) -> std::process::Output {
    use ats2_application::use_cases::CompileExecutableUseCase;
    use ats2_infrastructure::io::FileOutput;
    use ats2_infrastructure::toolchain::ClangToolchain;
    use std::io::Read;
    use std::process::Stdio;
    use std::time::Instant;

    let n = EXN_WORKDIR.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "ats2llvm-exn-{}-{}",
        std::process::id(),
        n
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a place to work");
    let ir = dir.join("exn.ll");
    let bin = dir.join("exn");
    let uc = CompileExecutableUseCase::new(Parser, LlvmIrEmitter, ClangToolchain, FileOutput);
    uc.execute(source, &ir, &bin)
        .expect("the program should build");

    let mut child = Command::new(&bin)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run the linked program");
    let start = Instant::now();
    loop {
        if let Some(status) = child.try_wait().expect("wait for the program") {
            let mut stdout = String::new();
            let mut stderr = String::new();
            child
                .stdout
                .take()
                .expect("stdout")
                .read_to_string(&mut stdout)
                .expect("read stdout");
            child
                .stderr
                .take()
                .expect("stderr")
                .read_to_string(&mut stderr)
                .expect("read stderr");
            let _ = std::fs::remove_dir_all(&dir);
            return std::process::Output {
                status,
                stdout: stdout.into_bytes(),
                stderr: stderr.into_bytes(),
            };
        }
        if start.elapsed().as_secs() > secs {
            let _ = child.kill();
            let _ = child.wait();
            panic!(
                "the program did not finish within {secs}s; a raise is re-entering its own try"
            );
        }
        std::thread::sleep(std::time::Duration::from_millis(50));
    }
}

#[test]
fn a_try_catches_what_a_raise_throws() {
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    let out = build_and_run(
        "exception E
         implement main0 () = let
           val ans = try $raise E with ~E () => 42
         in println! (\"ans = \", ans) end",
    );
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "ans = 42");
}

#[test]
fn a_raise_carries_its_payload_to_the_handler() {
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    let out = build_and_run(
        "exception Found of int
         implement main0 () = let
           val ans = try $raise Found(7) with ~Found(x) => x + 1
         in println! (\"ans = \", ans) end",
    );
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "ans = 8");
}

#[test]
fn a_void_try_catches_and_the_program_ends_normally() {
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    // `main0` is void, and so are both arms of the try: the merge of a
    // void try is where the ret lands.  This is the commonest shape a
    // catching program has, and it used to be the easy one to get wrong.
    let out = build_and_run(
        "exception E
         implement main0 () = try $raise E with ~E () => println! (\"caught\")",
    );
    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "caught");
}

#[test]
fn a_handler_that_raises_never_returns_and_needs_no_merge_value() {
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    // The handler's arm type is `never`: it raises rather than returning
    // a value, so it cannot disagree with the body's type.  The try's
    // merge has one less incoming value because of it.
    let out = build_and_run(
        "exception E
         implement main0 () = let
           val x = try 5 with ~E () => $raise E
         in println! (\"x = \", x) end",
    );
    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "x = 5");
}

#[test]
fn a_try_body_that_completes_keeps_its_value() {
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    let out = build_and_run(
        "exception E
         implement main0 () = let
           val ans = try 5 with ~E () => 0
         in println! (\"ans = \", ans) end",
    );
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "ans = 5");
}

#[test]
fn an_uncaught_raise_names_the_exception_and_stops() {
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    let out = build_and_run("exception E implement main0 () = $raise E");
    assert!(
        !out.status.success(),
        "an uncaught raise must stop the program"
    );
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("uncaught E"), "stderr was: {err}");
}

#[test]
fn what_no_handler_matches_is_raised_again_one_frame_up() {
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    let out = build_and_run(
        "exception A and B
         implement main0 () = let
           val ans = try (try $raise A with ~B () => 0) with ~A () => 1
         in println! (\"ans = \", ans) end",
    );
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "ans = 1");
}

#[test]
fn a_handler_that_raises_propagates_outward_without_recatching() {
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    // The inner handler raises the very exception it just caught.  Real
    // ATS sends it to the *outer* try; a lowering that re-enters the
    // inner one would loop forever, which the timeout would report.
    let out = build_and_run_timed(
        "exception A
         implement main0 () = let
           val ans = try (try $raise A with ~A () => $raise A) with ~A () => 99
         in println! (\"ans = \", ans) end",
        5,
    );
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "ans = 99");
}

#[test]
fn a_handler_that_raises_a_different_exception_reaches_the_outer_try() {
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    let out = build_and_run(
        "exception A and B
         implement main0 () = let
           val ans = try (try $raise A with ~A () => $raise B) with ~B () => 7
         in println! (\"ans = \", ans) end",
    );
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "ans = 7");
}

#[test]
fn a_payload_survives_a_reraise_to_the_outer_try() {
    if !clang_available() {
        eprintln!("skipping: no clang on PATH");
        return;
    }
    let out = build_and_run(
        "exception A of int and B
         implement main0 () = let
           val ans = try (try $raise A(5) with ~B () => 0) with ~A(x) => x
         in println! (\"ans = \", ans) end",
    );
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "ans = 5");
}
