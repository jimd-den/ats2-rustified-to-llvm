//! # CLI smoke tests — the binary, from the outside
//!
//! *Literate note.*  These tests drive the actual `ats2llvm` executable as
//! a black box: exit codes, files produced, and — when the host toolchain
//! is present — a binary that runs and prints `fact(5) = 120`.  This is
//! the outermost proof that the whole architecture composes.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

const EXE: &str = env!("CARGO_BIN_EXE_ats2llvm");

static COUNTER: AtomicUsize = AtomicUsize::new(0);

fn temp_file(tag: &str, ext: &str) -> PathBuf {
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "ats2llvm-cli-{tag}-{}-{n}.{ext}",
        std::process::id()
    ))
}

fn write_source() -> PathBuf {
    let src = "(* our demo *)\n\nfun fact(n: int): int = if n = 0 then 1 else n * fact(n - 1)\n\nimplement main0() = println!(\"fact(5) = \", fact(5))\n";
    let path = temp_file("src", "dats");
    std::fs::write(&path, src).expect("write source");
    path
}

#[test]
fn compiles_source_to_an_ir_file() {
    let src = write_source();
    let ir = temp_file("out", "ll");
    let status = Command::new(EXE)
        .arg(&src)
        .arg("--ir")
        .arg(&ir)
        .status()
        .expect("run ats2llvm");
    assert!(status.success(), "exit {status}");
    let text = std::fs::read_to_string(&ir).expect("read ir");
    assert!(text.contains("define i64 @fact(i64 %n)"), "got:\n{text}");
    assert!(text.contains("define i32 @main()"), "got:\n{text}");
    let _ = std::fs::remove_file(&src);
    let _ = std::fs::remove_file(&ir);
}

#[test]
fn syntax_errors_exit_nonzero_and_report_the_location() {
    let src = temp_file("bad", "dats");
    std::fs::write(&src, "fun f(x) = x\n").expect("write");
    let out = Command::new(EXE).arg(&src).output().expect("run");
    assert_eq!(out.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("parse error"), "stderr: {stderr}");
    assert!(stderr.contains("1:"), "stderr: {stderr}");
    let _ = std::fs::remove_file(&src);
}

#[test]
fn usage_errors_exit_two() {
    let out = Command::new(EXE).output().expect("run");
    assert_eq!(out.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("usage"), "stderr: {stderr}");
}

fn clang_available() -> bool {
    Command::new("clang").arg("--version").output().is_ok()
}

/// The full journey: .dats -> IR -> executable -> run.
#[test]
fn builds_and_runs_a_real_binary() {
    if !clang_available() {
        eprintln!("skipping: clang not on PATH");
        return;
    }
    let src = write_source();
    let ir = temp_file("out", "ll");
    let bin = temp_file("prog", "");
    let status = Command::new(EXE)
        .arg(&src)
        .arg("--ir")
        .arg(&ir)
        .arg("--bin")
        .arg(&bin)
        .status()
        .expect("run ats2llvm");
    assert!(status.success(), "exit {status}");
    assert!(ir.exists(), "IR file missing");
    assert!(bin.exists(), "binary missing");
    let out = Command::new(&bin).output().expect("run the binary");
    assert!(out.status.success(), "binary exited {out:?}");
    assert_eq!(String::from_utf8_lossy(&out.stdout), "fact(5) = 120\n");
    let _ = std::fs::remove_file(&src);
    let _ = std::fs::remove_file(&ir);
    let _ = std::fs::remove_file(&bin);
}
