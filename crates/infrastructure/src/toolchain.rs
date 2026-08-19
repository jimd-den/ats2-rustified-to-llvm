//! # Toolchain adapter — the host LLVM toolchain, through a port
//!
//! *Literate note.*  Our emitter writes textual LLVM IR; something else
//! must turn it into a runnable binary.  That something is the host
//! toolchain: `clang` (which is itself a thin LLVM driver) lowers and
//! links the IR.  This adapter shells out with `std::process::Command` —
//! the very first place the compiler touches the outside world's
//! *processes*.  The heavy lifting (optimization levels, target
//! selection) is delegated to clang; our job is only to pass the IR file
//! and the output path through the port contract.
//!
//! The toolchain is the only component whose tests depend on the
//! environment: when `clang` is absent, the link test *skips* politely
//! instead of failing.

use std::path::Path;
use std::process::Command;

use ats2_application::ports::ToolchainPort;

/// Links LLVM IR to an executable via `clang`.
pub struct ClangToolchain;

impl ToolchainPort for ClangToolchain {
    fn link(&self, ir_path: &Path, output: &Path) -> Result<(), String> {
        let result = Command::new("clang")
            .arg(ir_path)
            .arg("-o")
            .arg(output)
            .output()
            .map_err(|e| format!("cannot run clang: {e}"))?;
        if result.status.success() {
            Ok(())
        } else {
            let stderr = String::from_utf8_lossy(&result.stderr);
            let tail = stderr.lines().rev().take(3).collect::<Vec<_>>().join(" | ");
            Err(format!("clang exited with {}: {tail}", result.status))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    fn temp_path(tag: &str, ext: &str) -> std::path::PathBuf {
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        std::env::temp_dir().join(format!("ats2llvm-clang-test-{tag}-{}-{}.{ext}", std::process::id(), n))
    }

    fn clang_available() -> bool {
        Command::new("clang").arg("--version").output().is_ok()
    }

    #[test]
    fn links_a_trivial_ir_module_into_an_executable() {
        if !clang_available() {
            eprintln!("skipping: clang not on PATH");
            return;
        }
        let ir_path = temp_path("in", "ll");
        let out_path = temp_path("out", "");
        std::fs::write(&ir_path, "define i32 @main() {\n  ret i32 7\n}\n").expect("write ir");
        let result = ClangToolchain.link(&ir_path, &out_path);
        assert_eq!(result, Ok(()));
        assert!(out_path.exists(), "output executable missing");
        let _ = std::fs::remove_file(&ir_path);
        let _ = std::fs::remove_file(&out_path);
    }

    #[test]
    fn reports_toolchain_failures_as_strings() {
        if !clang_available() {
            eprintln!("skipping: clang not on PATH");
            return;
        }
        // Deliberately broken IR must not panic — just a string error.
        let broken = temp_path("bad", "ll");
        let out = temp_path("badout", "");
        std::fs::write(&broken, "definitely not IR").expect("write");
        let err = ClangToolchain.link(&broken, &out).expect_err("should fail");
        assert!(!err.is_empty());
        let _ = std::fs::remove_file(&broken);
    }
}
