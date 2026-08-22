//! # Runner adapter — executing LLVM IR on the host system
//!
//! *Literate note.*  The REPL evaluates expressions interactively. This
//! adapter implements [`RunnerPort`] by executing generated LLVM IR:
//! it tries the direct LLVM interpreter (`lli`) first for zero-overhead
//! evaluation, and falls back to compiling and linking via `clang` when
//! needed.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use ats2_application::ports::{ExecutionResult, RunnerPort};

static RUN_COUNTER: AtomicU64 = AtomicU64::new(0);

fn temp_ir_path() -> PathBuf {
    let count = RUN_COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!("ats2repl-{}-{}.ll", std::process::id(), count))
}

fn temp_bin_path() -> PathBuf {
    let count = RUN_COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!("ats2repl-bin-{}-{}", std::process::id(), count))
}

/// The default runner on the host system.
#[derive(Debug, Default, Clone, Copy)]
pub struct HostRunner;

impl RunnerPort for HostRunner {
    fn run_ir(&self, ir: &str) -> Result<ExecutionResult, String> {
        // Attempt 1: Direct interpretation via `lli`
        if let Ok(true) = lli_available() {
            let ir_file = temp_ir_path();
            if let Err(e) = std::fs::write(&ir_file, ir) {
                return Err(format!("cannot write temporary IR file: {e}"));
            }

            let result = Command::new("lli").arg(&ir_file).output();
            let _ = std::fs::remove_file(&ir_file);

            if let Ok(out) = result {
                if out.status.success() {
                    return Ok(ExecutionResult {
                        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
                        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
                        exit_code: out.status.code().unwrap_or(0),
                        success: true,
                    });
                } else if !out.stderr.is_empty() {
                    let err_msg = String::from_utf8_lossy(&out.stderr);
                    // If lli had a genuine runtime error or missing external symbol,
                    // we can report it or try clang fallback.
                    if !err_msg.contains("LLVM ERROR") && !err_msg.contains("symbol not found") {
                        return Ok(ExecutionResult {
                            stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
                            stderr: err_msg.into_owned(),
                            exit_code: out.status.code().unwrap_or(1),
                            success: false,
                        });
                    }
                }
            }
        }

        // Attempt 2: Compile & link with clang, then execute binary
        let ir_file = temp_ir_path();
        let bin_file = temp_bin_path();

        if let Err(e) = std::fs::write(&ir_file, ir) {
            return Err(format!("cannot write temporary IR file: {e}"));
        }

        let clang_res = Command::new("clang")
            .arg(&ir_file)
            .arg("-o")
            .arg(&bin_file)
            .output();

        let _ = std::fs::remove_file(&ir_file);

        match clang_res {
            Ok(c_out) if c_out.status.success() => {
                let run_res = Command::new(&bin_file).output();
                let _ = std::fs::remove_file(&bin_file);

                match run_res {
                    Ok(out) => Ok(ExecutionResult {
                        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
                        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
                        exit_code: out.status.code().unwrap_or(0),
                        success: out.status.success(),
                    }),
                    Err(e) => Err(format!("failed to execute compiled binary: {e}")),
                }
            }
            Ok(c_out) => {
                let _ = std::fs::remove_file(&bin_file);
                Err(format!(
                    "clang linking failed: {}",
                    String::from_utf8_lossy(&c_out.stderr)
                ))
            }
            Err(e) => {
                let _ = std::fs::remove_file(&bin_file);
                Err(format!("cannot invoke clang or lli: {e}"))
            }
        }
    }
}

fn lli_available() -> Result<bool, ()> {
    Command::new("lli")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .map_err(|_| ())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn host_runner_executes_simple_main() {
        let runner = HostRunner;
        let ir = "\
@.str = private unnamed_addr constant [15 x i8] c\"hello from ir\\0A\\00\", align 1
declare i32 @printf(ptr, ...)

define i32 @main() {
entry:
  %0 = call i32 (ptr, ...) @printf(ptr @.str)
  ret i32 0
}
";
        let res = runner.run_ir(ir);
        if let Ok(out) = res {
            assert_eq!(out.stdout, "hello from ir\n");
            assert!(out.success);
        }
    }
}
