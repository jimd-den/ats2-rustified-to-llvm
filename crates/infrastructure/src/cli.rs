//! # The CLI controller — the outermost ring
//!
//! *Literate note.*  This module owns exactly two things: the *shape* of
//! the command line (`CliArgs`, parsed purely) and the *wiring* that turns
//! OS arguments into use-case invocations (`run`).  Every decision about
//! *what* to do belongs to the application layer below; every mechanism —
//! reading the source file, writing IR, running clang, printing errors —
//! is reached through ports and adapters.  The controller is dumb on
//! purpose: it converts strings into a request, hands the request down,
//! and maps the outcome to a process exit code.
//!
//! Exit codes: 0 = success, 1 = compile/target failure, 2 = usage error.

use std::path::PathBuf;

use ats2_application::checking::Strictness;
use ats2_application::use_cases::{CompileExecutableUseCase, CompileToIrUseCase};

use crate::diagnostics::StderrDiagnostics;
use crate::io::FileOutput;
use crate::llvm_ir::LlvmIrEmitter;
use crate::parser::Parser;
use crate::sources::FileSources;
use crate::toolchain::ClangToolchain;
use ats2_application::ports::{DiagnosticsPort, OutputPort};

/// The parsed command line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CliArgs {
    pub source: PathBuf,
    pub ir: Option<PathBuf>,
    pub binary: Option<PathBuf>,
    /// What to do about a constraint that is neither proved nor refuted.
    ///
    /// Strict by default, because that is what "checked" means.  The
    /// `--permissive` hatch exists because a solver is finished later
    /// than the language it reasons about, and a program the checker
    /// merely cannot follow is not a program that is wrong.
    pub strictness: Strictness,
    /// Extra directories to look in for a `staload`ed file, tried after
    /// the directory of whichever file wrote the `staload`.
    pub include: Vec<PathBuf>,
}

impl CliArgs {
    /// Parse argv (without the program name).  Usage:
    /// `ats2llvm <file.dats> [--ir <file.ll>] [--bin <executable>]
    ///           [--strict | --permissive]`
    /// With `--bin` but no `--ir`, the IR is written next to the binary.
    pub fn parse_args(args: &[String]) -> Result<CliArgs, String> {
        let mut source: Option<PathBuf> = None;
        let mut ir: Option<PathBuf> = None;
        let mut binary: Option<PathBuf> = None;
        let mut strictness = Strictness::default();
        let mut include: Vec<PathBuf> = Vec::new();
        let mut i = 0;
        while i < args.len() {
            match args[i].as_str() {
                "--ir" => {
                    i += 1;
                    let value = args.get(i).ok_or("`--ir` needs a value")?;
                    ir = Some(PathBuf::from(value));
                }
                "--bin" => {
                    i += 1;
                    let value = args.get(i).ok_or("`--bin` needs a value")?;
                    binary = Some(PathBuf::from(value));
                }
                "-I" | "--include" => {
                    i += 1;
                    let value = args.get(i).ok_or("`-I` needs a directory")?;
                    include.push(PathBuf::from(value));
                }
                "--permissive" => strictness = Strictness::Permissive,
                "--strict" => strictness = Strictness::Strict,
                flag if flag.starts_with("-") && flag != "-" => {
                    return Err(format!("unknown flag `{flag}`"));
                }
                file => {
                    if source.is_some() {
                        return Err(format!("unexpected extra argument `{file}`"));
                    }
                    source = Some(PathBuf::from(file));
                }
            }
            i += 1;
        }
        let source = source.ok_or("missing source file")?;
        if binary.is_some() && ir.is_none() {
            let mut default = binary.as_ref().expect("checked").as_os_str().to_os_string();
            default.push(".ll");
            ir = Some(PathBuf::from(default));
        }
        Ok(CliArgs {
            source,
            ir,
            binary,
            strictness,
            include,
        })
    }
}

/// The controller: read the source, run the use cases, map to an exit code.
pub fn run(args: Vec<String>) -> i32 {
    let cli = match CliArgs::parse_args(&args) {
        Ok(cli) => cli,
        Err(message) => return usage_error(&message),
    };
    let source = match std::fs::read_to_string(&cli.source) {
        Ok(source) => source,
        Err(e) => {
            eprintln!("ats2llvm: cannot read {}: {e}", cli.source.display());
            return 1;
        }
    };
    let diag = StderrDiagnostics::new();
    match &cli.binary {
        Some(binary) => build_binary(&source, &cli, binary, &diag),
        None => build_ir(&source, &cli, &diag),
    }
}

/// Print a usage error and return the usage exit code.
fn usage_error(message: &str) -> i32 {
    eprintln!("ats2llvm: {message}");
    eprintln!(
        "usage: ats2llvm <file.dats> [--ir <file.ll>] [--bin <executable>] \\
         [-I <dir>] [--permissive]"
    );
    2
}

/// Where this invocation looks for the units the source `staload`s.
fn sources(cli: &CliArgs) -> FileSources {
    FileSources::at(&cli.source).searching(cli.include.iter().cloned())
}

/// The `--bin` route: compile to IR, persist it, link it.
fn build_binary(
    source: &str,
    cli: &CliArgs,
    binary: &std::path::Path,
    diag: &StderrDiagnostics,
) -> i32 {
    let ir_path = cli.ir.as_ref().expect("parse_args guarantees an IR path");
    let uc = CompileExecutableUseCase::new(Parser, LlvmIrEmitter, ClangToolchain, FileOutput)
        .checking(cli.strictness)
        .loading(sources(cli));
    match uc.execute(source, ir_path, binary) {
        Ok(()) => {
            diag.info(&format!("wrote IR      {}", ir_path.display()));
            diag.info(&format!("wrote binary  {}", binary.display()));
            0
        }
        Err(errors) => {
            diag.report_errors(&errors);
            1
        }
    }
}

/// The IR route: compile source text down to IR, then persist or print.
fn build_ir(source: &str, cli: &CliArgs, diag: &StderrDiagnostics) -> i32 {
    let uc = CompileToIrUseCase::new(Parser, LlvmIrEmitter)
        .checking(cli.strictness)
        .loading(sources(cli));
    match uc.execute(source) {
        Ok(ir) => match &cli.ir {
            Some(ir_path) => match FileOutput.write(ir_path, &ir) {
                Ok(()) => {
                    diag.info(&format!("wrote IR      {}", ir_path.display()));
                    0
                }
                Err(message) => {
                    diag.report_errors(&[ats2_domain::errors::CompileError::target(message)]);
                    1
                }
            },
            None => {
                print!("{ir}");
                0
            }
        },
        Err(errors) => {
            diag.report_errors(&errors);
            1
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(args: &[&str]) -> Result<CliArgs, String> {
        let owned: Vec<String> = args.iter().map(|s| s.to_string()).collect();
        CliArgs::parse_args(&owned)
    }

    #[test]
    fn a_program_looks_only_beside_itself_unless_told_otherwise() {
        assert_eq!(
            parse(&["hello.dats"]).expect("parse").include,
            Vec::<PathBuf>::new()
        );
    }

    #[test]
    fn include_directories_are_kept_in_the_order_they_were_given() {
        // They are tried in order after the directory of whichever file
        // wrote the `staload`, so the order is the meaning.
        let a = parse(&["-I", "vendor", "--include", "third_party", "hello.dats"]).expect("parse");
        assert_eq!(
            a.include,
            vec![PathBuf::from("vendor"), PathBuf::from("third_party")]
        );
        assert_eq!(a.source, PathBuf::from("hello.dats"));
    }

    #[test]
    fn an_include_with_no_directory_is_a_usage_error() {
        assert!(parse(&["hello.dats", "-I"]).is_err());
    }

    #[test]
    fn a_short_flag_nobody_defined_is_still_a_flag() {
        // `-x` used to be taken for a source file, so the error came
        // out as \"unexpected extra argument\" pointing at the real one.
        let message = parse(&["-x", "hello.dats"]).expect_err("should fail");
        assert!(message.contains("-x"), "{message}");
    }

    #[test]
    fn checking_is_strict_unless_the_caller_says_otherwise() {
        // The default has to be the honest one: a checker that forgives
        // what it cannot prove is not checking anything.
        assert_eq!(
            parse(&["hello.dats"]).expect("parse").strictness,
            Strictness::Strict
        );
    }

    #[test]
    fn permissive_asks_for_only_the_provably_false_to_be_refused() {
        // The escape hatch: a program the checker merely cannot reason
        // about still builds, so a corpus can be adopted before the
        // solver is finished.
        let a = parse(&["hello.dats", "--permissive"]).expect("parse");
        assert_eq!(a.strictness, Strictness::Permissive);
        assert_eq!(a.source, PathBuf::from("hello.dats"));
    }

    #[test]
    fn strict_may_be_asked_for_by_name() {
        assert_eq!(
            parse(&["--strict", "hello.dats"])
                .expect("parse")
                .strictness,
            Strictness::Strict
        );
    }

    #[test]
    fn source_alone_prints_ir_to_stdout() {
        let a = parse(&["hello.dats"]).expect("parse");
        assert_eq!(a.source, PathBuf::from("hello.dats"));
        assert_eq!(a.ir, None);
        assert_eq!(a.binary, None);
    }

    #[test]
    fn ir_output_is_parsed() {
        let a = parse(&["hello.dats", "--ir", "out.ll"]).expect("parse");
        assert_eq!(a.ir.as_deref(), Some(std::path::Path::new("out.ll")));
        assert_eq!(a.binary, None);
    }

    #[test]
    fn binary_output_implies_an_ir_file_next_to_it() {
        let a = parse(&["hello.dats", "--bin", "hello"]).expect("parse");
        assert_eq!(a.binary.as_deref(), Some(std::path::Path::new("hello")));
        assert_eq!(a.ir.as_deref(), Some(std::path::Path::new("hello.ll")));
    }

    #[test]
    fn explicit_ir_wins_over_the_default() {
        let a = parse(&["hello.dats", "--bin", "hello", "--ir", "custom.ll"]).expect("parse");
        assert_eq!(a.ir.as_deref(), Some(std::path::Path::new("custom.ll")));
        assert_eq!(a.binary.as_deref(), Some(std::path::Path::new("hello")));
    }

    #[test]
    fn missing_source_is_a_usage_error() {
        let err = parse(&[]).expect_err("should fail");
        assert!(err.contains("source"), "{err}");
    }

    #[test]
    fn unknown_flags_are_usage_errors() {
        for args in [
            &["hello.dats", "--frobnicate"][..],
            &["--ir"],
            &["--bin"],
            &["a.dats", "b.dats"],
        ] {
            let err = parse(args).expect_err("should fail: {args:?}");
            assert!(!err.is_empty(), "empty message for {args:?}");
        }
    }

    #[test]
    fn flag_needing_a_value_refuses_a_missing_value() {
        let err = parse(&["hello.dats", "--ir"]).expect_err("should fail");
        assert!(err.contains("--ir"), "{err}");
    }
}
