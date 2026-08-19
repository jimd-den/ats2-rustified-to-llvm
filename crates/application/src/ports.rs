//! # Ports — the abstract wall around the outside world
//!
//! *Literate note.*  This module declares the five **ports** through which
//! the application layer talks to everything external: source text becomes
//! a program (`ParserPort`), a program becomes LLVM IR (`LlvmEmitterPort`),
//! IR becomes an executable on the host toolchain (`ToolchainPort`), text
//! reaches a named output (`OutputPort`), and diagnostics reach a human
//! (`DiagnosticsPort`).  Ports are pure traits: no implementation, no
//! behavior, no opinions.  The dependency rule is what makes this
//! powerful — the use cases depend on these abstractions, the
//! infrastructure crate provides the concrete implementations, and the
//! application crate is tested against tiny in-memory fakes.
//!
//! A note on `std::path::Path`: naming external artifacts is a legitimate
//! application concern, so the toolchain and output ports speak in paths.
//! Nothing here ever *opens* a path; touching the file system remains an
//! infrastructure privilege.
//!
//! Every trait is object-safe (`dyn ParserPort` works) so the use cases
//! can be wired with either generics or trait objects — the contract
//! tests below pin that property down.
//!
//! *TDD note.*  The contract tests below were written *first*, against a
//! file with no traits in it (RED: the spec did not compile).  The traits
//! were then added to satisfy exactly those tests (GREEN).  The tests are
//! the normative description of what each port must look like.

use std::path::Path;

use ats2_domain::ast::Program;
use ats2_domain::errors::CompileError;

/// Turns source text into a parsed program.  Hides the lexer/parser pair
/// behind one seam: callers neither know nor care how tokens are made.
pub trait ParserPort {
    fn parse(&self, source: &str) -> Result<Program, Vec<CompileError>>;
}

/// Lowers a parsed program to canonical textual LLVM IR.
pub trait LlvmEmitterPort {
    fn emit(&self, program: &Program) -> Result<String, CompileError>;
}

/// Links an LLVM IR file into an executable using the host toolchain
/// (clang/llc).  The `String` error is free-form tool output.
pub trait ToolchainPort {
    fn link(&self, ir_path: &Path, output: &Path) -> Result<(), String>;
}

/// Writes text to a named output (a file, a socket, …).  The `String`
/// error is the target's own description of what went wrong.
pub trait OutputPort {
    fn write(&self, path: &Path, contents: &str) -> Result<(), String>;
}

/// Presents compiler diagnostics to a human.
pub trait DiagnosticsPort {
    fn report_errors(&self, errors: &[CompileError]);
    fn info(&self, message: &str);
}

#[cfg(test)]
mod contract_tests {
    //! The port contract, pinned by tests and in-memory fakes.
    use std::cell::RefCell;
    use std::path::Path;

    use ats2_domain::ast::{Def, Expr, FunDef, Program, Ty};
    use ats2_domain::errors::CompileError;

    // --- fakes -------------------------------------------------------

    /// A parser fake that returns a canned program and records its input.
    struct FakeParser {
        calls: RefCell<usize>,
        last_source: RefCell<Option<String>>,
    }

    /// An emitter fake returning canned IR and recording its input.
    struct FakeEmitter {
        calls: RefCell<usize>,
        last_program: RefCell<Option<Program>>,
    }

    /// A toolchain fake recording the paths it was asked to link.
    struct FakeToolchain {
        linked: RefCell<Vec<(String, String)>>,
    }

    /// An output fake recording every write.
    struct FakeOutput {
        writes: RefCell<Vec<(String, String)>>,
    }

    /// A diagnostics fake recording what it was told.
    struct FakeDiagnostics {
        error_count: RefCell<usize>,
        messages: RefCell<Vec<String>>,
    }

    fn canned_program() -> Program {
        Program::new(vec![Def::Fun(FunDef {
            universals: vec![],
            existentials: vec![],
            ty_params: vec![],
            name: "f".into(),
            params: vec![],
            ret: Ty::Name("int".into()),
            body: Expr::IntLit(1),
        })])
    }

    // --- implementations of the port traits for the fakes -----------

    impl crate::ports::ParserPort for FakeParser {
        fn parse(&self, source: &str) -> Result<Program, Vec<CompileError>> {
            *self.calls.borrow_mut() += 1;
            *self.last_source.borrow_mut() = Some(source.to_string());
            Ok(canned_program())
        }
    }

    impl crate::ports::LlvmEmitterPort for FakeEmitter {
        fn emit(&self, program: &Program) -> Result<String, CompileError> {
            *self.calls.borrow_mut() += 1;
            *self.last_program.borrow_mut() = Some(program.clone());
            Ok("define i64 @f() { ret i64 1 }".to_string())
        }
    }

    impl crate::ports::ToolchainPort for FakeToolchain {
        fn link(&self, ir_path: &Path, output: &Path) -> Result<(), String> {
            self.linked.borrow_mut().push((ir_path.to_string_lossy().into_owned(), output.to_string_lossy().into_owned()));
            Ok(())
        }
    }

    impl crate::ports::OutputPort for FakeOutput {
        fn write(&self, path: &Path, contents: &str) -> Result<(), String> {
            self.writes.borrow_mut().push((path.to_string_lossy().into_owned(), contents.to_string()));
            Ok(())
        }
    }

    impl crate::ports::DiagnosticsPort for FakeDiagnostics {
        fn report_errors(&self, errors: &[CompileError]) {
            *self.error_count.borrow_mut() += errors.len();
        }
        fn info(&self, message: &str) {
            self.messages.borrow_mut().push(message.to_string());
        }
    }

    // --- helpers the fakes rely on (kept in the same module so the
    // --- contract tests below stay readable)

    fn fake_parser() -> FakeParser {
        FakeParser { calls: RefCell::new(0), last_source: RefCell::new(None) }
    }

    fn fake_emitter() -> FakeEmitter {
        FakeEmitter { calls: RefCell::new(0), last_program: RefCell::new(None) }
    }

    // --- parser port contract --------------------------------------

    #[test]
    fn parser_port_turns_source_into_a_program() {
        let parser = fake_parser();
        let port: &dyn crate::ports::ParserPort = &parser; // object-safe
        let program = port.parse("fun f(): int = 1").expect("parse");
        assert_eq!(program.defs().len(), 1);
        assert_eq!(*parser.calls.borrow(), 1);
        assert_eq!(parser.last_source.borrow().as_deref(), Some("fun f(): int = 1"));
    }

    #[test]
    fn parser_port_reports_errors_as_a_list() {
        struct FailingParser;
        impl crate::ports::ParserPort for FailingParser {
            fn parse(&self, _source: &str) -> Result<Program, Vec<CompileError>> {
                Err(vec![CompileError::emit("boom")])
            }
        }
        let port: &dyn crate::ports::ParserPort = &FailingParser;
        let errs = port.parse("x").unwrap_err();
        assert_eq!(errs.len(), 1);
        assert_eq!(errs[0].message(), "boom");
    }

    // --- emitter port contract -------------------------------------

    #[test]
    fn emitter_port_lowers_a_program_to_ir_text() {
        let emitter = fake_emitter();
        let port: &dyn crate::ports::LlvmEmitterPort = &emitter;
        let ir = port.emit(&canned_program()).expect("emit");
        assert_eq!(ir, "define i64 @f() { ret i64 1 }");
        assert_eq!(*emitter.calls.borrow(), 1);
        assert_eq!(emitter.last_program.borrow().as_ref(), Some(&canned_program()));
    }

    #[test]
    fn emitter_port_reports_single_compile_error() {
        struct FailingEmitter;
        impl crate::ports::LlvmEmitterPort for FailingEmitter {
            fn emit(&self, _program: &Program) -> Result<String, CompileError> {
                Err(CompileError::emit("unsupported type"))
            }
        }
        let port: &dyn crate::ports::LlvmEmitterPort = &FailingEmitter;
        let err = port.emit(&canned_program()).unwrap_err();
        assert_eq!(err.message(), "unsupported type");
    }

    // --- toolchain port contract -----------------------------------

    #[test]
    fn toolchain_port_links_named_paths() {
        let toolchain = FakeToolchain { linked: RefCell::new(vec![]) };
        let port: &dyn crate::ports::ToolchainPort = &toolchain;
        let r = port.link(Path::new("out.ll"), Path::new("a.out"));
        assert!(r.is_ok());
        let linked = toolchain.linked.borrow();
        assert_eq!(linked.len(), 1);
        assert_eq!(linked[0], ("out.ll".to_string(), "a.out".to_string()));
    }

    #[test]
    fn toolchain_port_failures_are_free_form_strings() {
        struct FailingToolchain;
        impl crate::ports::ToolchainPort for FailingToolchain {
            fn link(&self, _ir: &Path, _out: &Path) -> Result<(), String> {
                Err("clang: error: linker command failed".into())
            }
        }
        let port: &dyn crate::ports::ToolchainPort = &FailingToolchain;
        assert_eq!(
            port.link(Path::new("a.ll"), Path::new("a.out")).unwrap_err(),
            "clang: error: linker command failed"
        );
    }

    // --- output port contract --------------------------------------

    #[test]
    fn output_port_writes_named_text() {
        let output = FakeOutput { writes: RefCell::new(vec![]) };
        let port: &dyn crate::ports::OutputPort = &output;
        let r = port.write(Path::new("out.ll"), "define void @main()");
        assert!(r.is_ok());
        let writes = output.writes.borrow();
        assert_eq!(writes.len(), 1);
        assert_eq!(writes[0], ("out.ll".to_string(), "define void @main()".to_string()));
    }

    #[test]
    fn output_port_failures_carry_the_targets_message() {
        struct FailingOutput;
        impl crate::ports::OutputPort for FailingOutput {
            fn write(&self, _path: &Path, _contents: &str) -> Result<(), String> {
                Err("permission denied".into())
            }
        }
        let port: &dyn crate::ports::OutputPort = &FailingOutput;
        assert_eq!(
            port.write(Path::new("x.ll"), "").unwrap_err(),
            "permission denied"
        );
    }

    // --- diagnostics port contract ---------------------------------

    #[test]
    fn diagnostics_port_reports_errors_and_info() {
        let diag = FakeDiagnostics {
            error_count: RefCell::new(0),
            messages: RefCell::new(vec![]),
        };
        let port: &dyn crate::ports::DiagnosticsPort = &diag;
        port.report_errors(&[CompileError::emit("bad")]);
        port.info("wrote out.ll");
        assert_eq!(*diag.error_count.borrow(), 1);
        assert_eq!(diag.messages.borrow().as_slice(), ["wrote out.ll"]);
    }
}
