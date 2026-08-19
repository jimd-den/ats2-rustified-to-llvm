//! # CompileExecutableUseCase — "build an executable from source text"
//!
//! *Literate note.*  The outermost use case: parse, emit, *persist* the IR
//! to a named output, then hand it to the host toolchain to link.  Its
//! tests pin down the full orchestration contract, including the failure
//! ordering: a failed IR write must prevent the toolchain from ever being
//! invoked.  External failures (disk, linker) enter the domain as
//! `Target` errors — the domain knows *that* a target failed, not which.

use std::path::Path;

use ats2_domain::errors::CompileError;

use crate::ports::{LlvmEmitterPort, OutputPort, ParserPort, ToolchainPort};

/// Compiles source text into an executable binary.
pub struct CompileExecutableUseCase<P: ParserPort, E: LlvmEmitterPort, T: ToolchainPort, O: OutputPort> {
    parser: P,
    emitter: E,
    toolchain: T,
    output: O,
}

impl<P: ParserPort, E: LlvmEmitterPort, T: ToolchainPort, O: OutputPort>
    CompileExecutableUseCase<P, E, T, O>
{
    pub fn new(parser: P, emitter: E, toolchain: T, output: O) -> Self {
        Self { parser, emitter, toolchain, output }
    }

    /// Parse, emit, persist the IR at `ir_path`, and link it to
    /// `binary_path`.  Returns `()` on success.
    pub fn execute(&self, source: &str, ir_path: &Path, binary_path: &Path) -> Result<(), Vec<CompileError>> {
        let program = self.parser.parse(source)?;
        // See `compile_to_ir`: the static language is checked before it
        // is erased, and both entry points must check, or the guarantee
        // depends on which one was used.
        let violations = crate::constraints::check_program(&program);
        if !violations.is_empty() {
            return Err(violations);
        }
        let ir = self.emitter.emit(&program).map_err(|e| vec![e])?;
        self.output.write(ir_path, &ir).map_err(|m| vec![CompileError::target(m)])?;
        self.toolchain.link(ir_path, binary_path).map_err(|m| vec![CompileError::target(m)])?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::path::Path;
    use std::rc::Rc;

    use ats2_domain::errors::ErrorKind;

    use super::*;
    use crate::use_cases::fakes::{FakeEmitter, FakeOutput, FakeParser, FakeToolchain};

    struct Harness {
        events: Rc<RefCell<Vec<String>>>,
        parser: FakeParser,
        emitter: FakeEmitter,
        output: FakeOutput,
        toolchain: FakeToolchain,
    }

    impl Harness {
        fn new() -> Self {
            let events = Rc::new(RefCell::new(vec![]));
            Self {
                events: events.clone(),
                parser: FakeParser { events: events.clone(), fail: None },
                emitter: FakeEmitter { events: events.clone(), ir: "ir-text".into(), fail: None },
                output: FakeOutput { events: events.clone(), fail: false },
                toolchain: FakeToolchain { events: events.clone(), fail: false },
            }
        }
    }

    #[test]
    fn builds_an_executable_end_to_end() {
        let h = Harness::new();
        let uc = CompileExecutableUseCase::new(h.parser, h.emitter, h.toolchain, h.output);
        uc.execute("fun f(): int = 1", Path::new("out.ll"), Path::new("a.out"))
            .expect("build");
        // Full orchestration contract, in order:
        assert_eq!(
            *h.events.borrow(),
            ["parse:fun f(): int = 1", "emit:1", "write:out.ll:7", "link:out.ll:a.out"]
        );
    }

    #[test]
    fn parse_failure_prevents_everything_after_it() {
        let h = Harness::new();
        let mut parser = h.parser;
        parser.fail = Some(vec![CompileError::emit("nope")]);
        let uc = CompileExecutableUseCase::new(parser, h.emitter, h.toolchain, h.output);
        uc.execute("garbage", Path::new("out.ll"), Path::new("a.out"))
            .expect_err("should fail");
        assert_eq!(*h.events.borrow(), ["parse:garbage"]);
    }

    #[test]
    fn failed_ir_write_prevents_linking() {
        let h = Harness::new();
        let output = FakeOutput { events: h.events.clone(), fail: true };
        let uc = CompileExecutableUseCase::new(h.parser, h.emitter, h.toolchain, output);
        let err = uc.execute("fun f(): int = 1", Path::new("out.ll"), Path::new("a.out"))
            .expect_err("should fail");
        assert_eq!(err.len(), 1);
        assert_eq!(err[0].kind(), ErrorKind::Target);
        assert_eq!(err[0].message(), "disk full");
        // The toolchain is never consulted after a failed write.
        assert_eq!(*h.events.borrow(), ["parse:fun f(): int = 1", "emit:1", "write:out.ll:7"]);
    }

    #[test]
    fn linker_failure_becomes_a_target_error() {
        let h = Harness::new();
        let toolchain = FakeToolchain { events: h.events.clone(), fail: true };
        let uc = CompileExecutableUseCase::new(h.parser, h.emitter, toolchain, h.output);
        let err = uc.execute("fun f(): int = 1", Path::new("out.ll"), Path::new("a.out"))
            .expect_err("should fail");
        assert_eq!(err.len(), 1);
        assert_eq!(err[0].kind(), ErrorKind::Target);
        assert_eq!(err[0].message(), "clang failed");
        // Order: everything up to and including the write happened.
        assert_eq!(
            *h.events.borrow(),
            ["parse:fun f(): int = 1", "emit:1", "write:out.ll:7", "link:out.ll:a.out"]
        );
    }
}
