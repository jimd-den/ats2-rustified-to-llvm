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

use crate::checking::Strictness;
use crate::ports::{LlvmEmitterPort, OutputPort, ParserPort, SourceLoaderPort, ToolchainPort};

/// Compiles source text into an executable binary.
pub struct CompileExecutableUseCase<
    P: ParserPort,
    E: LlvmEmitterPort,
    T: ToolchainPort,
    O: OutputPort,
> {
    parser: P,
    emitter: E,
    toolchain: T,
    output: O,
    /// See [`crate::checking::Strictness`].  Both entry points must
    /// check, and both must check the same way, or the guarantee depends
    /// on which one was used.
    strictness: Strictness,
    /// Where to find the units the source `staload`s, if anywhere.
    ///
    /// `None` is "this program is one file", which is what every
    /// caller wanted before multi-file support existed and what the
    /// fakes in these tests still want.  It is a trait object rather
    /// than a fifth type parameter because it is the only port that is
    /// genuinely optional, and making every existing caller name a
    /// do-nothing loader to say so would be a worse contract.
    modules: Option<Box<dyn SourceLoaderPort>>,
}

impl<P: ParserPort, E: LlvmEmitterPort, T: ToolchainPort, O: OutputPort>
    CompileExecutableUseCase<P, E, T, O>
{
    pub fn new(parser: P, emitter: E, toolchain: T, output: O) -> Self {
        Self {
            parser,
            emitter,
            toolchain,
            output,
            strictness: Strictness::default(),
            modules: None,
        }
    }

    /// Compile a program that may be spread over several files.
    ///
    /// Without this the source is the whole program and every `staload`
    /// is answered by the built-in prelude or by nothing.
    pub fn loading(mut self, loader: impl SourceLoaderPort + 'static) -> Self {
        self.modules = Some(Box::new(loader));
        self
    }

    /// Compile under a different strictness than the default.  See
    /// [`crate::checking::Strictness`]: an unproved claim is an error or
    /// is not, and only the caller knows which it wants.
    pub fn checking(mut self, strictness: Strictness) -> Self {
        self.strictness = strictness;
        self
    }

    /// Parse, emit, persist the IR at `ir_path`, and link it to
    /// `binary_path`.  Returns `()` on success.
    pub fn execute(
        &self,
        source: &str,
        ir_path: &Path,
        binary_path: &Path,
    ) -> Result<(), Vec<CompileError>> {
        let program = self.parser.parse(source)?;
        // Everything the source asked for, folded in before anything
        // looks at it.  It happens here, above the checker, because a
        // declaration in another file is a declaration this one is
        // entitled to rest on — and below the parser, because finding
        // files is not a parser's business.
        let program = match &self.modules {
            Some(loader) => crate::modules::resolve(program, &self.parser, loader.as_ref())?,
            None => program,
        };
        // See `compile_to_ir`: the static language is checked before it
        // is erased, and both entry points must check, or the guarantee
        // depends on which one was used.
        // Two disciplines, checked together: what the values *are*, and
        // whose they are.  Neither says anything about the other, so
        // both run and the reader sees everything wrong at once rather
        // than one thing per attempt.
        let prelude = self.parser.prelude();
        let mut violations = crate::checking::check_program(&program, &prelude, self.strictness);
        violations.extend(crate::linearity::check_linearity(&program, &prelude));
        if !violations.is_empty() {
            return Err(violations);
        }
        let ir = self.emitter.emit(&program).map_err(|e| vec![e])?;
        self.output
            .write(ir_path, &ir)
            .map_err(|m| vec![CompileError::target(m)])?;
        let mut inputs = vec![ir_path.to_path_buf()];
        // A program that brought its own C compiles to two files.  The
        // block is the body of some `extern fun` declared beside it, so
        // it goes to the toolchain together with the IR that calls into
        // it — written next to the IR, because that is where the other
        // half of the program already is.
        if let Some(c) = inline_c(&program) {
            let c_path = ir_path.with_extension("c");
            self.output
                .write(&c_path, &c)
                .map_err(|m| vec![CompileError::target(m)])?;
            inputs.push(c_path);
        }
        self.toolchain
            .link_all(&inputs, binary_path)
            .map_err(|m| vec![CompileError::target(m)])?;
        Ok(())
    }
}

/// Every `%{ ... %}` block the program brought, in the order written.
///
/// `None` when there are none, so a program with no foreign code still
/// compiles to exactly one file and the toolchain is asked for nothing
/// unusual.
fn inline_c(program: &ats2_domain::ast::Program) -> Option<String> {
    let blocks: Vec<&str> = program
        .defs()
        .iter()
        .filter_map(|d| match d {
            ats2_domain::ast::Def::InlineC(text) => Some(text.as_str()),
            _ => None,
        })
        .collect();
    (!blocks.is_empty()).then(|| blocks.join("\n"))
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
                parser: FakeParser {
                    events: events.clone(),
                    fail: None,
                },
                emitter: FakeEmitter {
                    events: events.clone(),
                    ir: "ir-text".into(),
                    fail: None,
                },
                output: FakeOutput {
                    events: events.clone(),
                    fail: false,
                },
                toolchain: FakeToolchain {
                    events: events.clone(),
                    fail: false,
                },
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
            [
                "parse:fun f(): int = 1",
                "emit:1",
                "write:out.ll:7",
                "link:out.ll:a.out"
            ]
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
        let output = FakeOutput {
            events: h.events.clone(),
            fail: true,
        };
        let uc = CompileExecutableUseCase::new(h.parser, h.emitter, h.toolchain, output);
        let err = uc
            .execute("fun f(): int = 1", Path::new("out.ll"), Path::new("a.out"))
            .expect_err("should fail");
        assert_eq!(err.len(), 1);
        assert_eq!(err[0].kind(), ErrorKind::Target);
        assert_eq!(err[0].message(), "disk full");
        // The toolchain is never consulted after a failed write.
        assert_eq!(
            *h.events.borrow(),
            ["parse:fun f(): int = 1", "emit:1", "write:out.ll:7"]
        );
    }

    #[test]
    fn linker_failure_becomes_a_target_error() {
        let h = Harness::new();
        let toolchain = FakeToolchain {
            events: h.events.clone(),
            fail: true,
        };
        let uc = CompileExecutableUseCase::new(h.parser, h.emitter, toolchain, h.output);
        let err = uc
            .execute("fun f(): int = 1", Path::new("out.ll"), Path::new("a.out"))
            .expect_err("should fail");
        assert_eq!(err.len(), 1);
        assert_eq!(err[0].kind(), ErrorKind::Target);
        assert_eq!(err[0].message(), "clang failed");
        // Order: everything up to and including the write happened.
        assert_eq!(
            *h.events.borrow(),
            [
                "parse:fun f(): int = 1",
                "emit:1",
                "write:out.ll:7",
                "link:out.ll:a.out"
            ]
        );
    }
}
