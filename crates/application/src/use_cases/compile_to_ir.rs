//! # CompileToIrUseCase — "compile source text to LLVM IR"
//!
//! *Literate note.*  This is the flagship use case of the front-end: it
//! sequences the two core ports — parse, then emit — and translates a
//! single emitter failure into the error list the rest of the pipeline
//! speaks.  Note the orchestration contract the tests pin down: the
//! emitter must **not** be consulted when parsing fails.  Short-circuiting
//! is business policy, and business policy lives here, not in the ports.

use ats2_domain::errors::CompileError;

use crate::checking::Strictness;
use crate::ports::{LlvmEmitterPort, ParserPort, SourceLoaderPort};

/// Compiles source text down to canonical textual LLVM IR.
pub struct CompileToIrUseCase<P: ParserPort, E: LlvmEmitterPort> {
    parser: P,
    emitter: E,
    /// What to do about a constraint the checker can neither prove nor
    /// refute.  A *policy*, so it is settable — and set here rather than
    /// inside the checker, because it is the caller who knows whether an
    /// unproved claim should stop a build.
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

impl<P: ParserPort, E: LlvmEmitterPort> CompileToIrUseCase<P, E> {
    pub fn new(parser: P, emitter: E) -> Self {
        Self {
            parser,
            emitter,
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

    /// Compile under a different strictness than the default.
    pub fn checking(mut self, strictness: Strictness) -> Self {
        self.strictness = strictness;
        self
    }

    /// Parse then emit.  Any parse error short-circuits: the emitter is
    /// never called on a program that does not exist.
    pub fn execute(&self, source: &str) -> Result<String, Vec<CompileError>> {
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
        // The dependent half of the program is checked here, between
        // parsing and emission: it is the last point at which the static
        // language still exists.  Emission erases it, by design.
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
        Ok(ir)
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use ats2_domain::errors::CompileError;

    use super::*;
    use crate::use_cases::fakes::{FakeEmitter, FakeParser};

    #[test]
    fn happy_path_parses_then_emits_and_returns_ir() {
        let events = Rc::new(RefCell::new(vec![]));
        let parser = FakeParser {
            events: events.clone(),
            fail: None,
        };
        let emitter = FakeEmitter {
            events: events.clone(),
            ir: "define i64 @f()".into(),
            fail: None,
        };
        let uc = CompileToIrUseCase::new(parser, emitter);
        let ir = uc.execute("fun f(): int = 1").expect("compile");
        assert_eq!(ir, "define i64 @f()");
        // Orchestration: parse happened first, emit second.
        assert_eq!(*events.borrow(), ["parse:fun f(): int = 1", "emit:1"]);
    }

    #[test]
    fn parse_failure_short_circuits_the_emitter() {
        let events = Rc::new(RefCell::new(vec![]));
        let parse_errs = vec![CompileError::parse(canned_span(), "syntax")];
        let parser = FakeParser {
            events: events.clone(),
            fail: Some(parse_errs.clone()),
        };
        let emitter = FakeEmitter {
            events: events.clone(),
            ir: String::new(),
            fail: None,
        };
        let uc = CompileToIrUseCase::new(parser, emitter);
        let got = uc.execute("garbage").expect_err("should fail");
        assert_eq!(got, parse_errs);
        // The emitter must never hear about the failure.
        assert_eq!(*events.borrow(), ["parse:garbage"]);
    }

    #[test]
    fn emitter_failure_is_wrapped_into_the_error_list() {
        let events = Rc::new(RefCell::new(vec![]));
        let parser = FakeParser {
            events: events.clone(),
            fail: None,
        };
        let emitter = FakeEmitter {
            events: events.clone(),
            ir: String::new(),
            fail: Some(CompileError::emit("unsupported type `list`")),
        };
        let uc = CompileToIrUseCase::new(parser, emitter);
        let got = uc.execute("fun f(): int = 1").expect_err("should fail");
        assert_eq!(got.len(), 1);
        assert_eq!(got[0].message(), "unsupported type `list`");
        assert_eq!(got[0].kind(), CompileError::emit("x").kind());
    }

    /// A tiny span helper so tests need not import token types.
    fn canned_span() -> ats2_domain::tokens::Span {
        ats2_domain::tokens::Span::new(
            ats2_domain::tokens::Pos::new(1, 1, 0),
            ats2_domain::tokens::Pos::new(1, 1, 0),
        )
    }
}
