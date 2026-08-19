//! # CompileToIrUseCase — "compile source text to LLVM IR"
//!
//! *Literate note.*  This is the flagship use case of the front-end: it
//! sequences the two core ports — parse, then emit — and translates a
//! single emitter failure into the error list the rest of the pipeline
//! speaks.  Note the orchestration contract the tests pin down: the
//! emitter must **not** be consulted when parsing fails.  Short-circuiting
//! is business policy, and business policy lives here, not in the ports.

use ats2_domain::errors::CompileError;

use crate::ports::{LlvmEmitterPort, ParserPort};

/// Compiles source text down to canonical textual LLVM IR.
pub struct CompileToIrUseCase<P: ParserPort, E: LlvmEmitterPort> {
    parser: P,
    emitter: E,
}

impl<P: ParserPort, E: LlvmEmitterPort> CompileToIrUseCase<P, E> {
    pub fn new(parser: P, emitter: E) -> Self {
        Self { parser, emitter }
    }

    /// Parse then emit.  Any parse error short-circuits: the emitter is
    /// never called on a program that does not exist.
    pub fn execute(&self, source: &str) -> Result<String, Vec<CompileError>> {
        let program = self.parser.parse(source)?;
        // The dependent half of the program is checked here, between
        // parsing and emission: it is the last point at which the static
        // language still exists.  Emission erases it, by design.
        let violations = crate::constraints::check_program(&program);
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
        let parser = FakeParser { events: events.clone(), fail: None };
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
        let parser = FakeParser { events: events.clone(), fail: Some(parse_errs.clone()) };
        let emitter = FakeEmitter { events: events.clone(), ir: String::new(), fail: None };
        let uc = CompileToIrUseCase::new(parser, emitter);
        let got = uc.execute("garbage").expect_err("should fail");
        assert_eq!(got, parse_errs);
        // The emitter must never hear about the failure.
        assert_eq!(*events.borrow(), ["parse:garbage"]);
    }

    #[test]
    fn emitter_failure_is_wrapped_into_the_error_list() {
        let events = Rc::new(RefCell::new(vec![]));
        let parser = FakeParser { events: events.clone(), fail: None };
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
