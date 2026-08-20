//! # ParseUseCase — "turn source text into a program"

use ats2_domain::ast::Program;
use ats2_domain::errors::CompileError;

use crate::ports::ParserPort;

/// The use case that parses ATS2 source text into a domain program.
///
/// It is deliberately a *thin* orchestrator: the entire heavy lifting
/// belongs to whatever `ParserPort` implementation the outer layer wired
/// in.  The use case exists so that "parsing" is a named business rule
/// with a testable contract instead of a call scattered through the
/// controller.
pub struct ParseUseCase<P: ParserPort> {
    parser: P,
}

impl<P: ParserPort> ParseUseCase<P> {
    /// Wire the use case to a concrete parser port implementation.
    pub fn new(parser: P) -> Self {
        Self { parser }
    }

    /// Parse source text.  Returns the program, or every lexer/parser
    /// error that was produced (the port decides how many to report).
    pub fn execute(&self, source: &str) -> Result<Program, Vec<CompileError>> {
        self.parser.parse(source)
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use ats2_domain::errors::CompileError;

    use super::*;
    use crate::use_cases::fakes::{FakeParser, canned_program};

    #[test]
    fn parses_source_into_a_program() {
        let events = Rc::new(RefCell::new(vec![]));
        let parser = FakeParser {
            events: events.clone(),
            fail: None,
        };
        let uc = ParseUseCase::new(parser);
        let program = uc.execute("fun f(): int = 1").expect("parse");
        assert_eq!(program, canned_program());
        assert_eq!(*events.borrow(), ["parse:fun f(): int = 1"]);
    }

    #[test]
    fn forwards_parser_errors_unmodified() {
        let events = Rc::new(RefCell::new(vec![]));
        let errs = vec![CompileError::emit("bad"), CompileError::emit("worse")];
        let parser = FakeParser {
            events: events.clone(),
            fail: Some(errs.clone()),
        };
        let uc = ParseUseCase::new(parser);
        let got = uc.execute("nonsense").expect_err("should fail");
        assert_eq!(got, errs);
    }
}
