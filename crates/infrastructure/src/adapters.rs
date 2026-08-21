//! # Port adapters — the seam where abstraction meets mechanism
//!
//! *Literate note.*  The application layer declared five ports; here the
//! infrastructure crate proves it honors them.  The lexer/parser pair is
//! already a `ParserPort`; the IR emitter is already a
//! `LlvmEmitterPort`.  Nothing in the application crate changes when these
//! impls are added — that is the entire point of depending on abstractions.

use ats2_domain::ast::Program;
use ats2_domain::errors::CompileError;

use ats2_application::ports::{LlvmEmitterPort, ParserPort};

use crate::llvm_ir::LlvmIrEmitter;
use crate::parser::Parser;

/// The stateless parser *is* the parsing port.
impl ParserPort for Parser {
    fn parse(&self, source: &str) -> Result<Program, Vec<CompileError>> {
        Parser::parse(source)
    }

    fn parse_dependency(&self, source: &str) -> Result<Program, Vec<CompileError>> {
        Parser::parse_dependency(source)
    }

    /// The prelude, read by the same parser as user code.
    ///
    /// A prelude that does not parse is a bug in this crate rather than
    /// in the program being compiled, so there is nothing useful to
    /// report and nothing sensible to do with a failure: the caller
    /// gets no ambient declarations and every claim resting on one
    /// becomes unproved, which is loud in exactly the right way.
    fn prelude(&self) -> Program {
        let mut defs = Vec::new();
        for source in [
            crate::prelude::PRELUDE_SOURCE,
            crate::prelude::PRELUDE_STATIC_SOURCE,
        ] {
            defs.extend(
                Parser::parse(source)
                    .map(|p| p.defs().to_vec())
                    .unwrap_or_default(),
            );
        }
        Program::new(defs)
    }
}

/// The stateless emitter *is* the IR-emitting port.
impl LlvmEmitterPort for LlvmIrEmitter {
    fn emit(&self, program: &Program) -> Result<String, CompileError> {
        LlvmIrEmitter::emit(program)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_parser_honors_the_parser_port() {
        let parser: &dyn ParserPort = &Parser;
        let program = parser.parse("fun f(): int = 1").expect("parse");
        assert_eq!(program.defs().len(), 1);
    }

    #[test]
    fn the_parser_port_recovers_available_dependency_declarations() {
        let parser: &dyn ParserPort = &Parser;
        let program = parser
            .parse_dependency("extern fun declared(): int\nimplement")
            .expect("dependency parse");
        assert_eq!(program.defs().len(), 1);
    }

    #[test]
    fn the_emitter_honors_the_emitter_port() {
        let emitter: &dyn LlvmEmitterPort = &LlvmIrEmitter;
        let program = Parser::parse("fun f(): int = 1").expect("parse");
        let ir = emitter.emit(&program).expect("emit");
        assert!(ir.starts_with("; ModuleID = 'ats2llvm'"), "got:\n{ir}");
    }

    #[test]
    fn the_ports_compose_into_the_compile_use_case() {
        // The whole reason ports exist: the *real* implementations slot
        // into the *application* use case unchanged.
        use ats2_application::use_cases::CompileToIrUseCase;
        let uc = CompileToIrUseCase::new(Parser, LlvmIrEmitter);
        let ir = uc.execute("fun f(): int = 1").expect("compile");
        assert!(ir.contains("define i64 @f()"), "got:\n{ir}");
    }
}
