//! A persistent, effect-free ATS REPL session.
//!
//! The session owns accepted source, not parser internals. Each submission
//! reparses the complete accepted transcript plus the candidate, which keeps
//! typedefs, macros, overloads, and declarations in exactly the same lexical
//! environment they would have in a source file. A rejected candidate is
//! transactional: neither source nor program changes.

use ats2_domain::ast::Program;
use ats2_domain::errors::CompileError;

use crate::checking::{Strictness, check_program};
use crate::linearity::check_linearity;
use crate::ports::ParserPort;

/// What changed after a submission was accepted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplUpdate {
    pub added_definitions: usize,
    pub total_definitions: usize,
}

/// The application use case behind an interactive ATS shell.
///
/// Terminal prompts, line editing, history, and LLVM execution are adapters.
/// This type only owns the language session and decides whether a candidate
/// becomes part of it.
pub struct ReplSession<'a, P: ParserPort + ?Sized> {
    parser: &'a P,
    strictness: Strictness,
    source: String,
    program: Program,
}

impl<'a, P: ParserPort + ?Sized> ReplSession<'a, P> {
    pub fn new(parser: &'a P, strictness: Strictness) -> Self {
        Self {
            parser,
            strictness,
            source: String::new(),
            program: Program::new(Vec::new()),
        }
    }

    /// Check and commit one definition-oriented snippet.
    ///
    /// The complete transcript is parsed again deliberately: parser state is
    /// language state, and keeping a second incremental symbol table here
    /// would let batch compilation and the REPL disagree.
    pub fn submit(&mut self, snippet: &str) -> Result<ReplUpdate, Vec<CompileError>> {
        let (source, program) = self.check_candidate(snippet)?;
        let before = self.program.defs().len();
        let total = program.defs().len();
        self.source = source;
        self.program = program;
        Ok(ReplUpdate {
            added_definitions: total.saturating_sub(before),
            total_definitions: total,
        })
    }

    /// Check a candidate without changing the session.
    pub fn check(&self, snippet: &str) -> Result<ReplUpdate, Vec<CompileError>> {
        let (_, program) = self.check_candidate(snippet)?;
        let before = self.program.defs().len();
        let total = program.defs().len();
        Ok(ReplUpdate {
            added_definitions: total.saturating_sub(before),
            total_definitions: total,
        })
    }

    pub fn source(&self) -> &str {
        &self.source
    }

    pub fn program(&self) -> &Program {
        &self.program
    }

    pub fn reset(&mut self) {
        self.source.clear();
        self.program = Program::new(Vec::new());
    }

    fn check_candidate(&self, snippet: &str) -> Result<(String, Program), Vec<CompileError>> {
        let source = if self.source.is_empty() {
            snippet.to_owned()
        } else {
            format!("{}\n{snippet}", self.source)
        };
        let program = self.parser.parse(&source)?;
        let prelude = self.parser.prelude();
        let mut errors = check_program(&program, &prelude, self.strictness);
        errors.extend(check_linearity(&program, &prelude));
        if errors.is_empty() {
            Ok((source, program))
        } else {
            Err(errors)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use ats2_domain::ast::{Def, Expr, FunDef, Param, Program, Ty};
    use ats2_domain::errors::{CompileError, ErrorKind};
    use ats2_domain::statics::{Quant, Sort};

    use super::*;

    struct SessionParser {
        seen: RefCell<Vec<String>>,
    }

    impl SessionParser {
        fn new() -> Self {
            Self {
                seen: RefCell::new(Vec::new()),
            }
        }

        fn valid_program(source: &str) -> Program {
            Program::new(
                source
                    .lines()
                    .enumerate()
                    .map(|(i, _)| {
                        Def::Fun(FunDef {
                            ty_params: vec![],
                            universals: vec![],
                            existentials: vec![],
                            metric: vec![],
                            name: format!("definition_{i}"),
                            params: vec![],
                            ret: Ty::Name("int".into()),
                            body: Expr::IntLit(i as i64),
                            proof: false,
                        })
                    })
                    .collect(),
            )
        }
    }

    impl ParserPort for SessionParser {
        fn parse(&self, source: &str) -> Result<Program, Vec<CompileError>> {
            self.seen.borrow_mut().push(source.to_owned());
            if source.contains("parse_bad") {
                return Err(vec![CompileError {
                    kind: ErrorKind::Parse,
                    span: None,
                    message: "bad snippet".into(),
                }]);
            }
            if source.contains("check_bad") {
                return Ok(Program::new(vec![Def::Fun(FunDef {
                    ty_params: vec![],
                    universals: vec![Quant {
                        vars: vec![("n".into(), Sort::Nat)],
                        guard: None,
                    }],
                    existentials: vec![],
                    metric: vec![],
                    name: "bad".into(),
                    params: vec![Param {
                        name: "x".into(),
                        ty: Ty::Index(
                            Box::new(Ty::Name("int".into())),
                            vec![ats2_domain::statics::SExp::Var("n".into())],
                        ),
                        borrowed: false,
                    }],
                    ret: Ty::Index(
                        Box::new(Ty::Name("int".into())),
                        vec![ats2_domain::statics::SExp::App(
                            "+".into(),
                            vec![
                                ats2_domain::statics::SExp::Var("n".into()),
                                ats2_domain::statics::SExp::IntLit(1),
                            ],
                        )],
                    ),
                    body: Expr::Var("x".into()),
                    proof: false,
                })]));
            }
            Ok(Self::valid_program(source))
        }
    }

    #[test]
    fn accepted_submissions_are_reparsed_as_one_persistent_program() {
        let parser = SessionParser::new();
        let mut session = ReplSession::new(&parser, Strictness::Strict);

        assert_eq!(
            session.submit("first").expect("first"),
            ReplUpdate {
                added_definitions: 1,
                total_definitions: 1,
            }
        );
        assert_eq!(
            session.submit("second").expect("second"),
            ReplUpdate {
                added_definitions: 1,
                total_definitions: 2,
            }
        );
        assert_eq!(session.source(), "first\nsecond");
        assert_eq!(
            parser.seen.borrow().as_slice(),
            ["first", "first\nsecond"]
        );
    }

    #[test]
    fn parse_and_check_failures_do_not_poison_the_session() {
        let parser = SessionParser::new();
        let mut session = ReplSession::new(&parser, Strictness::Strict);
        session.submit("first").expect("first");

        assert!(session.submit("parse_bad").is_err());
        assert_eq!(session.source(), "first");
        assert!(session.submit("check_bad").is_err());
        assert_eq!(session.source(), "first");
        session.submit("second").expect("second");
        assert_eq!(session.source(), "first\nsecond");
    }

    #[test]
    fn check_is_non_committing_and_reset_clears_the_language_environment() {
        let parser = SessionParser::new();
        let mut session = ReplSession::new(&parser, Strictness::Strict);
        session.submit("first").expect("first");

        let update = session.check("second").expect("check");
        assert_eq!(update.total_definitions, 2);
        assert_eq!(session.source(), "first");

        session.reset();
        assert!(session.source().is_empty());
        assert!(session.program().defs().is_empty());
    }
}
