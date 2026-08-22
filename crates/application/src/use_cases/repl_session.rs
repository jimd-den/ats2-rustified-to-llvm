//! # ReplSession — "an interactive ATS2 shell"
//!
//! *Literate note.*  The REPL session use case owns accepted source text,
//! not mutable compiler guts. Each submission evaluates against the
//! accumulated transcript: definitions persist transactionally, while
//! pure expressions are evaluated via synthesized execution wrappers.
//! A rejected snippet (syntax error, type error, or linear violation) is
//! transactional: neither the transcript nor the accepted AST is corrupted.

use ats2_domain::ast::{Def, Program};
use ats2_domain::errors::CompileError;

use crate::checking::{Strictness, check_program};
use crate::linearity::check_linearity;
use crate::ports::{ExecutionResult, LlvmEmitterPort, ParserPort, RunnerPort};

/// What changed after a definition was accepted into the session.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplUpdate {
    pub added_definitions: usize,
    pub total_definitions: usize,
}

/// The outcome of submitting an ATS snippet to the REPL.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReplResponse {
    /// A top-level definition was committed into the session environment.
    Definition(ReplUpdate),
    /// An expression was evaluated and produced execution output.
    Evaluated(ExecutionResult),
}

/// The application use case orchestrating an interactive ATS2 session.
pub struct ReplSession<P: ParserPort, E: LlvmEmitterPort, R: RunnerPort> {
    parser: P,
    emitter: E,
    runner: R,
    strictness: Strictness,
    source: String,
    program: Program,
}

impl<P: ParserPort, E: LlvmEmitterPort, R: RunnerPort> ReplSession<P, E, R> {
    pub fn new(parser: P, emitter: E, runner: R, strictness: Strictness) -> Self {
        Self {
            parser,
            emitter,
            runner,
            strictness,
            source: String::new(),
            program: Program::new(Vec::new()),
        }
    }

    /// Process a line or block of ATS code.
    ///
    /// If the snippet parses as one or more top-level definitions, it is
    /// typechecked and committed to the session state. If it is an expression,
    /// it is evaluated in the context of previous definitions without mutating
    /// the session.
    pub fn submit(&mut self, snippet: &str) -> Result<ReplResponse, Vec<CompileError>> {
        let trimmed = snippet.trim();
        if trimmed.is_empty() {
            return Ok(ReplResponse::Definition(ReplUpdate {
                added_definitions: 0,
                total_definitions: self.program.defs().len(),
            }));
        }

        // 1. Try treating as top-level definitions if it looks like a definition
        if looks_like_definition(trimmed) {
            return self.submit_definition(trimmed).map(ReplResponse::Definition);
        }

        // 2. Try evaluating as an expression
        match self.eval_expr(trimmed) {
            Ok(exec) => Ok(ReplResponse::Evaluated(exec)),
            Err(eval_errs) => {
                // If expression evaluation failed, try definition parse as fallback
                match self.submit_definition(trimmed) {
                    Ok(update) => Ok(ReplResponse::Definition(update)),
                    Err(_) => Err(eval_errs),
                }
            }
        }
    }

    /// Check and commit one or more definitions to the session transcript.
    pub fn submit_definition(&mut self, snippet: &str) -> Result<ReplUpdate, Vec<CompileError>> {
        let (candidate_source, candidate_program) = self.check_candidate(snippet)?;
        let before = self.program.defs().len();
        let total = candidate_program.defs().len();
        self.source = candidate_source;
        self.program = candidate_program;
        Ok(ReplUpdate {
            added_definitions: total.saturating_sub(before),
            total_definitions: total,
        })
    }

    /// Evaluate an expression in the current session context without altering state.
    pub fn eval_expr(&self, expr_snippet: &str) -> Result<ExecutionResult, Vec<CompileError>> {
        let trimmed = expr_snippet.trim().trim_end_matches(';');

        // Candidate 1: println!(<expr>)
        let print_wrapper = if self.source.is_empty() {
            format!("implement main0() = println!({trimmed})")
        } else {
            format!("{}\nimplement main0() = println!({trimmed})", self.source)
        };

        if let Ok((_src, prog)) = self.check_source(&print_wrapper) {
            let filtered_prog = filter_eval_program(&prog);
            if let Ok(ir) = self.emitter.emit(&filtered_prog) {
                if let Ok(res) = self.runner.run_ir(&ir) {
                    return Ok(res);
                }
            }
        }

        // Candidate 2: Statement/void wrapper
        let void_wrapper = if self.source.is_empty() {
            format!("implement main0() = {{\n  val () = ({trimmed})\n}}")
        } else {
            format!(
                "{}\nimplement main0() = {{\n  val () = ({trimmed})\n}}",
                self.source
            )
        };

        let (_src, prog) = self.check_source(&void_wrapper)?;
        let filtered_prog = filter_eval_program(&prog);
        let ir = self.emitter.emit(&filtered_prog).map_err(|e| vec![e])?;
        self.runner
            .run_ir(&ir)
            .map_err(|m| vec![CompileError::emit(m)])
    }

    /// Inspect the type of an expression in the current session context.
    pub fn type_of(&self, expr_snippet: &str) -> Result<String, Vec<CompileError>> {
        let trimmed = expr_snippet.trim().trim_end_matches(';');
        let test_src = if self.source.is_empty() {
            format!("val _repl_type_check = {trimmed}")
        } else {
            format!("{}\nval _repl_type_check = {trimmed}", self.source)
        };
        let (_src, prog) = self.check_source(&test_src)?;

        // Find the synthesized val binding
        for def in prog.defs().iter().rev() {
            if let Def::Val(v) = def {
                if v.name == "_repl_type_check" {
                    return Ok(format!("{:?}", v.value));
                }
            }
        }
        Ok("unknown".into())
    }

    /// Emit LLVM IR for the accumulated session program.
    pub fn emit_ir(&self) -> Result<String, CompileError> {
        self.emitter.emit(&self.program)
    }

    /// Load an entire ATS2 source string (e.g. from a file) into the session.
    pub fn load_source(&mut self, source: &str) -> Result<ReplUpdate, Vec<CompileError>> {
        self.submit_definition(source)
    }

    pub fn source(&self) -> &str {
        &self.source
    }

    pub fn program(&self) -> &Program {
        &self.program
    }

    pub fn strictness(&self) -> Strictness {
        self.strictness
    }

    pub fn set_strictness(&mut self, strictness: Strictness) {
        self.strictness = strictness;
    }

    pub fn reset(&mut self) {
        self.source.clear();
        self.program = Program::new(Vec::new());
    }

    fn check_candidate(&self, snippet: &str) -> Result<(String, Program), Vec<CompileError>> {
        let candidate = if self.source.is_empty() {
            snippet.to_owned()
        } else {
            format!("{}\n{snippet}", self.source)
        };
        self.check_source(&candidate)
    }

    fn check_source(&self, full_source: &str) -> Result<(String, Program), Vec<CompileError>> {
        let program = self.parser.parse(full_source)?;
        let prelude = self.parser.prelude();
        let mut errors = check_program(&program, &prelude, self.strictness);
        errors.extend(check_linearity(&program, &prelude));
        if !errors.is_empty() {
            return Err(errors);
        }

        // Dry-run code emission on the program to catch unbound variables / scope errors immediately
        if let Err(emit_err) = self.emitter.emit(&program) {
            return Err(vec![emit_err]);
        }

        Ok((full_source.to_owned(), program))
    }
}

/// Heuristic check whether a snippet starts with a known top-level ATS declaration keyword.
fn looks_like_definition(snippet: &str) -> bool {
    let first_word = snippet
        .split(|c: char| c.is_whitespace() || c == '(' || c == '{' || c == ':')
        .next()
        .unwrap_or("");

    matches!(
        first_word,
        "fun"
            | "fn"
            | "prfun"
            | "praxi"
            | "castfn"
            | "val"
            | "var"
            | "prval"
            | "implement"
            | "implmnt"
            | "primplement"
            | "datatype"
            | "datavtype"
            | "dataviewtype"
            | "typedef"
            | "vtypedef"
            | "viewtypedef"
            | "extern"
            | "staload"
            | "dynload"
            | "local"
            | "abstype"
            | "absviewtype"
            | "absvtype"
            | "exception"
            | "macdef"
            | "macrodef"
            | "symload"
            | "assume"
            | "overload"
    ) || snippet.starts_with('#')
        || snippet.starts_with("%{")
}

/// Retains only the most recent `main0` in the program to allow evaluating expressions
/// even after files with existing `main0` implementations have been loaded.
fn filter_eval_program(program: &Program) -> Program {
    let mut defs = Vec::new();
    let mut main_def = None;

    for def in program.defs() {
        match def {
            Def::Implement(im) if im.name == "main0" || im.name == "main" => {
                main_def = Some(def.clone());
            }
            other => defs.push(other.clone()),
        }
    }

    if let Some(m) = main_def {
        defs.push(m);
    }

    Program::new(defs).asking_for(program.staloads().to_vec())
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use ats2_domain::ast::{Def, Expr, FunDef, Program, Ty};
    use ats2_domain::errors::{CompileError, ErrorKind};

    use super::*;
    use crate::use_cases::fakes::{FakeEmitter, FakeRunner};

    fn dummy_program(name: &str) -> Program {
        Program::new(vec![Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![],
            existentials: vec![],
            metric: vec![],
            name: name.into(),
            params: vec![],
            ret: Ty::Name("int".into()),
            body: Expr::IntLit(1),
            proof: false,
        })])
    }

    struct DynamicParser {
        seen: RefCell<Vec<String>>,
    }

    impl ParserPort for DynamicParser {
        fn parse(&self, source: &str) -> Result<Program, Vec<CompileError>> {
            self.seen.borrow_mut().push(source.to_owned());
            if source.contains("syntax_err") {
                return Err(vec![CompileError {
                    kind: ErrorKind::Parse,
                    span: None,
                    message: "bad syntax".into(),
                }]);
            }
            if source.contains("println!(1 + 2)") {
                return Ok(dummy_program("eval_main"));
            }
            if source.contains("fun add") {
                return Ok(dummy_program("add"));
            }
            Ok(dummy_program("anon"))
        }
    }

    #[test]
    fn definition_submissions_accumulate_into_session() {
        let parser = DynamicParser {
            seen: RefCell::new(Vec::new()),
        };
        let emitter = FakeEmitter {
            events: Rc::new(RefCell::new(Vec::new())),
            ir: "define i64 @add()".into(),
            fail: None,
        };
        let runner = FakeRunner {
            events: Rc::new(RefCell::new(Vec::new())),
            output: "3\n".into(),
            fail: None,
        };

        let mut session = ReplSession::new(parser, emitter, runner, Strictness::Strict);
        let resp = session
            .submit("fun add(a: int, b: int): int = a + b")
            .expect("submit");

        match resp {
            ReplResponse::Definition(update) => {
                assert_eq!(update.total_definitions, 1);
            }
            ReplResponse::Evaluated(_) => panic!("expected definition update"),
        }
        assert!(session.source().contains("fun add"));
    }

    #[test]
    fn expression_submissions_evaluate_without_modifying_session() {
        let parser = DynamicParser {
            seen: RefCell::new(Vec::new()),
        };
        let emitter = FakeEmitter {
            events: Rc::new(RefCell::new(Vec::new())),
            ir: "define i32 @main()".into(),
            fail: None,
        };
        let runner = FakeRunner {
            events: Rc::new(RefCell::new(Vec::new())),
            output: "3\n".into(),
            fail: None,
        };

        let mut session = ReplSession::new(parser, emitter, runner, Strictness::Strict);
        session
            .submit_definition("fun add(a: int, b: int): int = a + b")
            .expect("def");

        let initial_src = session.source().to_string();
        let resp = session.submit("1 + 2").expect("eval expr");

        match resp {
            ReplResponse::Evaluated(exec) => {
                assert_eq!(exec.stdout, "3\n");
                assert!(exec.success);
            }
            ReplResponse::Definition(_) => panic!("expected evaluated expression"),
        }

        // Session source is unchanged
        assert_eq!(session.source(), initial_src);
    }

    #[test]
    fn syntax_errors_preserve_session_transactionality() {
        let parser = DynamicParser {
            seen: RefCell::new(Vec::new()),
        };
        let emitter = FakeEmitter {
            events: Rc::new(RefCell::new(Vec::new())),
            ir: "".into(),
            fail: None,
        };
        let runner = FakeRunner {
            events: Rc::new(RefCell::new(Vec::new())),
            output: "".into(),
            fail: None,
        };

        let mut session = ReplSession::new(parser, emitter, runner, Strictness::Strict);
        session.submit_definition("fun valid(): int = 1").expect("ok");
        let valid_source = session.source().to_string();

        assert!(session.submit("syntax_err").is_err());
        assert_eq!(session.source(), valid_source);
    }

    #[test]
    fn reset_clears_the_environment() {
        let parser = DynamicParser {
            seen: RefCell::new(Vec::new()),
        };
        let emitter = FakeEmitter {
            events: Rc::new(RefCell::new(Vec::new())),
            ir: "".into(),
            fail: None,
        };
        let runner = FakeRunner {
            events: Rc::new(RefCell::new(Vec::new())),
            output: "".into(),
            fail: None,
        };

        let mut session = ReplSession::new(parser, emitter, runner, Strictness::Strict);
        session.submit_definition("fun a(): int = 1").expect("ok");
        assert!(!session.source().is_empty());

        session.reset();
        assert!(session.source().is_empty());
        assert!(session.program().defs().is_empty());
    }

    #[test]
    fn emission_failures_are_rejected_immediately_without_poisoning_session() {
        let parser = DynamicParser {
            seen: RefCell::new(Vec::new()),
        };
        let emitter = FakeEmitter {
            events: Rc::new(RefCell::new(Vec::new())),
            ir: "".into(),
            fail: Some(CompileError::emit("unbound variable `x`")),
        };
        let runner = FakeRunner {
            events: Rc::new(RefCell::new(Vec::new())),
            output: "".into(),
            fail: None,
        };

        let mut session = ReplSession::new(parser, emitter, runner, Strictness::Strict);
        let errs = session.submit("val () = x + x").unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].message().contains("unbound variable `x`"));
        assert!(session.source().is_empty());
    }
}