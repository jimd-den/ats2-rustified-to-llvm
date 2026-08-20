//! # Use cases — the application's executable business rules
//!
//! *Literate note.*  A use case is one complete, named conversation with
//! the outside world: "parse this source", "compile this source to LLVM
//! IR", "build an executable from this source".  Each use case is a tiny
//! orchestrator: it calls the ports in the right order, translates port
//! failures into domain errors, and returns domain values.  There is no
//! I/O here and no policy about files — the use cases only know that
//! sources, programs, and IR texts flow through the seams the ports
//! declare.

pub mod compile_executable;
pub mod compile_to_ir;
pub mod parse;

pub use compile_executable::CompileExecutableUseCase;
pub use compile_to_ir::CompileToIrUseCase;
pub use parse::ParseUseCase;

/// Test doubles shared by every use-case test module.
///
/// Each fake records every port call into an `Rc<RefCell<Vec<String>>>`
/// event log, which lets the tests assert not only *what* happened but
/// *in what order* — the orchestration contract of the use cases.
#[cfg(test)]
pub(crate) mod fakes {
    use std::cell::RefCell;
    use std::path::Path;
    use std::rc::Rc;

    use ats2_domain::ast::{Def, Expr, FunDef, Program, Ty};
    use ats2_domain::errors::CompileError;

    use crate::ports::{LlvmEmitterPort, OutputPort, ParserPort, ToolchainPort};

    /// The minimal program the fakes hand out as "parsed".
    pub fn canned_program() -> Program {
        Program::new(vec![Def::Fun(FunDef {
            universals: vec![],
            existentials: vec![],
            metric: vec![],
            ty_params: vec![],
            name: "f".into(),
            params: vec![],
            ret: Ty::Name("int".into()),
            body: Expr::IntLit(1),
            proof: false,
        })])
    }

    pub struct FakeParser {
        pub events: Rc<RefCell<Vec<String>>>,
        pub fail: Option<Vec<CompileError>>,
    }

    impl ParserPort for FakeParser {
        fn parse(&self, source: &str) -> Result<Program, Vec<CompileError>> {
            self.events.borrow_mut().push(format!("parse:{source}"));
            match &self.fail {
                Some(errors) => Err(errors.clone()),
                None => Ok(canned_program()),
            }
        }
    }

    pub struct FakeEmitter {
        pub events: Rc<RefCell<Vec<String>>>,
        pub ir: String,
        pub fail: Option<CompileError>,
    }

    impl LlvmEmitterPort for FakeEmitter {
        fn emit(&self, program: &Program) -> Result<String, CompileError> {
            self.events
                .borrow_mut()
                .push(format!("emit:{}", program.defs().len()));
            match &self.fail {
                Some(err) => Err(err.clone()),
                None => Ok(self.ir.clone()),
            }
        }
    }

    pub struct FakeOutput {
        pub events: Rc<RefCell<Vec<String>>>,
        pub fail: bool,
    }

    impl OutputPort for FakeOutput {
        fn write(&self, path: &Path, contents: &str) -> Result<(), String> {
            self.events
                .borrow_mut()
                .push(format!("write:{}:{}", path.display(), contents.len()));
            if self.fail {
                Err("disk full".into())
            } else {
                Ok(())
            }
        }
    }

    pub struct FakeToolchain {
        pub events: Rc<RefCell<Vec<String>>>,
        pub fail: bool,
    }

    impl ToolchainPort for FakeToolchain {
        fn link_all(&self, inputs: &[std::path::PathBuf], output: &Path) -> Result<(), String> {
            let listed: Vec<String> = inputs.iter().map(|i| i.display().to_string()).collect();
            self.events.borrow_mut().push(format!(
                "link:{}:{}",
                listed.join(","),
                output.display()
            ));
            if self.fail {
                Err("clang failed".into())
            } else {
                Ok(())
            }
        }
    }
}
