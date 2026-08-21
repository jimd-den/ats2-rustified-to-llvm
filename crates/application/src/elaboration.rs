//! Module-aware source elaboration.
//!
//! Parsing records what was written. Elaboration connects declarations to
//! implementations and produces definitions whose parameters and result types
//! are explicit before either checker or backend sees them.

use std::collections::HashMap;

use ats2_domain::ast::{Def, Expr, FunDecl, FunDef, Program};
use ats2_domain::errors::CompileError;

use crate::modules::ResolvedModules;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElaboratedProgram {
    program: Program,
}

impl ElaboratedProgram {
    pub fn program(&self) -> &Program {
        &self.program
    }

    pub fn into_program(self) -> Program {
        self.program
    }
}

pub fn elaborate(
    modules: ResolvedModules,
    ambient: &Program,
) -> Result<ElaboratedProgram, Vec<CompileError>> {
    let mut declarations: HashMap<String, Vec<FunDecl>> = HashMap::new();
    let module_declarations = modules
        .units
        .iter()
        .flat_map(|unit| unit.program.defs());
    for definition in ambient
        .defs()
        .iter()
        .chain(module_declarations)
        .chain(modules.program.defs())
    {
        if let Def::Extern(declaration) = definition {
            let candidates = declarations.entry(declaration.name.clone()).or_default();
            if !candidates.contains(declaration) {
                candidates.push(declaration.clone());
            }
        }
    }

    let mut definitions = Vec::with_capacity(modules.program.defs.len());
    for definition in modules.program.defs {
        let Def::Implement(implementation) = definition else {
            definitions.push(definition);
            continue;
        };

        // Entry points and template holes have language-defined signatures.
        // Template instances remain syntax until monomorphisation chooses the
        // concrete instance requested at a call site.
        if matches!(implementation.name.as_str(), "main" | "main0")
            || implementation.name.contains('$')
            || !implementation.ty_params.is_empty()
            || !implementation.instance.is_empty()
        {
            definitions.push(Def::Implement(implementation));
            continue;
        }

        let Some(candidates) = declarations.get(&implementation.name) else {
            return Err(vec![CompileError::emit(format!(
                "`{}` is implemented but never declared; add an `extern fun` for it",
                implementation.name
            ))]);
        };
        let declaration = candidates
            .iter()
            .find(|candidate| {
                candidate.params.len() == implementation.params.len()
                    && (candidate.ty_params.is_empty()
                        || candidate.ty_params.len() == implementation.ty_params.len())
            })
            .or_else(|| candidates.first())
            .expect("a declaration bucket is never empty");
        if declaration.proof || !declaration.ty_params.is_empty() {
            definitions.push(Def::Implement(implementation));
            continue;
        }
        let mut implementation = implementation;
        while implementation.params.len() < declaration.params.len() {
            let Expr::Lam(params, _, body) = implementation.body else {
                break;
            };
            implementation.params.extend(params);
            implementation.body = *body;
        }
        if declaration.params.len() != implementation.params.len() {
            return Err(vec![CompileError::emit(format!(
                "`{}` is declared with {} parameter(s) but implemented with {}",
                implementation.name,
                declaration.params.len(),
                implementation.params.len()
            ))]);
        }

        let params = implementation
            .params
            .iter()
            .zip(&declaration.params)
            .map(|(implementation, declaration)| ats2_domain::ast::Param {
                name: implementation.name.clone(),
                ty: declaration.ty.clone(),
                borrowed: implementation.borrowed || declaration.borrowed,
            })
            .collect();
        definitions.push(Def::Fun(FunDef {
            ty_params: Vec::new(),
            universals: declaration.universals.clone(),
            existentials: declaration.existentials.clone(),
            metric: Vec::new(),
            name: implementation.name,
            params,
            ret: implementation
                .ret
                .unwrap_or_else(|| declaration.ret.clone()),
            body: implementation.body,
            proof: false,
        }));
    }

    Ok(ElaboratedProgram {
        program: Program::new(definitions),
    })
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use ats2_domain::ast::{Expr, FunDecl, ImplementDef, Param, Ty};

    use super::*;
    use crate::modules::ResolvedUnit;

    fn parameter(name: &str, ty: &str) -> Param {
        Param {
            name: name.into(),
            ty: Ty::Name(ty.into()),
            borrowed: false,
        }
    }

    fn declaration() -> FunDecl {
        FunDecl {
            name: "answer".into(),
            linear: false,
            proof: false,
            ty_params: Vec::new(),
            universals: Vec::new(),
            existentials: Vec::new(),
            params: vec![parameter("_", "int")],
            ret: Ty::Name("int".into()),
        }
    }

    #[test]
    fn an_implementation_inherits_its_declarations_types() {
        let implementation = ImplementDef {
            ty_params: Vec::new(),
            instance: Vec::new(),
            name: "answer".into(),
            params: vec![parameter("n", "_")],
            ret: None,
            body: Expr::Var("n".into()),
        };
        let modules = ResolvedModules::single(Program::new(vec![
            Def::Extern(declaration()),
            Def::Implement(implementation),
        ]));

        let program = elaborate(modules, &Program::new(Vec::new()))
            .expect("elaborate")
            .into_program();
        let Def::Fun(function) = &program.defs()[1] else {
            panic!("implementation was not materialized");
        };
        assert_eq!(function.params[0], parameter("n", "int"));
        assert_eq!(function.ret, Ty::Name("int".into()));
    }

    #[test]
    fn templates_are_left_for_monomorphisation() {
        let mut declaration = declaration();
        declaration.ty_params.push("a".into());
        let implementation = ImplementDef {
            ty_params: vec!["a".into()],
            instance: Vec::new(),
            name: "answer".into(),
            params: vec![parameter("n", "a")],
            ret: None,
            body: Expr::Var("n".into()),
        };
        let modules = ResolvedModules::single(Program::new(vec![
            Def::Extern(declaration),
            Def::Implement(implementation.clone()),
        ]));

        let program = elaborate(modules, &Program::new(Vec::new()))
            .expect("elaborate")
            .into_program();
        assert_eq!(program.defs()[1], Def::Implement(implementation));
    }

    #[test]
    fn declarations_are_indexed_from_resolved_units_not_only_the_flat_projection() {
        let implementation = ImplementDef {
            ty_params: Vec::new(),
            instance: Vec::new(),
            name: "answer".into(),
            params: vec![parameter("n", "_")],
            ret: None,
            body: Expr::Var("n".into()),
        };
        let modules = ResolvedModules {
            root: PathBuf::from("main.dats"),
            units: vec![ResolvedUnit {
                path: PathBuf::from("answer.sats"),
                program: Program::new(vec![Def::Extern(declaration())]),
            }],
            edges: Vec::new(),
            program: Program::new(vec![Def::Implement(implementation)]),
        };

        let program = elaborate(modules, &Program::new(Vec::new()))
            .expect("elaborate")
            .into_program();
        let Def::Fun(function) = &program.defs()[0] else {
            panic!("implementation was not materialized");
        };
        assert_eq!(function.params[0], parameter("n", "int"));
        assert_eq!(function.ret, Ty::Name("int".into()));
    }

    #[test]
    fn a_curried_implementation_supplies_remaining_parameters_with_a_lambda() {
        let declaration = FunDecl {
            name: "method".into(),
            linear: false,
            proof: false,
            ty_params: Vec::new(),
            universals: Vec::new(),
            existentials: Vec::new(),
            params: vec![parameter("_", "int"), parameter("_", "bool")],
            ret: Ty::Name("int".into()),
        };
        let implementation = ImplementDef {
            ty_params: Vec::new(),
            instance: Vec::new(),
            name: "method".into(),
            params: vec![parameter("receiver", "_")],
            ret: None,
            body: Expr::Lam(
                vec![parameter("predicate", "_")],
                None,
                Box::new(Expr::IntLit(1)),
            ),
        };
        let modules = ResolvedModules::single(Program::new(vec![
            Def::Extern(declaration),
            Def::Implement(implementation),
        ]));

        let program = elaborate(modules, &Program::new(Vec::new()))
            .expect("elaborate")
            .into_program();
        let Def::Fun(function) = &program.defs()[1] else {
            panic!("implementation was not materialized");
        };
        assert_eq!(
            function.params,
            vec![parameter("receiver", "int"), parameter("predicate", "bool")]
        );
        assert_eq!(function.body, Expr::IntLit(1));
    }
}
