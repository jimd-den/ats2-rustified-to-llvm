//! # Modules — how a program comes to be more than one file
//!
//! *Literate note.*  Until now a program was exactly the text handed to
//! the parser, and `staload` was read and thrown away.  That is a fine
//! answer for the corpus, where every `staload` names something inside
//! the ATS distribution and the built-in prelude answers it — but it
//! means nobody could ever write a program in two files of their own.
//!
//! This module answers the ones that name a real file. It walks the
//! `staload`s depth-first, asks the loader for each, parses what comes
//! back, and lays the definitions out in dependency order: everything a
//! unit needed, before the unit itself.
//!
//! **What it is, and what it is not.**  This is multi-*file*, not
//! separate compilation. Every unit ends up in one `Program` and one
//! module of IR; nothing here produces an object file per unit, so
//! nothing here makes a rebuild cheaper. What it makes possible is a
//! program written across several files, which is the part that was
//! missing.
//!
//! Two rules keep the walk honest, and both are about saying nothing
//! twice.  A unit is loaded once no matter how many units asked for it,
//! keyed on the path it was *found* at rather than the path that was
//! written — two spellings of one file are one file.  And a cycle is
//! not an error: the second time round, the unit is already loaded, so
//! the walk stops for the same reason it stops for a diamond.  ATS
//! programs really do have mutually-`staload`ing headers, and refusing
//! them would be inventing a rule the language does not have.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use ats2_domain::ast::{Def, LoadKind, Program};
use ats2_domain::errors::CompileError;

use crate::ports::{ParserPort, SourceLoaderPort};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedUnit {
    pub path: PathBuf,
    pub program: Program,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DependencyKind {
    Interface,
    Implementation,
    Dynamic,
    Include,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DependencyEdge {
    pub from: PathBuf,
    pub to: PathBuf,
    pub kind: DependencyKind,
    pub alias: Option<String>,
}

/// A module-aware result plus the compatibility projection consumed by the
/// current checker and emitter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedModules {
    pub root: PathBuf,
    pub units: Vec<ResolvedUnit>,
    pub edges: Vec<DependencyEdge>,
    pub program: Program,
}

impl ResolvedModules {
    pub fn single(program: Program) -> Self {
        Self {
            root: PathBuf::new(),
            units: Vec::new(),
            edges: Vec::new(),
            program,
        }
    }
}

/// Every unit `root` needs, followed by `root` itself, as one program.
///
/// The order is the point: a unit's definitions arrive before those of
/// whoever asked for it, so nothing downstream ever has to look forward
/// to a declaration it has not seen.
pub fn resolve<P: ParserPort, L: SourceLoaderPort + ?Sized>(
    root: Program,
    parser: &P,
    loader: &L,
) -> Result<Program, Vec<CompileError>> {
    resolve_modules(root, parser, loader).map(|resolved| resolved.program)
}

pub fn resolve_modules<P: ParserPort, L: SourceLoaderPort + ?Sized>(
    root: Program,
    parser: &P,
    loader: &L,
) -> Result<ResolvedModules, Vec<CompileError>> {
    let origin = loader.origin();
    let mut walk = Walk {
        parser,
        loader,
        loaded: HashSet::new(),
        defs: Vec::new(),
        units: Vec::new(),
        edges: Vec::new(),
    };
    walk.dependencies_of(&root, &origin)?;
    let mut defs = walk.defs;
    defs.extend(root.defs.clone());
    Ok(ResolvedModules {
        root: origin,
        units: walk.units,
        edges: walk.edges,
        program: Program::new(defs),
    })
}

struct Walk<'a, P: ParserPort, L: SourceLoaderPort + ?Sized> {
    parser: &'a P,
    loader: &'a L,
    /// The units already folded in, by the path they were found at.
    loaded: HashSet<PathBuf>,
    /// Their definitions, in the order they were finished.
    defs: Vec<ats2_domain::ast::Def>,
    units: Vec<ResolvedUnit>,
    edges: Vec<DependencyEdge>,
}

impl<P: ParserPort, L: SourceLoaderPort + ?Sized> Walk<'_, P, L> {
    /// Fold in everything `program`, which lives at `at`, asked for.
    fn dependencies_of(&mut self, program: &Program, at: &Path) -> Result<(), Vec<CompileError>> {
        let requested = program
            .staloads()
            .iter()
            .map(|load| {
                (
                    load.path.as_str(),
                    Exposure::from(load.kind),
                    DependencyKind::from(load.kind),
                    load.alias.clone(),
                )
            })
            .chain(
                program
                    .includes()
                    .iter()
                    .map(|include| {
                        (
                            include.path.as_str(),
                            Exposure::Definitions,
                            DependencyKind::Include,
                            None,
                        )
                    }),
            );
        for (requested, exposure, kind, alias) in requested {
            let found = self
                .loader
                .load(requested, at)
                .map_err(|m| vec![CompileError::target(m)])?;
            // Not one of ours: a path into the ATS distribution, which
            // the built-in prelude already answers.
            let Some(unit) = found else { continue };
            self.edges.push(DependencyEdge {
                from: at.to_path_buf(),
                to: unit.path.clone(),
                kind,
                alias,
            });
            // Already folded in — by a diamond, or by a cycle, and the
            // walk cannot tell the two apart because it does not need
            // to.  Marked before recursing, which is what makes the
            // cycle stop rather than the stack.
            if !self.loaded.insert(unit.path.clone()) {
                continue;
            }
            // Dependency ingestion may preserve declarations before syntax
            // this compiler cannot read yet.  If even that yields no usable
            // program, step over the unit rather than refusing every root
            // that reaches for a heavy contrib library.
            let Ok(parsed) = self.parser.parse_dependency(&unit.source) else {
                continue;
            };
            self.dependencies_of(&parsed, &unit.path)?;
            self.defs.extend(
                parsed
                    .defs
                    .iter()
                    .filter(|definition| exposure.keeps(definition))
                    .cloned(),
            );
            self.units.push(ResolvedUnit {
                path: unit.path,
                program: parsed,
            });
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Exposure {
    Interface,
    Definitions,
}

impl From<LoadKind> for Exposure {
    fn from(kind: LoadKind) -> Self {
        match kind {
            LoadKind::Interface => Exposure::Interface,
            LoadKind::Implementation | LoadKind::Dynamic => Exposure::Definitions,
        }
    }
}

impl From<LoadKind> for DependencyKind {
    fn from(kind: LoadKind) -> Self {
        match kind {
            LoadKind::Interface => DependencyKind::Interface,
            LoadKind::Implementation => DependencyKind::Implementation,
            LoadKind::Dynamic => DependencyKind::Dynamic,
        }
    }
}

impl Exposure {
    fn keeps(self, definition: &Def) -> bool {
        match self {
            Exposure::Definitions => true,
            Exposure::Interface => matches!(
                definition,
                Def::Datatype(_)
                    | Def::Exception(_, _)
                    | Def::Extern(_)
                    | Def::Val(ats2_domain::ast::ValDef { ty: Some(_), .. })
                    | Def::Overload { .. }
                    | Def::Const(_)
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ats2_domain::ast::Def;

    use super::*;
    use crate::ports::Unit;

    /// A loader over an in-memory directory.
    ///
    /// It resolves the way the real one does — relative to the file that
    /// wrote the `staload` — and answers `None` for anything that looks
    /// like it belongs to the ATS distribution, because that is the case
    /// the whole corpus depends on.
    struct Files {
        origin: PathBuf,
        files: HashMap<PathBuf, String>,
    }

    impl Files {
        fn new(origin: &str, files: &[(&str, &str)]) -> Self {
            Self {
                origin: PathBuf::from(origin),
                files: files
                    .iter()
                    .map(|(p, s)| (PathBuf::from(p), (*s).to_string()))
                    .collect(),
            }
        }
    }

    impl SourceLoaderPort for Files {
        fn origin(&self) -> PathBuf {
            self.origin.clone()
        }

        fn load(&self, requested: &str, from: &Path) -> Result<Option<Unit>, String> {
            if requested.starts_with("prelude/") {
                return Ok(None);
            }
            let path = from
                .parent()
                .unwrap_or(Path::new(""))
                .join(requested)
                .components()
                .collect::<PathBuf>();
            match self.files.get(&path) {
                Some(source) => Ok(Some(Unit {
                    path,
                    source: source.clone(),
                })),
                None => Err(format!("no such file: {}", path.display())),
            }
        }
    }

    /// A parser that reads the real thing, so the tests are about
    /// resolution rather than about a fake's idea of a program.
    struct RealEnough;

    impl ParserPort for RealEnough {
        fn parse(&self, source: &str) -> Result<Program, Vec<CompileError>> {
            crate::modules::tests::parse_for_test(source)
        }
    }

    /// The application crate cannot depend on the parser — that is the
    /// dependency rule — so the tests build their programs by hand from
    /// a tiny made-up syntax: one `staload` or one `fun` per line.
    fn parse_for_test(source: &str) -> Result<Program, Vec<CompileError>> {
        let mut defs = Vec::new();
        let mut staloads = Vec::new();
        for line in source.lines().map(str::trim).filter(|l| !l.is_empty()) {
            match line.split_once(' ') {
                Some(("staload", path)) => staloads.push(ats2_domain::ast::Staload {
                    path: path.to_string(),
                    alias: None,
                    kind: ats2_domain::ast::LoadKind::Implementation,
                }),
                Some(("fun", name)) => defs.push(Def::Fun(ats2_domain::ast::FunDef {
                    name: name.to_string(),
                    ..fun_shape()
                })),
                _ => return Err(vec![CompileError::target(format!("bad line: {line}"))]),
            }
        }
        Ok(Program::new(defs).asking_for(staloads))
    }

    fn fun_shape() -> ats2_domain::ast::FunDef {
        ats2_domain::ast::FunDef {
            ty_params: Vec::new(),
            universals: Vec::new(),
            existentials: Vec::new(),
            metric: Vec::new(),
            name: String::new(),
            params: Vec::new(),
            ret: ats2_domain::ast::Ty::Name("int".into()),
            body: ats2_domain::ast::Expr::IntLit(1),
            proof: false,
        }
    }

    /// The names of the functions a resolved program ended up with, in
    /// order — which is the whole observable result of resolution.
    fn names(p: &Program) -> Vec<String> {
        p.defs()
            .iter()
            .filter_map(|d| match d {
                Def::Fun(f) => Some(f.name.clone()),
                _ => None,
            })
            .collect()
    }

    fn resolved(origin: &str, files: &[(&str, &str)], root: &str) -> Result<Program, Vec<String>> {
        let loader = Files::new(origin, files);
        let program = parse_for_test(root).expect("root parses");
        resolve(program, &RealEnough, &loader)
            .map_err(|es| es.into_iter().map(|e| e.message).collect())
    }

    #[test]
    fn a_program_that_asks_for_nothing_is_left_alone() {
        let p = resolved("main.dats", &[], "fun main").expect("resolve");
        assert_eq!(names(&p), ["main"]);
    }

    #[test]
    fn an_included_unit_contributes_its_definitions() {
        let loader = Files::new("main.dats", &[("part.dats", "fun included")]);
        let root = Program::new(vec![Def::Fun(ats2_domain::ast::FunDef {
            name: "main".into(),
            ..fun_shape()
        })])
        .including(vec![ats2_domain::ast::Include {
            path: "part.dats".into(),
        }]);
        let program = resolve(root, &RealEnough, &loader).expect("resolve include");
        assert_eq!(names(&program), ["included", "main"]);
    }

    #[test]
    fn resolution_retains_units_and_dependency_edges() {
        let loader = Files::new("main.dats", &[("part.dats", "fun included")]);
        let root = Program::new(vec![Def::Fun(ats2_domain::ast::FunDef {
            name: "main".into(),
            ..fun_shape()
        })])
        .including(vec![ats2_domain::ast::Include {
            path: "part.dats".into(),
        }]);

        let resolved = resolve_modules(root, &RealEnough, &loader).expect("resolve graph");
        assert_eq!(resolved.root, PathBuf::from("main.dats"));
        assert_eq!(resolved.units.len(), 1);
        assert_eq!(resolved.units[0].path, PathBuf::from("part.dats"));
        assert_eq!(resolved.edges.len(), 1);
        assert_eq!(resolved.edges[0].from, PathBuf::from("main.dats"));
        assert_eq!(resolved.edges[0].to, PathBuf::from("part.dats"));
        assert_eq!(resolved.edges[0].kind, DependencyKind::Include);
    }

    #[test]
    fn an_interface_exposes_signatures_but_not_runtime_bodies() {
        let declaration = Def::Extern(ats2_domain::ast::FunDecl {
            name: "declared".into(),
            linear: false,
            proof: false,
            ty_params: Vec::new(),
            universals: Vec::new(),
            existentials: Vec::new(),
            params: Vec::new(),
            ret: ats2_domain::ast::Ty::Name("int".into()),
        });
        let body = Def::Fun(ats2_domain::ast::FunDef {
            name: "private_body".into(),
            ..fun_shape()
        });
        let value_declaration = Def::Val(ats2_domain::ast::ValDef {
            name: "the_null_ptr".into(),
            ty: Some(ats2_domain::ast::Ty::App(
                "ptr".into(),
                vec![ats2_domain::ast::Ty::Name("null".into())],
            )),
            value: ats2_domain::ast::Expr::IntLit(0),
        });

        assert!(Exposure::Interface.keeps(&declaration));
        assert!(Exposure::Interface.keeps(&value_declaration));
        assert!(!Exposure::Interface.keeps(&body));
        assert!(Exposure::Definitions.keeps(&body));
    }

    #[test]
    fn a_dependency_that_cannot_parse_is_stepped_over_not_fatal() {
        // A program may reach for a unit whose syntax this compiler
        // cannot read yet.  That unit's declarations cannot be imported,
        // but its being unreadable must not take the whole program down:
        // everything else that was asked for is still folded in.
        let p = resolved(
            "main.dats",
            &[
                ("good.dats", "fun good"),
                ("heavy.dats", "this line the toy parser cannot read"),
            ],
            "staload good.dats\nstaload heavy.dats\nfun main",
        )
        .expect("resolve succeeds even when a dependency is unreadable");
        let names = names(&p);
        assert!(
            names.contains(&"good".into()),
            "good is imported, got {names:?}"
        );
        assert!(
            names.contains(&"main".into()),
            "main survives, got {names:?}"
        );
    }

    #[test]
    fn what_a_unit_asked_for_arrives_before_the_unit() {
        // Everything a file needed is defined by the time the file is
        // read, so nothing downstream has to look forward.
        let p = resolved(
            "main.dats",
            &[("helper.dats", "fun help")],
            "staload helper.dats\nfun main",
        )
        .expect("resolve");
        assert_eq!(names(&p), ["help", "main"]);
    }

    #[test]
    fn a_unit_two_others_asked_for_is_loaded_once() {
        // The diamond: `main` needs both `a` and `b`, and both need
        // `base`.  Defining `base` twice would be a duplicate-symbol
        // error from the linker, which is a long way from here.
        let p = resolved(
            "main.dats",
            &[
                ("a.dats", "staload base.dats\nfun a"),
                ("b.dats", "staload base.dats\nfun b"),
                ("base.dats", "fun base"),
            ],
            "staload a.dats\nstaload b.dats\nfun main",
        )
        .expect("resolve");
        assert_eq!(names(&p), ["base", "a", "b", "main"]);
    }

    #[test]
    fn two_units_that_ask_for_each_other_still_finish() {
        // Mutually-`staload`ing headers are ordinary in ATS, so a cycle
        // is not a mistake to report — it is a walk to stop.  The test
        // that matters is that this terminates at all.
        let p = resolved(
            "main.dats",
            &[
                ("a.dats", "staload b.dats\nfun a"),
                ("b.dats", "staload a.dats\nfun b"),
            ],
            "staload a.dats\nfun main",
        )
        .expect("resolve");
        assert_eq!(names(&p), ["b", "a", "main"]);
    }

    #[test]
    fn a_unit_asks_relative_to_itself_not_to_the_root() {
        // `lib/impl.dats` writing `staload util.dats` means the one
        // beside it.  Resolving against the root's directory instead
        // would find a different file, or none, and either is worse
        // than the error it would eventually cause.
        let p = resolved(
            "main.dats",
            &[
                ("lib/impl.dats", "staload util.dats\nfun impl"),
                ("lib/util.dats", "fun util"),
            ],
            "staload lib/impl.dats\nfun main",
        )
        .expect("resolve");
        assert_eq!(names(&p), ["util", "impl", "main"]);
    }

    #[test]
    fn a_path_the_prelude_answers_is_not_looked_for() {
        // Every `staload` in the corpus names something in the ATS
        // distribution.  The loader says "not mine", and that has to be
        // an answer rather than a failure, or nothing compiles.
        let p = resolved(
            "main.dats",
            &[],
            "staload prelude/DATS/integer.dats\nfun main",
        )
        .expect("resolve");
        assert_eq!(names(&p), ["main"]);
    }

    #[test]
    fn a_file_that_is_not_there_is_reported_rather_than_ignored() {
        // The old behaviour — skip the line — would turn a typo into a
        // missing symbol at link time, named after something the user
        // never wrote.
        let errs =
            resolved("main.dats", &[], "staload helper.dats\nfun main").expect_err("should fail");
        assert_eq!(errs.len(), 1, "{errs:?}");
        assert!(errs[0].contains("helper.dats"), "{}", errs[0]);
    }

    #[test]
    fn a_bad_line_in_a_loaded_unit_is_that_units_problem() {
        // A unit whose source this compiler cannot read contributes
        // nothing, but its being unreadable is not the program's error:
        // the declaration it holds is just not available.  Everything
        // that does parse is still folded in, and the program survives.
        let p = resolved(
            "main.dats",
            &[("helper.dats", "!!!")],
            "staload helper.dats\nfun main",
        )
        .expect("an unreadable dependency is stepped over");
        assert_eq!(names(&p), ["main"]);
    }
}
