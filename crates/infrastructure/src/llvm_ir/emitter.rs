use super::builder::*;
use super::types::*;
use ats2_domain::ast::*;
use ats2_domain::errors::CompileError;
use ats2_domain::tokens::*;
use std::collections::{HashMap, HashSet};

pub struct LlvmIrEmitter;

impl LlvmIrEmitter {
    /// Lower a program to textual LLVM IR.
    pub fn emit(program: &Program) -> Result<String, CompileError> {
        // Two source-level constructs have no counterpart in LLVM and are
        // removed before anything else looks at the program.  Templates go
        // first: expanding one produces ordinary functions, and those may
        // themselves contain the nested functions lifting deals with.
        // The prelude supplies the declarations every ATS program assumes
        // it has.  It comes first so that inference and expansion see one
        // program, with no notion of where a declaration came from.
        // The static language stops here.  A `praxi`, a `prfun` and each
        // constructor of a `dataprop` declare something with no body, no
        // symbol and no bits, whose result type — `FACT(n, r)` — is not a
        // type any machine has.  They are dropped before anything else
        // looks at the program, because every stage after this one is
        // about what runs.
        let program = &without_proofs(program);
        let program = &with_prelude(program)?;
        // Naming the instance a bare template call means needs the types
        // of its arguments, so inference runs before expansion.
        let program = &crate::infer::Inferencer::resolve(program)?;
        let program = &crate::mono::Monomorphiser::expand(program)?;
        let program = &crate::lift::Lifter::lift(program)?;
        let registry = registry_of(program)?;
        let mut module = ModuleBuilder::new();
        for def in &program.defs {
            match def {
                // Not this compiler's language; the toolchain reads it.
                Def::InlineC(_) => {}
                Def::Exception(_, _) => {}
                Def::Fun(f) => emit_function(f, &registry, &mut module)?,
                Def::Implement(im) if im.name == "main0" || im.name == "main" => {
                    // The initializers run first, in the order they were
                    // written, so a value may be defined in terms of one
                    // above it.
                    let inits: Vec<&ats2_domain::ast::ValDef> = program
                        .defs
                        .iter()
                        .filter_map(|d| match d {
                            Def::Val(v) => Some(v),
                            _ => None,
                        })
                        .collect();
                    emit_main(im, &inits, &registry, &mut module)?
                }
                // A template hole is inlined where it is used, so it
                // emits no function of its own.
                Def::Implement(im) if im.name.contains('$') => {}
                // An `implement` of a declared function is that function.
                Def::Implement(im) => {
                    let sig = registry.fns[&im.name].clone();
                    let params = im
                        .params
                        .iter()
                        .zip(&sig.params)
                        .map(|(p, ty)| Param {
                            borrowed: false,
                            name: p.name.clone(),
                            ty: ty_for(*ty),
                        })
                        .collect();
                    let f = ats2_domain::ast::FunDef {
                        metric: Vec::new(),
                        ty_params: im.ty_params.clone(),
                        // An `implement` inherits the declaration's
                        // quantifiers; nothing here re-states them.
                        universals: vec![],
                        existentials: vec![],
                        name: im.name.clone(),
                        params,
                        ret: im.ret.clone().unwrap_or_else(|| ty_for(sig.ret)),
                        body: im.body.clone(),
                        // An `implement` fills in a function, never a proof.
                        proof: false,
                    };
                    emit_function(&f, &registry, &mut module)?
                }
                Def::Datatype(d) => module.lines.push(format!("; datatype {}", d.name)),
                // A constant is substituted at every use site, so it
                // contributes a comment and nothing else.
                Def::Const(c) => module.lines.push(format!("; #define {}", c.name)),
                // A declaration promises a definition elsewhere; only the
                // definition emits anything.
                Def::Extern(d) => module.lines.push(format!("; extern {}", d.name)),
                Def::Overload { op, func } => {
                    module.lines.push(format!("; overload {op} with {func}"))
                }
                // The storage is declared here; the value is computed in
                // `main`, in the order the program wrote them.
                Def::Val(v) if v.name.starts_with(crate::parser::TOPLEVEL_STATEMENT) => {
                    let has_main = program.defs.iter().any(|d| match d {
                        Def::Implement(im) => im.name == "main0" || im.name == "main",
                        _ => false,
                    });
                    if !has_main {
                        let mut fb = FnBuilder::new();
                        LlvmIrEmitter.emit_expr(&v.value, &mut fb, &registry, &mut module)?;
                    }
                }
                Def::Val(v) => {
                    let ty = registry.globals[&v.name];
                    let has_main = program.defs.iter().any(|d| match d {
                        Def::Implement(im) => im.name == "main0" || im.name == "main",
                        _ => false,
                    });
                    if !has_main {
                        let mut fb = FnBuilder::new();
                        let val = LlvmIrEmitter.emit_expr_expecting(
                            &v.value,
                            Some(ty),
                            &mut fb,
                            &registry,
                            &mut module,
                        )?;
                        if val.ty != ty {
                            return Err(CompileError::emit(format!(
                                "`{}` is declared as {} but its value is {}",
                                v.name,
                                llvm_ty_str(ty),
                                llvm_ty_str(val.ty)
                            )));
                        }
                    }
                    module.globals.push(format!(
                        "@{} = internal global {} {}",
                        sanitize(&v.name),
                        llvm_ty_str(ty),
                        zero_literal(ty)
                    ));
                }
            }
        }
        Ok(module.render())
    }
}

/// Prepend the prelude declarations the program did not make for itself.
///
/// A program that declares its own `list0` keeps it: the prelude fills
/// gaps rather than shadowing.  Anything unused is dropped later, since
/// datatypes are only instantiated on demand.
pub(crate) fn with_prelude(program: &Program) -> Result<Program, CompileError> {
    let prelude = crate::parser::Parser::parse(crate::prelude::PRELUDE_SOURCE).map_err(|e| {
        CompileError::emit(format!("the built-in prelude does not parse: {}", e[0]))
    })?;

    // A name the program defines for itself is the program's; the prelude
    // only fills gaps.
    //
    // An `implement` does not define a name — it supplies a *body* for
    // one declared elsewhere, and that elsewhere is often the prelude.
    // Counting it here would take the declaration away and leave the
    // body with nothing to be the body of, which is exactly what a
    // program adding its own `fprint_val<t>` does.
    let own: std::collections::HashSet<String> = program
        .defs
        .iter()
        .filter(|d| !matches!(d, Def::Implement(_)))
        .filter_map(def_name)
        .collect();

    // Which prelude definitions are actually wanted?  Start from the names
    // the program mentions, and keep going: a prelude function may call
    // another, and `fileref_get_lines_stringlst` needs the list datatype
    // that only it mentions.  The fixpoint is what keeps an unused prelude
    // from costing anything.
    let mut wanted: std::collections::HashSet<String> = std::collections::HashSet::new();
    collect_names(&program.defs, &mut wanted);
    loop {
        let mut added = false;
        for def in &prelude.defs {
            let Some(name) = def_name(def) else { continue };
            if own.contains(&name) || !wanted.contains(&name) {
                continue;
            }
            let before = wanted.len();
            collect_names(std::slice::from_ref(def), &mut wanted);
            if wanted.len() != before {
                added = true;
            }
        }
        if !added {
            break;
        }
    }

    let mut defs: Vec<Def> = prelude
        .defs
        .iter()
        .filter(|d| match def_name(d) {
            // A datatype is always available: it emits nothing unless a
            // program actually instantiates it.
            None => true,
            Some(name) => {
                !own.contains(&name) && (wanted.contains(&name) || matches!(d, Def::Datatype(_)))
            }
        })
        .cloned()
        .collect();
    defs.extend(program.defs.iter().cloned());
    Ok(Program::new(defs))
}

/// The type of a top-level `val`'s initializer, where it can be read off
/// the expression without evaluating it.
pub(crate) fn global_type_of(expr: &Expr, registry: &Registry) -> Option<LlvmType> {
    match expr {
        Expr::IntLit(_) => Some(LlvmType::I64),
        Expr::BoolLit(_) => Some(LlvmType::I1),
        Expr::StrLit(_) => Some(LlvmType::I8Ptr),
        Expr::CharLit(_) => Some(LlvmType::I8),
        Expr::FloatLit(_) => Some(LlvmType::F64),
        Expr::UnaryNeg(_) => Some(LlvmType::I64),
        Expr::BinOp(op, l, _) => {
            if op.is_comparison() {
                Some(LlvmType::I1)
            } else {
                global_type_of(l, registry)
            }
        }
        Expr::Var(n) => registry.globals.get(n).copied(),
        // `'{ sing= ..., isemp= ... }` — a record of functions, which is
        // how ATS passes a module around.  Its type is read off its
        // fields, in the order they are written.
        Expr::RecordLit(fields) => {
            let parts: Option<Vec<(String, LlvmType)>> = fields
                .iter()
                .map(|(n, v)| Some((n.clone(), global_type_of(v, registry)?)))
                .collect();
            Some(LlvmType::Record(registry.intern_record(parts?)))
        }
        // `setmod_int.sing` — one field of a record global.
        Expr::Field(base, name) => {
            let LlvmType::Record(index) = global_type_of(base, registry)? else {
                return None;
            };
            registry
                .record_fields(index)
                .into_iter()
                .find(|(n, _)| n == name)
                .map(|(_, t)| t)
        }
        Expr::Call(callee, args) => match &**callee {
            // `setmod_int.sing (0)` — applying a field means the type it
            // returns, which its closure signature says.
            Expr::Field(..) => match global_type_of(callee, registry)? {
                LlvmType::Closure(i) => Some(registry.closure_sig(i).ret),
                _ => None,
            },
            Expr::Var(n) | Expr::Inst(n, _) => {
                if matches!(n.as_str(), "ref" | "ref_make_elt" | "refc_make_elt") {
                    // A fresh cell holding the argument: its type is the
                    // one-slot tuple of the argument's type.
                    return global_type_of(args.first()?, registry)
                        .map(|t| LlvmType::Tuple(registry.intern_tuple(vec![t])));
                }
                if n == "ref_make_viewptr" {
                    // `ref_make_viewptr (pf | addr@ x)` hands back the cell
                    // `x` already is, so it has exactly `x`'s type.
                    return match args.first()? {
                        Expr::Call(c, a) if matches!(&**c, Expr::Var(m) if m == "addr@" || m == "view@" || m == "ptrof") => {
                            global_type_of(a.first()?, registry)
                        }
                        a => global_type_of(a, registry)
                            .map(|t| LlvmType::Tuple(registry.intern_tuple(vec![t]))),
                    };
                }
                registry.fns.get(n).map(|s| s.ret)
            }
            _ => None,
        },
        Expr::Lam(params, Some(ret), _) => {
            let ps = params
                .iter()
                .map(|p| llvm_type_in(&p.ty, registry))
                .collect::<Result<Vec<_>, _>>()
                .ok()?;
            let r = llvm_type_in(ret, registry).ok()?;
            Some(LlvmType::Closure(
                registry.intern_closure(FnSig { params: ps, ret: r }),
            ))
        }
        _ => None,
    }
}

/// The bit pattern a cell of this type starts out holding.
///
/// A global holds it before its initializer runs, and an uninitialized
/// `var` holds it until its first write.  Nothing observes either —
/// `main` writes every global before the program's own code runs, and
/// ATS's type system is what stops a `var` being read too early — but
/// LLVM requires a value, and the representation's own nothing is the
/// honest one.
pub(crate) fn zero_literal(ty: LlvmType) -> &'static str {
    match ty {
        LlvmType::F64 => "0.0",
        LlvmType::I1 => "false",
        LlvmType::I8Ptr
        | LlvmType::Argv
        | LlvmType::FileRef
        | LlvmType::Data(_)
        | LlvmType::Tuple(_)
        | LlvmType::Array(_)
        | LlvmType::Closure(_)
        | LlvmType::Lazy(_)
        | LlvmType::Record(_) => "null",
        _ => "0",
    }
}

/// The name a definition introduces, if it introduces one.
pub(crate) fn def_name(def: &Def) -> Option<String> {
    match def {
        // Not this compiler's language; the toolchain reads it.
        Def::InlineC(_) => None,
        Def::Exception(name, _) => Some(name.clone()),
        Def::Fun(f) => Some(f.name.clone()),
        Def::Extern(d) => Some(d.name.clone()),
        Def::Implement(im) => Some(im.name.clone()),
        Def::Datatype(d) => Some(d.name.clone()),
        Def::Const(c) => Some(c.name.clone()),
        Def::Val(v) => Some(v.name.clone()),
        Def::Overload { .. } => None,
    }
}

/// Every name these definitions mention, in types or in code.
pub(crate) fn collect_names(defs: &[Def], out: &mut std::collections::HashSet<String>) {
    for def in defs {
        match def {
            // Not this compiler's language; the toolchain reads it.
            Def::InlineC(_) => {}
            Def::Exception(_, payload) => {
                for t in payload {
                    collect_type_names(t, out);
                }
            }
            Def::Fun(f) => {
                for p in &f.params {
                    collect_type_names(&p.ty, out);
                }
                collect_type_names(&f.ret, out);
                collect_expr_names(&f.body, out);
            }
            Def::Implement(im) => {
                for p in &im.params {
                    collect_type_names(&p.ty, out);
                }
                collect_expr_names(&im.body, out);
            }
            Def::Extern(d) => {
                for p in &d.params {
                    collect_type_names(&p.ty, out);
                }
                collect_type_names(&d.ret, out);
            }
            Def::Datatype(d) => {
                for c in &d.ctors {
                    out.insert(c.name.clone());
                    for f in &c.fields {
                        collect_type_names(f, out);
                    }
                }
            }
            Def::Const(c) => collect_expr_names(&c.value, out),
            Def::Val(v) => {
                if let Some(t) = &v.ty {
                    collect_type_names(t, out);
                }
                collect_expr_names(&v.value, out);
            }
            Def::Overload { func, .. } => {
                out.insert(func.clone());
            }
        }
    }
}

pub(crate) fn collect_type_names(ty: &Ty, out: &mut std::collections::HashSet<String>) {
    match ty {
        // A proposition names nothing the emitter has to build.
        Ty::Proof(_, value) => collect_type_names(value, out),
        Ty::Name(n) => {
            out.insert(n.clone());
        }
        Ty::App(n, args) => {
            out.insert(n.clone());
            for a in args {
                collect_type_names(a, out);
            }
        }
        Ty::Tuple(items) => items.iter().for_each(|i| collect_type_names(i, out)),
        Ty::Record(fields) => fields.iter().for_each(|(_, t)| collect_type_names(t, out)),
        Ty::Fun(ps, r) => {
            ps.iter().for_each(|p| collect_type_names(p, out));
            collect_type_names(r, out);
        }
        Ty::Index(base, _) => collect_type_names(base, out),
    }
}

pub(crate) fn collect_expr_names(expr: &Expr, out: &mut std::collections::HashSet<String>) {
    fn go(e: &Expr, out: &mut std::collections::HashSet<String>) {
        collect_expr_names(e, out);
    }
    match expr {
        Expr::Var(n) => {
            out.insert(n.clone());
        }
        // An ascription and a proof pair both wrap an expression whose
        // names are still needed: the prelude is pruned by this walk, and
        // a name it does not reach is a function that is never built.
        Expr::Ascribe(inner, ty) => {
            collect_expr_names(inner, out);
            collect_type_names(ty, out);
        }
        Expr::ProofPair(_, value) => collect_expr_names(value, out),
        Expr::StaticInst(inner, _) => collect_expr_names(inner, out),
        Expr::Inst(n, tys) => {
            out.insert(n.clone());
            for t in tys {
                collect_type_names(t, out);
            }
        }
        Expr::UnaryNeg(e) => go(e, out),
        Expr::BinOp(_, l, r) => {
            go(l, out);
            go(r, out);
        }
        Expr::Index(a, b) => {
            go(a, out);
            go(b, out);
        }
        Expr::Proj(a, _) | Expr::Deref(a) => go(a, out),
        Expr::Store(p, v) => {
            go(p, out);
            go(v, out);
        }
        Expr::Assign(n, v) => {
            out.insert(n.clone());
            go(v, out);
        }
        Expr::While(a, b) => {
            go(a, out);
            go(b, out);
        }
        Expr::For(a, b, c, d) => {
            go(a, out);
            go(b, out);
            go(c, out);
            go(d, out);
        }
        Expr::Call(c, args) => {
            go(c, out);
            args.iter().for_each(|a| go(a, out));
        }
        Expr::MacroCall(_, args) | Expr::TupleLit(args) => args.iter().for_each(|a| go(a, out)),
        Expr::IfThenElse(a, b, c) => {
            go(a, out);
            go(b, out);
            go(c, out);
        }
        Expr::Lam(_, _, b) => go(b, out),
        Expr::Let(binds, body) => {
            // A proof binding mentions names that exist only in the
            // static language — an axiom has no body to emit and no
            // symbol to link.  Collecting them would ask the emitter to
            // build something the source never wrote.
            for b in binds.iter().filter(|b| !b.proof) {
                if let Some(t) = &b.ty {
                    collect_type_names(t, out);
                }
                collect_expr_names(&b.value, out);
            }
            collect_expr_names(body, out);
        }
        Expr::Case(s, arms) => {
            collect_expr_names(s, out);
            for (p, b) in arms {
                collect_pattern_names(p, out);
                collect_expr_names(b, out);
            }
        }
        Expr::Try(s, handlers) => {
            collect_expr_names(s, out);
            for (p, b) in handlers {
                collect_pattern_names(p, out);
                collect_expr_names(b, out);
            }
        }
        Expr::Raise(v) => collect_expr_names(v, out),
        Expr::LetFun(funs, body) => {
            for f in funs {
                collect_expr_names(&f.body, out);
                collect_type_names(&f.ret, out);
            }
            collect_expr_names(body, out);
        }
        _ => {}
    }
}

pub(crate) fn collect_pattern_names(pattern: &Pattern, out: &mut std::collections::HashSet<String>) {
    match pattern {
        Pattern::Ctor(n, fields) => {
            out.insert(n.clone());
            fields.iter().for_each(|f| collect_pattern_names(f, out));
        }
        Pattern::Tuple(items) => items.iter().for_each(|i| collect_pattern_names(i, out)),
        Pattern::InPlace(inner) => collect_pattern_names(inner, out),
        _ => {}
    }
}
