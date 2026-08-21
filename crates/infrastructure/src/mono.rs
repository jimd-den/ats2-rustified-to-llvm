//! # Monomorphisation — turning one template into many functions
//!
//! *Literate note.*  ATS writes a generic function as a **template**:
//!
//! ```text
//! extern fun{a:t@ype} ident (x: a): a
//! implement{a} ident (x) = x
//! ```
//!
//! `a` is not a type; it is a hole where a type will go.  LLVM has no such
//! hole — every function there has a settled signature — so before
//! emission each template must become one ordinary function per type it is
//! actually used at.  That is this pass.
//!
//! The technique is the one C++ and Rust use for generics: find every
//! instantiation, substitute, and emit a specialised copy under a mangled
//! name.  Three decisions are worth recording:
//!
//! 1. **Demand drives it.**  Nothing is emitted for a template that is
//!    never instantiated, and each distinct instantiation is emitted
//!    exactly once.  A worklist does both: an instantiation is queued the
//!    first time it is seen and skipped every time after.
//!
//! 2. **Instantiations are found inside instantiations.**  A template may
//!    call another — or itself — at a type that is only known once the
//!    caller's own substitution is applied.  Processing the worklist until
//!    it drains handles both, and recursion terminates because a program
//!    can only mention finitely many types.
//!
//! 3. **The instantiation must be written.**  ATS infers it; this compiler
//!    does not, and rather than guess it reports a template used without
//!    one.  Inferring it needs the type checker that the roadmap keeps
//!    deliberately late.

use std::collections::{HashMap, HashSet, VecDeque};

use ats2_domain::ast::{
    Ctor, DatatypeDef, Def, Expr, FunDef, ImplementDef, LetBind, Param, Program, Ty,
};
use ats2_domain::errors::CompileError;

/// Rewrite a program so that no template survives.
pub struct Monomorphiser;

/// A template: the shape to copy, and the holes to fill.
#[derive(Debug, Clone)]
struct Template {
    ty_params: Vec<String>,
    params: Vec<Param>,
    ret: Ty,
    /// The body that answers for every instance, when there is one.
    body: Option<Expr>,
    /// Bodies supplied for *particular* instances, by the key of their
    /// type arguments.  One of these wins over the generic body for the
    /// instance it names, and says nothing about any other.
    instances: HashMap<String, (Vec<Param>, Expr)>,
}

impl Monomorphiser {
    /// Replace every template with the instances the program asks for.
    pub fn expand(program: &Program) -> Result<Program, CompileError> {
        let mut templates: HashMap<String, Template> = HashMap::new();

        // A declaration gives the shape; an implementation gives the body.
        // They are separate defs, so both are collected before either is
        // used.
        for def in &program.defs {
            if let Def::Extern(d) = def {
                if !d.ty_params.is_empty() {
                    templates.insert(
                        d.name.clone(),
                        Template {
                            ty_params: d.ty_params.clone(),
                            params: d.params.clone(),
                            ret: d.ret.clone(),
                            body: None,
                            instances: HashMap::new(),
                        },
                    );
                }
            }
        }
        for def in &program.defs {
            match def {
                Def::Implement(im) if templates.contains_key(&im.name) => {
                    let t = templates.get_mut(&im.name).expect("just checked");
                    // The declaration named the parameters' types; the
                    // implementation may rename the parameters themselves.
                    if im.params.len() == t.params.len() {
                        for (slot, given) in t.params.iter_mut().zip(&im.params) {
                            slot.name = given.name.clone();
                        }
                    }
                    if !im.ty_params.is_empty() {
                        t.ty_params = im.ty_params.clone();
                    }
                    // `implement fprint_val<list0(int)> (...)` answers
                    // for that instance alone.  Filing it as the generic
                    // body would let it answer for `fprint_val<int>` as
                    // well, which is exactly what the protocol must not
                    // do: the compiler already knows how to print an
                    // int, and the program is adding a case, not
                    // replacing every case.
                    // `implement(a) f<a> (...)` names the instance `<a>`,
                    // which is the implementation's own parameter — that
                    // is the generic case written the long way round, not
                    // an instance.
                    let generic = im
                        .instance
                        .iter()
                        .all(|t| matches!(t, Ty::Name(n) if im.ty_params.contains(n)));
                    if !generic && !im.instance.is_empty() && im.instance.len() == t.ty_params.len()
                    {
                        let key = instance_key(&im.instance);
                        t.instances
                            .insert(key, (im.params.clone(), im.body.clone()));
                    } else {
                        t.body = Some(im.body.clone());
                    }
                }
                // An `implement{a} f (...) = body` with nothing
                // declaring `f`.  The braces are then the only thing
                // saying it is a template — and they have to be enough,
                // or the type variable reaches the emitter as if it
                // named a real type.  The implementation supplies the
                // shape it would otherwise have read off a declaration.
                // A `$`-name is a *hole* in another template, not a
                // template in its own right: it is selected by the
                // instantiation that surrounds it, so it stays an
                // ordinary definition for the hole-filling pass to find.
                Def::Implement(im) if !im.ty_params.is_empty() && !im.name.contains('$') => {
                    templates.insert(
                        im.name.clone(),
                        Template {
                            ty_params: im.ty_params.clone(),
                            params: im.params.clone(),
                            ret: im.ret.clone().unwrap_or(Ty::Name("void".into())),
                            body: Some(im.body.clone()),
                            instances: HashMap::new(),
                        },
                    );
                }
                // `fun{a:t@ype} f (...) = body` states both at once.
                Def::Fun(f) if !f.ty_params.is_empty() => {
                    templates.insert(
                        f.name.clone(),
                        Template {
                            ty_params: f.ty_params.clone(),
                            params: f.params.clone(),
                            ret: f.ret.clone(),
                            body: Some(f.body.clone()),
                            instances: HashMap::new(),
                        },
                    );
                }
                _ => {}
            }
        }

        // A datatype may be parameterized too — the prelude's list is
        // `datatype list0(a)` — and it is instantiated by exactly the same
        // demand-driven rule as a function template.
        let mut datatypes: HashMap<String, DatatypeDef> = HashMap::new();
        for def in &program.defs {
            if let Def::Datatype(d) = def {
                if !d.ty_params.is_empty() {
                    datatypes.insert(d.name.clone(), d.clone());
                }
            }
        }

        let mut ctx = MonoCtx {
            templates,
            datatypes,
            queued: HashSet::new(),
            work: VecDeque::new(),
            dqueued: HashSet::new(),
            dwork: VecDeque::new(),
            out: Vec::new(),
        };

        // Everything that is not a template is kept, with its body scanned
        // for the instantiations it asks for.
        let mut defs = Vec::new();
        for def in &program.defs {
            match def {
                Def::Fun(f) if ctx.templates.contains_key(&f.name) => {}
                Def::Extern(d) if ctx.templates.contains_key(&d.name) => {}
                Def::Implement(im) if ctx.templates.contains_key(&im.name) => {}
                // A parameterized datatype is a recipe, like a template:
                // only its instances are kept.
                Def::Datatype(d) if !d.ty_params.is_empty() => {}
                Def::Fun(f) => {
                    let params = ctx.rewrite_params(&f.params, &HashMap::new());
                    let ret = ctx.rewrite_ty(&f.ret, &HashMap::new());
                    let body = ctx.rewrite(&f.body, &HashMap::new())?;
                    defs.push(Def::Fun(FunDef {
                        params,
                        ret,
                        body,
                        ..f.clone()
                    }));
                }
                Def::Extern(d) => {
                    let params = ctx.rewrite_params(&d.params, &HashMap::new());
                    let ret = ctx.rewrite_ty(&d.ret, &HashMap::new());
                    defs.push(Def::Extern(ats2_domain::ast::FunDecl {
                        proof: false,
                        universals: Vec::new(),
                        existentials: Vec::new(),
                        params,
                        ret,
                        ..d.clone()
                    }));
                }
                Def::Implement(im) => {
                    let params = ctx.rewrite_params(&im.params, &HashMap::new());
                    let ret = im.ret.as_ref().map(|t| ctx.rewrite_ty(t, &HashMap::new()));
                    let body = ctx.rewrite(&im.body, &HashMap::new())?;
                    defs.push(Def::Implement(ImplementDef {
                        params,
                        ret,
                        body,
                        ..im.clone()
                    }));
                }
                Def::Val(v) => {
                    let value = ctx.rewrite(&v.value, &HashMap::new())?;
                    let ty = v.ty.as_ref().map(|t| ctx.rewrite_ty(t, &HashMap::new()));
                    defs.push(Def::Val(ats2_domain::ast::ValDef {
                        ty,
                        value,
                        ..v.clone()
                    }));
                }
                other => defs.push(other.clone()),
            }
        }

        // Draining the worklist may queue more work, which is exactly what
        // lets one instantiation pull in the next.
        // Draining either queue may fill the other: a function instance
        // can mention a datatype instance, and a datatype instance's
        // fields can mention further ones.
        loop {
            if let Some((name, args)) = ctx.dwork.pop_front() {
                let instance = ctx.instantiate_datatype(&name, &args);
                ctx.out.push(instance);
                continue;
            }
            if let Some((name, args)) = ctx.work.pop_front() {
                let instance = ctx.instantiate(&name, &args)?;
                ctx.out.push(instance);
                continue;
            }
            break;
        }

        let mut all = std::mem::take(&mut ctx.out);
        all.extend(defs);
        Ok(Program::new(all))
    }
}

struct MonoCtx {
    templates: HashMap<String, Template>,
    datatypes: HashMap<String, DatatypeDef>,
    queued: HashSet<String>,
    work: VecDeque<(String, Vec<Ty>)>,
    dqueued: HashSet<String>,
    dwork: VecDeque<(String, Vec<Ty>)>,
    out: Vec<Def>,
}

/// The internal type former standing for a suspended value.
///
/// It has a `$` in its name because no ATS source can spell it: it is
/// what `stream`, `stream_vt` and `lazy` all rewrite into, so that one
/// representation serves them and the emitter has one thing to know
/// about rather than four.
pub const LAZY: &str = "$lazy";

/// The substitution in force while rewriting: a template's type parameters
/// bound to the types this instance uses.
type Subst = HashMap<String, Ty>;

impl MonoCtx {
    /// Rewrite a type: apply the substitution in force, and turn any
    /// mention of a parameterized datatype into the instance it names.
    fn rewrite_ty(&mut self, ty: &Ty, subst: &Subst) -> Ty {
        let ty = substitute(ty, subst);
        self.rewrite_substituted_ty(&ty)
    }

    /// Rewrite a type after simultaneous substitution has already happened.
    ///
    /// A replacement is atomic with respect to the substitution that produced
    /// it. Reapplying that substitution inside the replacement turns
    /// `{a ↦ (a, b)}` into an infinite `(a, b)` nesting rather than the one
    /// replacement simultaneous substitution means.
    fn rewrite_substituted_ty(&mut self, ty: &Ty) -> Ty {
        match &ty {
            Ty::Proof(p, v) => Ty::Proof(
                Box::new(self.rewrite_substituted_ty(p)),
                Box::new(self.rewrite_substituted_ty(v)),
            ),
            // `stream(t)` / `stream_vt(t)` — a *suspended* `stream_con(t)`.
            // The suspension is a representation this compiler supplies
            // rather than one the source declares, so the type is
            // rewritten into the internal one that names it, and the
            // element datatype is requested along the way.
            Ty::App(name, args)
                if matches!(name.as_str(), "stream" | "stream_vt" | "lazy" | "llazy") =>
            {
                let args: Vec<Ty> = args
                    .iter()
                    .map(|a| self.rewrite_substituted_ty(a))
                    .collect();
                let con = self.request_datatype("stream_con", &args);
                Ty::App(LAZY.into(), vec![Ty::Name(con)])
            }
            Ty::App(name, args) if self.datatypes.contains_key(name) => {
                let args: Vec<Ty> = args
                    .iter()
                    .map(|a| self.rewrite_substituted_ty(a))
                    .collect();
                Ty::Name(self.request_datatype(name, &args))
            }
            // A parameterized datatype named with no arguments at all
            // cannot be instantiated; leave it for the emitter to reject
            // with a type error that names it.
            Ty::App(name, args) => Ty::App(
                name.clone(),
                args.iter()
                    .map(|a| self.rewrite_substituted_ty(a))
                    .collect(),
            ),
            Ty::Tuple(items) => Ty::Tuple(
                items
                    .iter()
                    .map(|i| self.rewrite_substituted_ty(i))
                    .collect(),
            ),
            Ty::Fun(ps, r) => Ty::Fun(
                ps.iter().map(|p| self.rewrite_substituted_ty(p)).collect(),
                Box::new(self.rewrite_substituted_ty(r)),
            ),
            Ty::Index(base, idx) => {
                Ty::Index(Box::new(self.rewrite_substituted_ty(base)), idx.clone())
            }
            Ty::Record(fields) => Ty::Record(
                fields
                    .iter()
                    .map(|(n, t)| (n.clone(), self.rewrite_substituted_ty(t)))
                    .collect(),
            ),
            Ty::Name(_) => ty.clone(),
        }
    }

    fn rewrite_params(&mut self, params: &[Param], subst: &Subst) -> Vec<Param> {
        params
            .iter()
            .map(|p| Param {
                borrowed: false,
                name: p.name.clone(),
                ty: self.rewrite_ty(&p.ty, subst),
            })
            .collect()
    }

    /// Queue a datatype instance if it has not been asked for before.
    fn request_datatype(&mut self, name: &str, args: &[Ty]) -> String {
        let mangled = mangle(name, args);
        if self.dqueued.insert(mangled.clone()) {
            self.dwork.push_back((name.to_string(), args.to_vec()));
        }
        mangled
    }

    /// Build one instance of a parameterized datatype.
    ///
    /// The constructors keep their original names.  Two instances of the
    /// same datatype therefore declare constructors that share a name, and
    /// telling them apart is the emitter's job — it has the types, which
    /// is what the choice depends on.
    fn instantiate_datatype(&mut self, name: &str, args: &[Ty]) -> Def {
        let d = self.datatypes[name].clone();
        let subst: Subst = d
            .ty_params
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        let ctors = d
            .ctors
            .iter()
            .map(|c| Ctor {
                name: c.name.clone(),
                fields: c
                    .fields
                    .iter()
                    .map(|f| self.rewrite_ty(f, &subst))
                    .collect(),
            })
            .collect();
        Def::Datatype(DatatypeDef {
            linear: false,
            name: mangle(name, args),
            ty_params: vec![],
            ctors,
        })
    }

    /// Build one instance of a template.
    fn instantiate(&mut self, name: &str, args: &[Ty]) -> Result<Def, CompileError> {
        let t = self.templates[name].clone();
        // A body supplied for *this* instance wins over the generic one:
        // it was written knowing which types it is dealing with.
        let supplied = t.instances.get(&instance_key(args)).cloned();
        let (params, body) = match supplied {
            Some((params, body)) => (params, body),
            None => {
                let Some(body) = t.body.clone() else {
                    return Err(CompileError::emit(format!(
                        "`{name}` is declared as a template but never implemented"
                    )));
                };
                (t.params.clone(), body)
            }
        };
        if args.len() != t.ty_params.len() {
            return Err(CompileError::emit(format!(
                "`{name}` takes {} type argument(s), got {}",
                t.ty_params.len(),
                args.len()
            )));
        }
        let subst: Subst = t
            .ty_params
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        // The declaration named the parameters' types; an instance
        // implementation names the parameters, and may be the only thing
        // that does.
        let params: Vec<Param> = t
            .params
            .iter()
            .zip(params.iter().map(Some).chain(std::iter::repeat(None)))
            .map(|(declared, given)| Param {
                borrowed: false,
                name: given.map_or_else(|| declared.name.clone(), |g| g.name.clone()),
                ty: declared.ty.clone(),
            })
            .collect();
        let params = self.rewrite_params(&params, &subst);
        let ret = self.rewrite_ty(&t.ret, &subst);
        let body = self.rewrite(&body, &subst)?;
        Ok(Def::Fun(FunDef {
            metric: Vec::new(),
            ty_params: vec![],
            // Monomorphisation copies a template's body; the static
            // quantifiers belong to the template's declaration, which is
            // not what is being copied here.
            universals: vec![],
            existentials: vec![],
            name: mangle(name, args),
            params,
            ret,
            body,
            proof: false,
        }))
    }

    /// Queue an instantiation if it has not been asked for before.
    ///
    /// Not every `f<t>` names a template: the prelude shims are written
    /// with type arguments too (`fileref_load<int>`), and there the
    /// arguments say which shim is meant rather than which copy to build.
    /// Such a name is passed through unchanged for the emitter to resolve.
    fn request(&mut self, name: &str, args: &[Ty]) -> Result<String, CompileError> {
        let Some(t) = self.templates.get(name) else {
            return Ok(name.to_string());
        };
        // A protocol like `fprint_val` is declared for every type and
        // implemented for a few.  An instance nobody supplied is not an
        // error: the compiler may know it already, so the name is passed
        // through for the emitter to answer.
        if t.body.is_none() && !t.instances.contains_key(&instance_key(args)) {
            return Ok(name.to_string());
        }
        let mangled = mangle(name, args);
        if self.queued.insert(mangled.clone()) {
            self.work.push_back((name.to_string(), args.to_vec()));
        }
        Ok(mangled)
    }

    /// Rewrite an expression under a substitution, replacing every
    /// instantiation with the name of the instance it needs.
    fn rewrite(&mut self, expr: &Expr, subst: &Subst) -> Result<Expr, CompileError> {
        Ok(match expr {
            Expr::Unit
            | Expr::Uninit
            | Expr::Wildcard
            | Expr::IntLit(_)
            | Expr::CharLit(_)
            | Expr::FloatLit(_)
            | Expr::BoolLit(_)
            | Expr::StrLit(_) => expr.clone(),
            Expr::StaticInst(inner, at) => {
                Expr::StaticInst(Box::new(self.rewrite(inner, subst)?), at.clone())
            }
            Expr::ProofPair(p, v) => Expr::ProofPair(
                Box::new(self.rewrite(p, subst)?),
                Box::new(self.rewrite(v, subst)?),
            ),
            Expr::Ascribe(inner, ty) => Expr::Ascribe(
                Box::new(self.rewrite(inner, subst)?),
                self.rewrite_ty(ty, subst),
            ),
            Expr::Var(name) => {
                // A template mentioned with no instantiation cannot be
                // resolved: say so, rather than emitting a call to a
                // function that was never built.
                if self.templates.contains_key(name) {
                    return Err(CompileError::emit(format!(
                        "`{name}` is a template and must say which instance it means, as in `{name}<int>`"
                    )));
                }
                expr.clone()
            }
            Expr::Inst(name, args) => {
                let args: Vec<Ty> = args.iter().map(|a| self.rewrite_ty(a, subst)).collect();
                if self.templates.contains_key(name) {
                    Expr::Var(self.request(name, &args)?)
                } else {
                    // Not a template: a prelude shim written with type
                    // arguments, such as `gnumber_int<double>`.  The
                    // arguments say which shim is meant, so they are kept
                    // for the emitter rather than dropped.
                    Expr::Inst(name.clone(), args)
                }
            }
            Expr::UnaryNeg(e) => Expr::UnaryNeg(Box::new(self.rewrite(e, subst)?)),
            Expr::BinOp(op, l, r) => Expr::BinOp(
                *op,
                Box::new(self.rewrite(l, subst)?),
                Box::new(self.rewrite(r, subst)?),
            ),
            Expr::Index(b, i) => Expr::Index(
                Box::new(self.rewrite(b, subst)?),
                Box::new(self.rewrite(i, subst)?),
            ),
            Expr::Proj(b, i) => Expr::Proj(Box::new(self.rewrite(b, subst)?), *i),
            Expr::Field(b, n) => Expr::Field(Box::new(self.rewrite(b, subst)?), n.clone()),
            Expr::RecordLit(fields) => Expr::RecordLit(
                fields
                    .iter()
                    .map(|(n, v)| Ok((n.clone(), self.rewrite(v, subst)?)))
                    .collect::<Result<Vec<_>, CompileError>>()?,
            ),
            Expr::Deref(b) => Expr::Deref(Box::new(self.rewrite(b, subst)?)),
            Expr::Store(p, v) => Expr::Store(
                Box::new(self.rewrite(p, subst)?),
                Box::new(self.rewrite(v, subst)?),
            ),
            Expr::Assign(n, v) => Expr::Assign(n.clone(), Box::new(self.rewrite(v, subst)?)),
            Expr::While(c, b) => Expr::While(
                Box::new(self.rewrite(c, subst)?),
                Box::new(self.rewrite(b, subst)?),
            ),
            Expr::For(i, c, st, b) => Expr::For(
                Box::new(self.rewrite(i, subst)?),
                Box::new(self.rewrite(c, subst)?),
                Box::new(self.rewrite(st, subst)?),
                Box::new(self.rewrite(b, subst)?),
            ),
            Expr::Call(callee, args) => Expr::Call(
                Box::new(self.rewrite(callee, subst)?),
                args.iter()
                    .map(|a| self.rewrite(a, subst))
                    .collect::<Result<_, _>>()?,
            ),
            Expr::ExtVal {
                ty,
                name,
                args,
                via_ptr,
            } => Expr::ExtVal {
                ty: ty.clone(),
                name: name.clone(),
                args: args
                    .iter()
                    .map(|a| self.rewrite(a, subst))
                    .collect::<Result<_, _>>()?,
                via_ptr: *via_ptr,
            },
            Expr::MacroCall(name, args) => Expr::MacroCall(
                name.clone(),
                args.iter()
                    .map(|a| self.rewrite(a, subst))
                    .collect::<Result<_, _>>()?,
            ),
            Expr::TupleLit(items) => Expr::TupleLit(
                items
                    .iter()
                    .map(|a| self.rewrite(a, subst))
                    .collect::<Result<_, _>>()?,
            ),
            Expr::IfThenElse(c, t, e) => Expr::IfThenElse(
                Box::new(self.rewrite(c, subst)?),
                Box::new(self.rewrite(t, subst)?),
                Box::new(self.rewrite(e, subst)?),
            ),
            Expr::Lam(ps, r, b) => Expr::Lam(
                self.rewrite_params(ps, subst),
                r.as_ref().map(|t| self.rewrite_ty(t, subst)),
                Box::new(self.rewrite(b, subst)?),
            ),
            Expr::Let(binds, body) => {
                let mut out = Vec::new();
                for b in binds {
                    out.push(LetBind {
                        ty: b.ty.as_ref().map(|t| self.rewrite_ty(t, subst)),
                        value: self.rewrite(&b.value, subst)?,
                        ..b.clone()
                    });
                }
                Expr::Let(out, Box::new(self.rewrite(body, subst)?))
            }
            Expr::Try(scrutinee, handlers) => {
                let mut out = Vec::new();
                for (p, b) in handlers {
                    out.push((p.clone(), self.rewrite(b, subst)?));
                }
                Expr::Try(Box::new(self.rewrite(scrutinee, subst)?), out)
            }
            Expr::Raise(value) => Expr::Raise(Box::new(self.rewrite(value, subst)?)),
            Expr::Case(scrutinee, arms) => {
                let mut out = Vec::new();
                for (p, b) in arms {
                    out.push((p.clone(), self.rewrite(b, subst)?));
                }
                Expr::Case(Box::new(self.rewrite(scrutinee, subst)?), out)
            }
            Expr::LetFun(funs, body) => {
                let mut out = Vec::new();
                for f in funs {
                    out.push(FunDef {
                        params: self.rewrite_params(&f.params, subst),
                        ret: self.rewrite_ty(&f.ret, subst),
                        body: self.rewrite(&f.body, subst)?,
                        ..f.clone()
                    });
                }
                Expr::LetFun(out, Box::new(self.rewrite(body, subst)?))
            }
        })
    }
}

/// Replace a template's type parameters wherever they appear in a type.
fn substitute(ty: &Ty, subst: &Subst) -> Ty {
    match ty {
        Ty::Proof(p, v) => Ty::Proof(
            Box::new(substitute(p, subst)),
            Box::new(substitute(v, subst)),
        ),
        Ty::Name(n) => subst.get(n).cloned().unwrap_or_else(|| ty.clone()),
        Ty::App(n, args) => {
            let args = args.iter().map(|a| substitute(a, subst)).collect();
            match subst.get(n) {
                // Substituting into the *head* of an application would
                // need a higher-kinded substitution; the subset has none,
                // so the head is left alone and only the arguments move.
                Some(_) | None => Ty::App(n.clone(), args),
            }
        }
        Ty::Fun(ps, r) => Ty::Fun(
            ps.iter().map(|p| substitute(p, subst)).collect(),
            Box::new(substitute(r, subst)),
        ),
        Ty::Tuple(items) => Ty::Tuple(items.iter().map(|i| substitute(i, subst)).collect()),
        Ty::Index(base, idx) => Ty::Index(Box::new(substitute(base, subst)), idx.clone()),
        Ty::Record(fields) => Ty::Record(
            fields
                .iter()
                .map(|(n, t)| (n.clone(), substitute(t, subst)))
                .collect(),
        ),
    }
}

/// The name one instance is emitted under.
///
/// `ident<int>` becomes `ident$int`.  The `$` is deliberate: ATS
/// identifiers may contain one, but only in template *holes*, so a mangled
/// name cannot collide with a name the program could have written.
fn mangle(name: &str, args: &[Ty]) -> String {
    let mut out = name.to_string();
    for a in args {
        out.push('$');
        out.push_str(&type_key(a));
    }
    out
}

/// The key an instance's type arguments are filed under.
fn instance_key(args: &[Ty]) -> String {
    args.iter().map(type_key).collect::<Vec<_>>().join("$")
}

/// A short, stable spelling of a type, for use inside a mangled name.
fn type_key(ty: &Ty) -> String {
    match ty {
        // The proof half is erased, so two instances differing only in
        // it are one instance.
        Ty::Proof(_, value) => type_key(value),
        Ty::Name(n) => n.clone(),
        Ty::App(n, args) => {
            let inner: Vec<String> = args.iter().map(type_key).collect();
            format!("{n}_{}", inner.join("_"))
        }
        Ty::Tuple(items) => {
            let inner: Vec<String> = items.iter().map(type_key).collect();
            format!("tup_{}", inner.join("_"))
        }
        // A record's field *names* are part of its identity, so they are
        // part of the key: two records that differ only in them are two
        // types and must mangle to two names.
        Ty::Record(fields) => {
            let inner: Vec<String> = fields
                .iter()
                .map(|(n, t)| format!("{n}_{}", type_key(t)))
                .collect();
            format!("rec_{}", inner.join("_"))
        }
        Ty::Fun(ps, r) => {
            let inner: Vec<String> = ps.iter().map(type_key).collect();
            format!("fn_{}_{}", inner.join("_"), type_key(r))
        }
        // Two instances that differ only in a static index share one
        // machine representation, so they share one instance.
        Ty::Index(base, _) => type_key(base),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_substitution_is_not_reapplied_inside_its_replacement() {
        let mut datatypes = HashMap::new();
        datatypes.insert(
            "stream_con".into(),
            DatatypeDef {
                linear: false,
                name: "stream_con".into(),
                ty_params: vec!["a".into()],
                ctors: Vec::new(),
            },
        );
        let mut ctx = MonoCtx {
            templates: HashMap::new(),
            datatypes,
            queued: HashSet::new(),
            work: VecDeque::new(),
            dqueued: HashSet::new(),
            dwork: VecDeque::new(),
            out: Vec::new(),
        };
        let replacement = Ty::Tuple(vec![Ty::Name("a".into()), Ty::Name("b".into())]);
        let subst = HashMap::from([("a".into(), replacement.clone())]);

        let rewritten = ctx.rewrite_ty(
            &Ty::App("stream".into(), vec![Ty::Name("a".into())]),
            &subst,
        );

        assert_eq!(
            rewritten,
            Ty::App(LAZY.into(), vec![Ty::Name("stream_con$tup_a_b".into())])
        );
        assert_eq!(
            ctx.dwork.pop_front(),
            Some(("stream_con".into(), vec![replacement]))
        );
        assert!(ctx.dwork.is_empty());
    }
}
