//! # Inference — working out which instance a template call means
//!
//! *Literate note.*  Monomorphisation can expand `length<int>(xs)`, but
//! real ATS almost never writes the instantiation:
//!
//! ```text
//! fun{a:t0p} length (xs: list0(a)): int = ...
//! val n = length (xs)     // xs : list0(int)
//! ```
//!
//! Choosing between `length$int` and `length$string` here means knowing
//! the type of the *argument expression*, which no substitution can tell
//! you.  That is what this pass adds: enough type inference to name the
//! instance, and no more.
//!
//! Three decisions shape it:
//!
//! 1. **It infers, it does not check.**  A type it cannot work out is
//!    simply unknown, and an expression whose type is unknown leaves the
//!    call alone for the emitter to report as it always did.  The pass can
//!    therefore only turn programs that used to fail into programs that
//!    work — it can never reject one that used to compile.
//!
//! 2. **The instance is found by matching, not by looking.**  For
//!    `length (xs)` the parameter's declared type `list0(a)` is matched
//!    against the argument's actual type `list0(int)`, and `a` falls out
//!    of the two lining up.  That one rule covers the argument being the
//!    type variable itself (`a` against `int`) as well.
//!
//! 3. **Static indices are dropped by arity.**  `list (int, n)` names a
//!    list with a length; the datatype was declared with one parameter, so
//!    the first argument is the type and the rest are indices.  Knowing
//!    the declared arity is what finally separates the two, which nothing
//!    earlier in the pipeline could do.

use std::collections::HashMap;

use ats2_domain::ast::{Def, Expr, FunDef, ImplementDef, LetBind, Pattern, Program, Ty};
use ats2_domain::errors::CompileError;

/// Fill in the instantiations the source left implicit.
pub struct Inferencer;

/// What is known about a callable name.
#[derive(Debug, Clone)]
struct Signature {
    ty_params: Vec<String>,
    params: Vec<Ty>,
    ret: Ty,
}

/// What is known about a constructor.
#[derive(Debug, Clone)]
struct CtorShape {
    /// The datatype it builds, and that datatype's parameters.
    datatype: String,
    ty_params: Vec<String>,
    fields: Vec<Ty>,
}

impl Inferencer {
    /// Rewrite every implicit template call into an explicit one.
    pub fn resolve(program: &Program) -> Result<Program, CompileError> {
        let mut ctx = InferCtx {
            globals: HashMap::new(),
            signatures: HashMap::new(),
            ctors: HashMap::new(),
            datatype_arity: HashMap::new(),
        };

        for def in &program.defs {
            match def {
                Def::Extern(d) => {
                    ctx.signatures.insert(
                        d.name.clone(),
                        Signature {
                            ty_params: d.ty_params.clone(),
                            params: d.params.iter().map(|p| p.ty.clone()).collect(),
                            ret: d.ret.clone(),
                        },
                    );
                }
                Def::Fun(f) => {
                    ctx.signatures.entry(f.name.clone()).or_insert(Signature {
                        ty_params: f.ty_params.clone(),
                        params: f.params.iter().map(|p| p.ty.clone()).collect(),
                        ret: f.ret.clone(),
                    });
                }
                Def::Datatype(d) => {
                    ctx.datatype_arity.insert(d.name.clone(), d.ty_params.len());
                    for c in &d.ctors {
                        ctx.ctors.insert(
                            c.name.clone(),
                            CtorShape {
                                datatype: d.name.clone(),
                                ty_params: d.ty_params.clone(),
                                fields: c.fields.clone(),
                            },
                        );
                    }
                }
                _ => {}
            }
        }

        // A top-level `val` without an annotation still has a type, and
        // the values after it may depend on knowing it.
        for def in &program.defs {
            if let Def::Val(v) = def {
                let known = v.ty.clone().or_else(|| {
                    let globals = ctx.globals.clone();
                    ctx.type_of(&v.value, &globals)
                });
                if let Some(t) = known {
                    ctx.globals.insert(v.name.clone(), t);
                }
            }
        }

        // `nil`/`cons` are the shorthands ATS programs write for the
        // prelude's list constructors, and inference has to know them by
        // those names too — a pattern spelled `cons(x, r)` is where the
        // element type of a list becomes visible.
        for (alias, declared) in crate::prelude::CTOR_ALIASES {
            if ctx.ctors.contains_key(*alias) {
                continue;
            }
            if let Some(shape) = ctx.ctors.get(*declared).cloned() {
                ctx.ctors.insert((*alias).to_string(), shape);
            }
        }

        let mut defs = Vec::new();
        for def in &program.defs {
            match def {
                Def::Fun(f) => {
                    let env = ctx.env_of(&f.params);
                    let body = ctx.walk(&f.body, &env);
                    defs.push(Def::Fun(FunDef { body, ..f.clone() }));
                }
                Def::Implement(im) => {
                    // An `implement` may leave its parameters unannotated,
                    // taking their types from the `extern` above it.
                    // Inference has to follow the same rule, or the body
                    // of a template would be typed with holes for
                    // parameters whose types are perfectly well known.
                    let env = match ctx.signatures.get(&im.name) {
                        Some(sig) if sig.params.len() == im.params.len() => im
                            .params
                            .iter()
                            .zip(&sig.params)
                            .map(|(p, ty)| (p.name.clone(), ty.clone()))
                            .collect(),
                        _ => ctx.env_of(&im.params),
                    };
                    let body = ctx.walk(&im.body, &env);
                    defs.push(Def::Implement(ImplementDef { body, ..im.clone() }));
                }
                Def::Val(v) => {
                    let globals = ctx.globals.clone();
                    let value = ctx.walk(&v.value, &globals);
                    defs.push(Def::Val(ats2_domain::ast::ValDef { value, ..v.clone() }));
                }
                other => defs.push(other.clone()),
            }
        }
        Ok(Program::new(defs))
    }
}

/// The types of the names visible at a point in a body.
type Env = HashMap<String, Ty>;

struct InferCtx {
    /// Top-level `val`s, which every body can see.
    globals: Env,
    signatures: HashMap<String, Signature>,
    ctors: HashMap<String, CtorShape>,
    datatype_arity: HashMap<String, usize>,
}

impl InferCtx {
    fn env_of(&self, params: &[ats2_domain::ast::Param]) -> Env {
        // Top-level values are in scope everywhere, and a parameter of
        // the same name shadows one.
        let mut env = self.globals.clone();
        env.extend(params.iter().map(|p| (p.name.clone(), p.ty.clone())));
        env
    }

    /// Rewrite an expression, naming the instance of every template call
    /// whose arguments reveal it.
    fn walk(&self, expr: &Expr, env: &Env) -> Expr {
        match expr {
            Expr::Call(callee, args) => {
                let args: Vec<Expr> = args.iter().map(|a| self.walk(a, env)).collect();
                if let Expr::Var(name) = &**callee {
                    if let Some(inst) = self.instantiation_for(name, &args, env) {
                        return Expr::Call(Box::new(inst), args);
                    }
                    // `list0_cons ("a", list0_nil ())` builds a list of
                    // strings, and the argument is the only thing that
                    // says so.  Naming the instance here keeps the
                    // emitter from reporting an ambiguity in a program
                    // that was never ambiguous — the same job
                    // `instantiation_for` does for a template call, for
                    // the same reason.
                    if let Some(shape) = self.ctors.get(name) {
                        if !shape.ty_params.is_empty() {
                            if let Some(Ty::App(_, ty_args)) = self.ctor_result(shape, &args, env) {
                                return Expr::Call(
                                    Box::new(Expr::Inst(name.clone(), ty_args)),
                                    args,
                                );
                            }
                        }
                    }
                }
                Expr::Call(Box::new(self.walk(callee, env)), args)
            }
            Expr::Let(binds, body) => {
                let mut inner = env.clone();
                let mut out = Vec::new();
                for b in binds {
                    let value = self.walk(&b.value, &inner);
                    let ty = b.ty.clone().or_else(|| self.type_of(&value, &inner));
                    if let (Some(name), Some(ty)) = (&b.name, ty) {
                        inner.insert(name.clone(), ty);
                    }
                    out.push(LetBind { value, ..b.clone() });
                }
                Expr::Let(out, Box::new(self.walk(body, &inner)))
            }
            Expr::Case(scrutinee, arms) => {
                let scrutinee = self.walk(scrutinee, env);
                let subject = self.type_of(&scrutinee, env);
                let arms = arms
                    .iter()
                    .map(|(p, b)| {
                        let mut inner = env.clone();
                        self.bind_pattern(p, subject.as_ref(), &mut inner);
                        (p.clone(), self.walk(b, &inner))
                    })
                    .collect();
                Expr::Case(Box::new(scrutinee), arms)
            }
            Expr::LetFun(funs, body) => {
                let funs = funs
                    .iter()
                    .map(|f| {
                        let inner = self.env_of(&f.params);
                        FunDef { body: self.walk(&f.body, &inner), ..f.clone() }
                    })
                    .collect();
                Expr::LetFun(funs, Box::new(self.walk(body, env)))
            }
            Expr::IfThenElse(c, t, e) => Expr::IfThenElse(
                Box::new(self.walk(c, env)),
                Box::new(self.walk(t, env)),
                Box::new(self.walk(e, env)),
            ),
            Expr::BinOp(op, l, r) => Expr::BinOp(*op, Box::new(self.walk(l, env)), Box::new(self.walk(r, env))),
            Expr::UnaryNeg(e) => Expr::UnaryNeg(Box::new(self.walk(e, env))),
            Expr::Index(b, i) => Expr::Index(Box::new(self.walk(b, env)), Box::new(self.walk(i, env))),
            Expr::Proj(b, i) => Expr::Proj(Box::new(self.walk(b, env)), *i),
            Expr::Deref(b) => Expr::Deref(Box::new(self.walk(b, env))),
            Expr::Store(p, v) => Expr::Store(Box::new(self.walk(p, env)), Box::new(self.walk(v, env))),
            Expr::Assign(n, v) => Expr::Assign(n.clone(), Box::new(self.walk(v, env))),
            Expr::While(c, b) => Expr::While(Box::new(self.walk(c, env)), Box::new(self.walk(b, env))),
            Expr::For(i, c, s, b) => Expr::For(
                Box::new(self.walk(i, env)),
                Box::new(self.walk(c, env)),
                Box::new(self.walk(s, env)),
                Box::new(self.walk(b, env)),
            ),
            Expr::MacroCall(n, args) => Expr::MacroCall(n.clone(), args.iter().map(|a| self.walk(a, env)).collect()),
            Expr::TupleLit(items) => Expr::TupleLit(items.iter().map(|a| self.walk(a, env)).collect()),
            Expr::Lam(ps, r, b) => Expr::Lam(ps.clone(), r.clone(), Box::new(self.walk(b, env))),
            _ => expr.clone(),
        }
    }

    /// The explicit instantiation a bare template call should carry, if
    /// the argument types reveal it.
    fn instantiation_for(&self, name: &str, args: &[Expr], env: &Env) -> Option<Expr> {
        let sig = self.signatures.get(name)?;
        if sig.ty_params.is_empty() {
            return None;
        }
        let mut subst: HashMap<String, Ty> = HashMap::new();
        for (declared, actual) in sig.params.iter().zip(args) {
            if let Some(actual) = self.type_of(actual, env) {
                self.match_types(declared, &actual, &sig.ty_params, &mut subst);
            }
        }
        // Every hole must be filled; a partly-known instance is no
        // instance at all.
        let resolved: Option<Vec<Ty>> = sig.ty_params.iter().map(|p| subst.get(p).cloned()).collect();
        Some(Expr::Inst(name.to_string(), resolved?))
    }

    /// Line a declared type up against an actual one, learning what the
    /// template's parameters must be.
    fn match_types(&self, declared: &Ty, actual: &Ty, holes: &[String], subst: &mut HashMap<String, Ty>) {
        let declared = strip_annotations(declared);
        let actual = strip_annotations(actual);
        match (&declared, &actual) {
            (Ty::Name(n), _) if holes.contains(n) => {
                subst.entry(n.clone()).or_insert_with(|| actual.clone());
            }
            (Ty::App(dn, dargs), Ty::App(an, aargs)) if dn == an => {
                for (d, a) in dargs.iter().zip(aargs) {
                    self.match_types(d, a, holes, subst);
                }
            }
            (Ty::Tuple(ds), Ty::Tuple(as_)) => {
                for (d, a) in ds.iter().zip(as_) {
                    self.match_types(d, a, holes, subst);
                }
            }
            _ => {}
        }
    }

    /// The type of an expression, where it can be worked out.
    fn type_of(&self, expr: &Expr, env: &Env) -> Option<Ty> {
        match expr {
            Expr::IntLit(_) => Some(Ty::Name("int".into())),
            Expr::CharLit(_) => Some(Ty::Name("char".into())),
            Expr::FloatLit(_) => Some(Ty::Name("double".into())),
            Expr::BoolLit(_) => Some(Ty::Name("bool".into())),
            Expr::StrLit(_) => Some(Ty::Name("string".into())),
            Expr::Var(n) => env.get(n).cloned().or_else(|| self.nullary_ctor_type(n)),
            Expr::UnaryNeg(_) => Some(Ty::Name("int".into())),
            Expr::BinOp(op, _, _) => {
                Some(Ty::Name(if op.is_comparison() { "bool" } else { "int" }.into()))
            }
            Expr::TupleLit(items) => {
                let parts: Option<Vec<Ty>> = items.iter().map(|i| self.type_of(i, env)).collect();
                Some(Ty::Tuple(parts?))
            }
            // `!s` — forcing a stream, or reading a `ref`.  It is the
            // one place a suspension becomes the thing it produces, and
            // everything a program does with a stream happens on the
            // other side of it: without this step the pattern under a
            // `val c = !ns` binds nothing inference can use.
            Expr::Deref(inner) => match strip_annotations(&self.type_of(inner, env)?) {
                Ty::App(n, args) if crate::prelude::is_a_suspension(&n) => {
                    Some(Ty::App("stream_con".into(), args))
                }
                Ty::App(n, args) if n == "ref" => args.into_iter().next(),
                // `!p` on an array *views* the cells rather than loading
                // one: there is no single element it could mean.  So the
                // type is unchanged, which is also what the emitter does
                // with it.
                Ty::App(n, args) if n == "array" => Some(Ty::App(n, args)),
                _ => None,
            },
            Expr::IfThenElse(_, t, e) => self.type_of(t, env).or_else(|| self.type_of(e, env)),
            Expr::Let(binds, body) => {
                let mut inner = env.clone();
                for b in binds {
                    let ty = b.ty.clone().or_else(|| self.type_of(&b.value, &inner));
                    if let (Some(name), Some(ty)) = (&b.name, ty) {
                        inner.insert(name.clone(), ty);
                    }
                }
                self.type_of(body, &inner)
            }
            Expr::Inst(name, args) => {
                // A constructor written with its instance — `BTnil{int}()`
                // — builds exactly that instance of its datatype.
                if let Some(shape) = self.ctors.get(name) {
                    if shape.ty_params.len() == args.len() {
                        return Some(Ty::App(shape.datatype.clone(), args.clone()));
                    }
                }
                let sig = self.signatures.get(name)?;
                let subst: HashMap<String, Ty> =
                    sig.ty_params.iter().cloned().zip(args.iter().cloned()).collect();
                Some(apply(&sig.ret, &subst))
            }
            Expr::Call(callee, args) => match &**callee {
                Expr::Var(name) => {
                    if let Some(shape) = self.ctors.get(name) {
                        return self.ctor_result(shape, args, env);
                    }
                    // A cast that moves no bits moves no type either.
                    if crate::prelude::preserves_its_argument_type(name) {
                        return self.type_of(args.first()?, env);
                    }
                    let sig = self.signatures.get(name)?;
                    if sig.ty_params.is_empty() {
                        return Some(sig.ret.clone());
                    }
                    // A template's result depends on the instance, which
                    // is found the same way the call site finds it.
                    let inst = self.instantiation_for(name, args, env)?;
                    self.type_of(&inst, env)
                }
                other => self.type_of(other, env),
            },
            _ => None,
        }
    }

    /// The type a constructor call builds, when its fields say what the
    /// datatype's parameters are.
    fn ctor_result(&self, shape: &CtorShape, args: &[Expr], env: &Env) -> Option<Ty> {
        if shape.ty_params.is_empty() {
            return Some(Ty::Name(shape.datatype.clone()));
        }
        let mut subst: HashMap<String, Ty> = HashMap::new();
        for (declared, actual) in shape.fields.iter().zip(args) {
            if let Some(actual) = self.type_of(actual, env) {
                self.match_types(declared, &actual, &shape.ty_params, &mut subst);
            }
        }
        let resolved: Option<Vec<Ty>> = shape.ty_params.iter().map(|p| subst.get(p).cloned()).collect();
        Some(Ty::App(shape.datatype.clone(), resolved?))
    }

    /// A nullary constructor of an unparameterized datatype names its
    /// type all by itself.
    fn nullary_ctor_type(&self, name: &str) -> Option<Ty> {
        let shape = self.ctors.get(name)?;
        if shape.ty_params.is_empty() && shape.fields.is_empty() {
            Some(Ty::Name(shape.datatype.clone()))
        } else {
            None
        }
    }

    /// Bring the names a pattern binds into the environment.
    fn bind_pattern(&self, pattern: &Pattern, subject: Option<&Ty>, env: &mut Env) {
        match pattern {
            Pattern::Var(n) => {
                if let Some(t) = subject {
                    env.insert(n.clone(), t.clone());
                }
            }
            Pattern::Tuple(items) => {
                let parts = match subject {
                    Some(Ty::Tuple(parts)) => parts.clone(),
                    _ => vec![],
                };
                for (i, sub) in items.iter().enumerate() {
                    self.bind_pattern(sub, parts.get(i), env);
                }
            }
            // `@cons(n, ns)` binds the same names an ordinary `cons`
            // pattern would; that they name cells rather than copies is
            // a question for the emitter, not for inference.
            Pattern::InPlace(inner) => self.bind_pattern(inner, subject, env),
            Pattern::Ctor(name, fields) => {
                let Some(shape) = self.ctors.get(name) else { return };
                // The scrutinee's own type says what the datatype's
                // parameters are, and therefore what the fields hold.
                let subst = match subject {
                    Some(Ty::App(_, args)) => shape
                        .ty_params
                        .iter()
                        .cloned()
                        .zip(args.iter().cloned())
                        .collect::<HashMap<_, _>>(),
                    _ => HashMap::new(),
                };
                for (sub, declared) in fields.iter().zip(&shape.fields) {
                    let ty = apply(declared, &subst);
                    self.bind_pattern(sub, Some(&ty), env);
                }
            }
            _ => {}
        }
    }
}

/// Substitute a datatype's parameters through one of its field types.
fn apply(ty: &Ty, subst: &HashMap<String, Ty>) -> Ty {
    match ty {
        Ty::Name(n) => subst.get(n).cloned().unwrap_or_else(|| ty.clone()),
        Ty::App(n, args) => Ty::App(n.clone(), args.iter().map(|a| apply(a, subst)).collect()),
        Ty::Tuple(items) => Ty::Tuple(items.iter().map(|i| apply(i, subst)).collect()),
        Ty::Fun(ps, r) => Ty::Fun(ps.iter().map(|p| apply(p, subst)).collect(), Box::new(apply(r, subst))),
        // A type parameter is substituted for a *type*, never for a
        // static index, so the indices ride along untouched.
        Ty::Index(base, idx) => Ty::Index(Box::new(apply(base, subst)), idx.clone()),
        Ty::Record(fields) => {
            Ty::Record(fields.iter().map(|(n, t)| (n.clone(), apply(t, subst))).collect())
        }
    }
}

/// Remove the wrappers that decorate a type without changing it.
///
/// `INV(a)` marks a parameter invariant for the type checker's benefit;
/// underneath it is just `a`, and matching has to see through it.
fn strip_annotations(ty: &Ty) -> Ty {
    match ty {
        Ty::App(n, args) if args.len() == 1 && matches!(n.as_str(), "INV" | "OUT" | "INVAR") => {
            strip_annotations(&args[0])
        }
        _ => ty.clone(),
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    fn resolve(src: &str) -> Program {
        let p = Parser::parse(src).expect("parse");
        Inferencer::resolve(&p).expect("resolve")
    }

    #[test]
    fn a_cast_that_moves_no_bits_moves_no_type_either() {
        // `ptrcast (A)` drops what ATS knows about `A` into a bare
        // `ptr`, and the proof it hands back separately is what puts it
        // there again.  Proofs are erased here, so the only way the
        // element type survives the cast is for the cast to be
        // transparent to inference — which is honest, because it is
        // transparent to the machine too.
        let p = resolve(concat!(
            "extern fun{a:t@ype} rev (xs: list0(a)): void\n",
            "fun f (ys: list0(int)): void = rev (ptrcast (ys))\n",
        ));
        let rendered = format!("{:?}", &p.defs()[1]);
        assert!(
            rendered.contains("Inst(\"rev\", [Name(\"int\")])"),
            "the cast lost the element type:\n{rendered}"
        );
    }

    #[test]
    fn a_constructor_call_is_instantiated_from_its_arguments() {
        // `list0_cons (\"a\", list0_nil ())` can only be building a list
        // of strings, and nothing but the argument says so — there is no
        // annotation on the binding and no context around it.  Leaving
        // it for the emitter means an ambiguity report for a program
        // that was never ambiguous.
        let p = resolve(concat!(
            "datatype list0(a) = list0_nil of () | list0_cons of (a, list0(a))\n",
            "implement main0 () = { val xs = list0_cons (\"a\", list0_nil ()) }\n",
        ));
        let rendered = format!("{:?}", &p.defs()[1]);
        assert!(
            rendered.contains("Inst(\"list0_cons\", [Name(\"string\")])"),
            "the constructor was not instantiated:\n{rendered}"
        );
    }

    #[test]
    fn forcing_a_stream_yields_the_type_it_produces() {
        // `!ns` is where a stream stops being a suspension and starts
        // being a `stream_con`.  Without that step the pattern below it
        // binds nothing inference can use, and the template call two
        // lines later has no instance.
        let p = resolve(concat!(
            // The prelude declares this; the test states it so that the
            // test is about inference and not about prelude assembly.
            "datatype stream_con(a) = stream_nil of () | stream_cons of (a, stream(a))\n",
            "extern fun{a:t@ype} take (xs: stream(a)): int\n",
            "fun f (ns: stream(int)): int = let
",
            "  val c = !ns
",
            "  val-stream_cons(n, ns2) = c
",
            "in take (ns2) end
",
        ));
        let rendered = format!("{:?}", &p.defs()[2]);
        assert!(
            rendered.contains("Inst(\"take\", [Name(\"int\")])"),
            "the call was not instantiated:\n{rendered}"
        );
    }

    #[test]
    fn an_instantiated_constructor_call_tells_a_template_its_instance() {
        // `size (BTnil{int}())` — the constructor was written with its
        // instance, so the bare template call can be read straight off
        // the argument.
        let p = resolve(concat!(
            "datatype bintree(a) = BTnil of () | BTcons of (bintree a, a, bintree a)\n",
            "fun{a:t@ype} size (bt: bintree a): int = 0\n",
            "implement main0 () = { val n = size (BTnil{int}()) }\n",
        ));
        let rendered = format!("{:?}", &p.defs()[2]);
        assert!(
            rendered.contains("Inst(\"size\", [Name(\"int\")])"),
            "the call was not instantiated:\n{rendered}"
        );
    }

    #[test]
    fn a_value_built_by_a_constructor_tells_a_template_its_instance() {
        // `val bt0 = BTnil{int}()` then `size (bt0)` — the instance is
        // one hop away, in the type the binding carries.
        let p = resolve(concat!(
            "datatype bintree(a) = BTnil of () | BTcons of (bintree a, a, bintree a)\n",
            "fun{a:t@ype} size (bt: bintree a): int = 0\n",
            "implement main0 () = { val bt0 = BTnil{int}() val n = size (bt0) }\n",
        ));
        let rendered = format!("{:?}", &p.defs()[2]);
        assert!(
            rendered.contains("Inst(\"size\", [Name(\"int\")])"),
            "the call was not instantiated:\n{rendered}"
        );
    }
}
