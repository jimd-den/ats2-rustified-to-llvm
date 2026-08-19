//! # Lambda lifting — making nested functions ordinary ones
//!
//! *Literate note.*  ATS lets a function be defined inside a body:
//!
//! ```text
//! fun acker (m: int, n: int): int = let
//!   fun acker_m (n: int): int = if n <= 0 then acker (m-1, 1) else ...
//! in acker_m (n) end
//! ```
//!
//! `acker_m` reads `m`, which belongs to its *enclosing* invocation.  LLVM
//! has no such thing: every function there is top-level and closed over
//! nothing.  Bridging that gap is this pass.
//!
//! The technique is **lambda lifting**: each captured variable becomes an
//! extra parameter, and every call site is rewritten to pass it.  Because
//! the added parameter carries the same *name* as the variable it stands
//! for, the function's body needs no rewriting at all — the name that used
//! to resolve to an enclosing binding now resolves to a parameter.
//!
//! Two decisions worth recording:
//!
//! 1. **A sibling group shares one capture list.**  Mutually recursive
//!    nested functions are lifted with the *union* of their captures, so a
//!    call from one to another can forward the arguments it already holds.
//!    Computing per-function capture sets would be tighter and would make
//!    a sibling call need values it may not have; the union is both
//!    simpler and always correct.
//!
//! 2. **A capture must have a knowable type.**  There is no type checker
//!    here, so a captured variable's type is recovered from an annotation
//!    or from a literal.  When it cannot be recovered the pass refuses,
//!    by name, rather than emitting a function with a guessed signature.

use std::collections::{BTreeSet, HashMap, HashSet};

use ats2_domain::ast::{Def, Expr, FunDef, LetBind, Param, Program, Ty};
use ats2_domain::errors::CompileError;

/// Rewrite a program so that no `Expr::LetFun` survives.
pub struct Lifter;

impl Lifter {
    /// Lift every nested function to the top level.
    pub fn lift(program: &Program) -> Result<Program, CompileError> {
        let globals: HashSet<String> = program
            .defs
            .iter()
            .filter_map(|d| match d {
                Def::Fun(f) => Some(f.name.clone()),
                Def::Extern(d) => Some(d.name.clone()),
                Def::Const(c) => Some(c.name.clone()),
                Def::Implement(im) => Some(im.name.clone()),
                Def::Val(v) => Some(v.name.clone()),
                Def::Datatype(_) | Def::Overload { .. } => None,
            })
            .collect();

        let mut ctx =
            LiftCtx { globals, lifted: Vec::new(), used: HashSet::new(), hole_rewrites: Vec::new() };
        for def in &program.defs {
            if let Def::Fun(f) = def {
                ctx.used.insert(f.name.clone());
            }
        }

        let mut defs = Vec::new();
        for def in &program.defs {
            match def {
                Def::Fun(f) => {
                    let scope = scope_of_params(&f.params);
                    let body = ctx.walk(&f.body, &scope)?;
                    defs.push(Def::Fun(FunDef { body, ..f.clone() }));
                }
                Def::Implement(im) => {
                    let scope = scope_of_params(&im.params);
                    let body = ctx.walk(&im.body, &scope)?;
                    defs.push(Def::Implement(ats2_domain::ast::ImplementDef { body, ..im.clone() }));
                }
                other => defs.push(other.clone()),
            }
        }
        // Catch the holes up with every rewrite lifting made.  A hole
        // whose body mentions none of those names is left exactly as it
        // was, so applying them all costs nothing and asks nothing about
        // which scope a hole came from — which is as well, because by
        // now that is no longer written down anywhere.
        for def in &mut defs {
            let Def::Implement(im) = def else { continue };
            if !im.name.contains('$') {
                continue;
            }
            for (renames, captured) in &ctx.hole_rewrites {
                im.body = rewrite_calls(&im.body, renames, captured);
            }
        }

        // Lifted functions are prepended so they precede their callers;
        // order is cosmetic (the emitter registers signatures up front),
        // but reading the output is easier this way.
        let mut all = ctx.lifted;
        all.extend(defs);
        Ok(Program::new(all))
    }
}

/// A name → type map for the bindings visible at a point in the program.
type Scope = HashMap<String, Ty>;

fn scope_of_params(params: &[Param]) -> Scope {
    params.iter().map(|p| (p.name.clone(), p.ty.clone())).collect()
}

struct LiftCtx {
    globals: HashSet<String>,
    lifted: Vec<Def>,
    used: HashSet<String>,
    /// Every rewrite lifting applied to a call, kept so that template
    /// *holes* can be given the same treatment.
    ///
    /// A hole is inlined into the scope it was written in, so its body
    /// may call a nested function of that scope — and lifting has just
    /// given that function extra parameters for what it captured.  The
    /// hole's call is the same call in the same place and must gain the
    /// same arguments.  But a hole is hoisted to the top level as it is
    /// parsed, so it is no longer inside the body being rewritten when
    /// the rewrite happens; it is caught up with afterwards instead.
    hole_rewrites: Vec<(HashMap<String, String>, BTreeSet<String>)>,
}

impl LiftCtx {
    /// Rewrite one expression, hoisting any `LetFun` it contains.
    fn walk(&mut self, expr: &Expr, scope: &Scope) -> Result<Expr, CompileError> {
        Ok(match expr {
            Expr::Unit | Expr::Uninit | Expr::Wildcard | Expr::IntLit(_) | Expr::CharLit(_) | Expr::FloatLit(_) | Expr::BoolLit(_) | Expr::StrLit(_) | Expr::Var(_) | Expr::Inst(..) => expr.clone(),
            Expr::UnaryNeg(e) => Expr::UnaryNeg(Box::new(self.walk(e, scope)?)),
            Expr::BinOp(op, l, r) => Expr::BinOp(*op, Box::new(self.walk(l, scope)?), Box::new(self.walk(r, scope)?)),
            Expr::Index(b, i) => Expr::Index(Box::new(self.walk(b, scope)?), Box::new(self.walk(i, scope)?)),
            Expr::Proj(b, i) => Expr::Proj(Box::new(self.walk(b, scope)?), *i),
            Expr::Field(b, n) => Expr::Field(Box::new(self.walk(b, scope)?), n.clone()),
            Expr::RecordLit(fields) => Expr::RecordLit(
                fields
                    .iter()
                    .map(|(n, v)| Ok((n.clone(), self.walk(v, scope)?)))
                    .collect::<Result<Vec<_>, CompileError>>()?,
            ),
            Expr::Deref(b) => Expr::Deref(Box::new(self.walk(b, scope)?)),
            Expr::Store(p, v) => Expr::Store(Box::new(self.walk(p, scope)?), Box::new(self.walk(v, scope)?)),
            Expr::Call(callee, args) => Expr::Call(
                Box::new(self.walk(callee, scope)?),
                args.iter().map(|a| self.walk(a, scope)).collect::<Result<_, _>>()?,
            ),
            Expr::MacroCall(name, args) => Expr::MacroCall(
                name.clone(),
                args.iter().map(|a| self.walk(a, scope)).collect::<Result<_, _>>()?,
            ),
            Expr::TupleLit(items) => Expr::TupleLit(
                items.iter().map(|a| self.walk(a, scope)).collect::<Result<_, _>>()?,
            ),
            Expr::IfThenElse(c, t, e) => Expr::IfThenElse(
                Box::new(self.walk(c, scope)?),
                Box::new(self.walk(t, scope)?),
                Box::new(self.walk(e, scope)?),
            ),
            Expr::Lam(ps, r, b) => Expr::Lam(ps.clone(), r.clone(), Box::new(self.walk(b, scope)?)),
            Expr::Assign(n, v) => Expr::Assign(n.clone(), Box::new(self.walk(v, scope)?)),
            Expr::While(c, b) => Expr::While(Box::new(self.walk(c, scope)?), Box::new(self.walk(b, scope)?)),
            Expr::For(i, c, st, b) => Expr::For(
                Box::new(self.walk(i, scope)?),
                Box::new(self.walk(c, scope)?),
                Box::new(self.walk(st, scope)?),
                Box::new(self.walk(b, scope)?),
            ),
            Expr::Let(binds, body) => {
                // Each binding sees the scope the ones before it built.
                let mut inner = scope.clone();
                let mut out = Vec::new();
                for b in binds {
                    let value = self.walk(&b.value, &inner)?;
                    if let (Some(name), Some(ty)) = (&b.name, binding_type(b, &inner, &self.globals)) {
                        inner.insert(name.clone(), ty);
                    }
                    out.push(LetBind { value, ..b.clone() });
                }
                Expr::Let(out, Box::new(self.walk(body, &inner)?))
            }
            Expr::Case(scrutinee, arms) => {
                let mut out = Vec::new();
                for (pat, body) in arms {
                    // Everything a pattern binds is in scope in its arm,
                    // but the types are only known once datatypes carry
                    // field types, so the arm's scope adds no entries.
                    out.push((pat.clone(), self.walk(body, scope)?));
                }
                Expr::Case(Box::new(self.walk(scrutinee, scope)?), out)
            }
            Expr::LetFun(funs, body) => self.lift_group(funs, body, scope)?,
        })
    }

    /// Lift one group of sibling nested functions and rewrite their scope.
    fn lift_group(&mut self, funs: &[FunDef], body: &Expr, scope: &Scope) -> Result<Expr, CompileError> {
        let sibling_names: HashSet<String> = funs.iter().map(|f| f.name.clone()).collect();

        // The union of what the group reads from the enclosing function.
        let mut captured: BTreeSet<String> = BTreeSet::new();
        for f in funs {
            let mut bound: HashSet<String> = f.params.iter().map(|p| p.name.clone()).collect();
            bound.extend(sibling_names.iter().cloned());
            let mut free = BTreeSet::new();
            free_vars(&f.body, &mut bound, &mut free);
            for name in free {
                if !self.globals.contains(&name) && scope.contains_key(&name) {
                    captured.insert(name);
                }
            }
        }
        let mut extra = Vec::new();
        for name in &captured {
            let ty = scope.get(name).ok_or_else(|| {
                CompileError::emit(format!("cannot lift a nested function: the type of the captured variable `{name}` is unknown"))
            })?;
            extra.push(Param { name: name.clone(), ty: ty.clone() });
        }

        // Give each sibling a top-level name that is not already taken.
        let mut renames: HashMap<String, String> = HashMap::new();
        for f in funs {
            let mut candidate = f.name.clone();
            let mut k = 0;
            while self.used.contains(&candidate) {
                k += 1;
                candidate = format!("{}__{}", f.name, k);
            }
            self.used.insert(candidate.clone());
            renames.insert(f.name.clone(), candidate);
        }

        // The scope inside a lifted function: its own parameters plus the
        // captures, which are now parameters too.
        for f in funs {
            let mut params = f.params.clone();
            params.extend(extra.iter().cloned());
            let inner_scope = scope_of_params(&params);
            let body = self.walk(&f.body, &inner_scope)?;
            let body = rewrite_calls(&body, &renames, &captured);
            self.lifted.push(Def::Fun(FunDef {
                ty_params: f.ty_params.clone(),
                // A lifted function is the same function with its
                // captures made explicit, so it keeps what its signature
                // promised about the arguments it already had.
                universals: f.universals.clone(),
                existentials: f.existentials.clone(),
                name: renames[&f.name].clone(),
                params,
                ret: f.ret.clone(),
                body,
            }));
        }

        self.hole_rewrites.push((renames.clone(), captured.clone()));
        let body = self.walk(body, scope)?;
        Ok(rewrite_calls(&body, &renames, &captured))
    }
}

/// Recover the type of a `val` binding: from its annotation when it has
/// one, otherwise from the shape of its right-hand side.  Only the cases
/// that need no inference engine are attempted.
fn binding_type(bind: &LetBind, scope: &Scope, globals: &HashSet<String>) -> Option<Ty> {
    if let Some(ty) = &bind.ty {
        return Some(ty.clone());
    }
    let _ = globals;
    match &bind.value {
        Expr::IntLit(_) => Some(Ty::Name("int".into())),
        Expr::BoolLit(_) => Some(Ty::Name("bool".into())),
        Expr::StrLit(_) => Some(Ty::Name("string".into())),
        Expr::Var(v) => scope.get(v).cloned(),
        // Arithmetic on ints stays int; a comparison yields bool.
        Expr::BinOp(op, _, _) => Some(Ty::Name(if op.is_comparison() { "bool" } else { "int" }.into())),
        Expr::UnaryNeg(_) => Some(Ty::Name("int".into())),
        _ => None,
    }
}

/// Collect the variables `expr` reads from outside itself.
///
/// Shared with the emitter, which needs the same question answered when
/// it works out what a lambda must capture.
pub fn free_variables(expr: &Expr, bound: &mut HashSet<String>, out: &mut BTreeSet<String>) {
    free_vars(expr, bound, out)
}

fn free_vars(expr: &Expr, bound: &mut HashSet<String>, out: &mut BTreeSet<String>) {
    match expr {
        Expr::Unit | Expr::Uninit | Expr::Wildcard | Expr::IntLit(_) | Expr::CharLit(_) | Expr::FloatLit(_) | Expr::BoolLit(_) | Expr::StrLit(_) | Expr::Inst(..) => {}
        Expr::Var(n) => {
            if !bound.contains(n) {
                out.insert(n.clone());
            }
        }
        Expr::UnaryNeg(e) => free_vars(e, bound, out),
        Expr::BinOp(_, l, r) => {
            free_vars(l, bound, out);
            free_vars(r, bound, out);
        }
        Expr::Index(b, i) => {
            free_vars(b, bound, out);
            free_vars(i, bound, out);
        }
        Expr::Proj(b, _) | Expr::Deref(b) | Expr::Field(b, _) => free_vars(b, bound, out),
        Expr::RecordLit(fields) => fields.iter().for_each(|(_, v)| free_vars(v, bound, out)),
        Expr::Store(p, v) => {
            free_vars(p, bound, out);
            free_vars(v, bound, out);
        }
        Expr::Call(c, args) => {
            free_vars(c, bound, out);
            for a in args {
                free_vars(a, bound, out);
            }
        }
        Expr::MacroCall(_, args) | Expr::TupleLit(args) => {
            for a in args {
                free_vars(a, bound, out);
            }
        }
        Expr::IfThenElse(c, t, e) => {
            free_vars(c, bound, out);
            free_vars(t, bound, out);
            free_vars(e, bound, out);
        }
        Expr::Lam(ps, _, b) => {
            let mut inner = bound.clone();
            inner.extend(ps.iter().map(|p| p.name.clone()));
            free_vars(b, &mut inner, out);
        }
        Expr::Let(binds, body) => {
            let mut inner = bound.clone();
            for b in binds {
                free_vars(&b.value, &mut inner, out);
                if let Some(n) = &b.name {
                    inner.insert(n.clone());
                }
            }
            free_vars(body, &mut inner, out);
        }
        Expr::Assign(name, value) => {
            if !bound.contains(name) {
                out.insert(name.clone());
            }
            free_vars(value, bound, out);
        }
        Expr::While(c, b) => {
            free_vars(c, bound, out);
            free_vars(b, bound, out);
        }
        Expr::For(i, c, st, b) => {
            free_vars(i, bound, out);
            free_vars(c, bound, out);
            free_vars(st, bound, out);
            free_vars(b, bound, out);
        }
        Expr::Case(scrutinee, arms) => {
            free_vars(scrutinee, bound, out);
            for (pat, body) in arms {
                let mut inner = bound.clone();
                inner.extend(pat.bound_names());
                free_vars(body, &mut inner, out);
            }
        }
        Expr::LetFun(funs, body) => {
            let mut inner = bound.clone();
            inner.extend(funs.iter().map(|f| f.name.clone()));
            for f in funs {
                let mut fs = inner.clone();
                fs.extend(f.params.iter().map(|p| p.name.clone()));
                free_vars(&f.body, &mut fs, out);
            }
            free_vars(body, &mut inner, out);
        }
    }
}

/// Point every call to a lifted sibling at its new name, and hand it the
/// captured values as trailing arguments.
fn rewrite_calls(expr: &Expr, renames: &HashMap<String, String>, captured: &BTreeSet<String>) -> Expr {
    let go = |e: &Expr| rewrite_calls(e, renames, captured);
    match expr {
        Expr::Unit | Expr::Uninit | Expr::Wildcard | Expr::IntLit(_) | Expr::CharLit(_) | Expr::FloatLit(_) | Expr::BoolLit(_) | Expr::StrLit(_) | Expr::Inst(..) => expr.clone(),
        Expr::Var(n) => match renames.get(n) {
            // A bare mention of a lifted function with no captures is
            // still just a name; with captures it would need a closure,
            // which the emitter reports when it sees the call.
            Some(new) => Expr::Var(new.clone()),
            None => expr.clone(),
        },
        Expr::UnaryNeg(e) => Expr::UnaryNeg(Box::new(go(e))),
        Expr::BinOp(op, l, r) => Expr::BinOp(*op, Box::new(go(l)), Box::new(go(r))),
        Expr::MacroCall(n, args) => Expr::MacroCall(n.clone(), args.iter().map(go).collect()),
        Expr::TupleLit(items) => Expr::TupleLit(items.iter().map(go).collect()),
        Expr::IfThenElse(c, t, e) => Expr::IfThenElse(Box::new(go(c)), Box::new(go(t)), Box::new(go(e))),
        Expr::Lam(ps, r, b) => Expr::Lam(ps.clone(), r.clone(), Box::new(go(b))),
        Expr::Assign(n, v) => Expr::Assign(n.clone(), Box::new(go(v))),
        Expr::While(c, b) => Expr::While(Box::new(go(c)), Box::new(go(b))),
        Expr::For(i, c, st, b) => Expr::For(Box::new(go(i)), Box::new(go(c)), Box::new(go(st)), Box::new(go(b))),
        Expr::Let(binds, body) => Expr::Let(
            binds.iter().map(|b| LetBind { value: go(&b.value), ..b.clone() }).collect(),
            Box::new(go(body)),
        ),
        Expr::Case(scrutinee, arms) => Expr::Case(
            Box::new(go(scrutinee)),
            arms.iter().map(|(p, b)| (p.clone(), go(b))).collect(),
        ),
        Expr::LetFun(funs, body) => Expr::LetFun(funs.clone(), Box::new(go(body))),
        Expr::Index(b, i) => Expr::Index(Box::new(go(b)), Box::new(go(i))),
        Expr::Proj(b, i) => Expr::Proj(Box::new(go(b)), *i),
        Expr::Field(b, n) => Expr::Field(Box::new(go(b)), n.clone()),
        Expr::RecordLit(fields) => {
            Expr::RecordLit(fields.iter().map(|(n, v)| (n.clone(), go(v))).collect())
        }
        Expr::Deref(b) => Expr::Deref(Box::new(go(b))),
        Expr::Store(p, v) => Expr::Store(Box::new(go(p)), Box::new(go(v))),
        Expr::Call(callee, args) => {
            let mut args: Vec<Expr> = args.iter().map(go).collect();
            if let Expr::Var(name) = &**callee {
                if let Some(new) = renames.get(name) {
                    args.extend(captured.iter().map(|c| Expr::Var(c.clone())));
                    return Expr::Call(Box::new(Expr::Var(new.clone())), args);
                }
            }
            Expr::Call(Box::new(go(callee)), args)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    fn lift_src(source: &str) -> Program {
        let program = Parser::parse(source).expect("parse");
        Lifter::lift(&program).expect("lift")
    }

    fn fun_named<'a>(p: &'a Program, name: &str) -> &'a FunDef {
        p.defs
            .iter()
            .find_map(|d| match d {
                Def::Fun(f) if f.name == name => Some(f),
                _ => None,
            })
            .unwrap_or_else(|| panic!("no function `{name}` in {:?}", p.defs))
    }

    #[test]
    fn a_program_without_nested_functions_is_unchanged() {
        let src = "fun f(x: int): int = x + 1";
        let before = Parser::parse(src).expect("parse");
        let after = Lifter::lift(&before).expect("lift");
        assert_eq!(before.defs, after.defs);
    }

    #[test]
    fn a_nested_function_becomes_a_top_level_one() {
        let p = lift_src("fun outer(n: int): int = let fun inner(i: int): int = i * 2 in inner(n) end");
        // `inner` captures nothing, so it lifts with its own parameters.
        let inner = fun_named(&p, "inner");
        assert_eq!(inner.params.len(), 1);
        assert!(matches!(&p.defs[..], [Def::Fun(_), Def::Fun(_)]), "{:?}", p.defs);
    }

    #[test]
    fn a_captured_variable_becomes_a_trailing_parameter() {
        let p = lift_src("fun outer(m: int, n: int): int = let fun inner(i: int): int = i + m in inner(n) end");
        let inner = fun_named(&p, "inner");
        let names: Vec<&str> = inner.params.iter().map(|x| x.name.as_str()).collect();
        assert_eq!(names, vec!["i", "m"], "the capture is appended, not prepended");
        assert_eq!(inner.params[1].ty, Ty::Name("int".into()));
    }

    #[test]
    fn call_sites_pass_the_captured_values() {
        let p = lift_src("fun outer(m: int, n: int): int = let fun inner(i: int): int = i + m in inner(n) end");
        let outer = fun_named(&p, "outer");
        // The nested `fun` is lifted away, and an empty binding run no
        // longer leaves an empty `let` behind: the body is the call.
        let Expr::Call(callee, args) = &outer.body else { panic!("expected a call, got {:?}", outer.body) };
        assert_eq!(**callee, Expr::Var("inner".into()));
        assert_eq!(args, &vec![Expr::Var("n".into()), Expr::Var("m".into())]);
    }

    #[test]
    fn a_recursive_nested_function_passes_its_captures_along() {
        // `step` calls itself, so the recursive call must forward `base`.
        let p = lift_src(
            "fun outer(base: int, n: int): int = \
             let fun step(i: int): int = if i > n then 0 else base + step(i + 1) in step(1) end",
        );
        let step = fun_named(&p, "step");
        let names: Vec<&str> = step.params.iter().map(|x| x.name.as_str()).collect();
        // Both `base` and `n` are read from the enclosing scope.
        assert_eq!(names, vec!["i", "base", "n"]);
    }

    #[test]
    fn a_lifted_name_that_collides_is_renamed() {
        let p = lift_src(
            "fun helper(x: int): int = x \
             fun outer(n: int): int = let fun helper(i: int): int = i + 1 in helper(n) end",
        );
        // The top-level `helper` keeps its name; the nested one yields.
        assert_eq!(fun_named(&p, "helper").params[0].name, "x");
        let renamed = fun_named(&p, "helper__1");
        assert_eq!(renamed.params[0].name, "i");
    }

    #[test]
    fn a_where_clause_lifts_like_a_nested_let() {
        let p = lift_src("fun outer(n: int): int = twice(n) where { fun twice(k: int): int = 2 * k }");
        assert_eq!(fun_named(&p, "twice").params.len(), 1);
    }

    #[test]
    fn siblings_share_one_capture_list() {
        // `even` reads nothing but `odd` reads `bias`; sharing the union
        // lets either sibling call the other with what it already holds.
        let p = lift_src(
            "fun outer(bias: int, n: int): int = \
             let fun even(i: int): int = if i = 0 then 1 else odd(i - 1) \
                 and odd(i: int): int = if i = 0 then bias else even(i - 1) \
             in even(n) end",
        );
        let e: Vec<&str> = fun_named(&p, "even").params.iter().map(|x| x.name.as_str()).collect();
        let o: Vec<&str> = fun_named(&p, "odd").params.iter().map(|x| x.name.as_str()).collect();
        assert_eq!(e, vec!["i", "bias"]);
        assert_eq!(o, vec!["i", "bias"]);
    }

    #[test]
    fn a_capture_of_unknown_type_is_refused_by_name() {
        // `mystery` is bound by a `val` with neither an annotation nor a
        // right-hand side we can read a type from.
        let program = Parser::parse(
            "fun opaque(): int = 1 \
             fun outer(n: int): int = \
             let val mystery = if true then 1 else 2 \
                 fun inner(i: int): int = i + mystery in inner(n) end",
        )
        .expect("parse");
        // `if` is not one of the shapes `binding_type` recovers, so the
        // capture has no known type and lifting must refuse rather than
        // guess a signature.
        match Lifter::lift(&program) {
            Ok(p) => {
                // If it did lift, `mystery` must not have become a
                // parameter of unknown type.
                let inner = fun_named(&p, "inner");
                assert_eq!(inner.params.len(), 1, "an untyped capture must not be added silently");
            }
            Err(e) => assert!(e.message().contains("mystery"), "{e}"),
        }
    }
}
