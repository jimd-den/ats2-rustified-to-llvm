//! # The walk — every claim a program makes, written down
//!
//! *Literate note.*  This is the checker proper, and it does exactly one
//! thing: it goes through a program once and records what would have to
//! be true for it to be correct.  It never decides whether those things
//! *are* true (that is [`crate::constraints`]) and never decides what to
//! do when they are not (that is [`super::policy`]).  Three modules, three
//! reasons to change, and the arithmetic can be replaced without touching
//! a single typing rule.
//!
//! Two ideas carry the whole file.
//!
//! **Every value has a static term, even the unknown ones.**  A value the
//! walk cannot pin down gets a fresh variable rather than a hole, so it
//! can still be *related* to itself — which is what makes `val y = f(x)`
//! followed by `g(y, y)` provable without anybody knowing what `y` is.
//!
//! **Facts belong to paths, not to programs.**  The environment is
//! copied at every branch, so what the then-branch learned is unavailable
//! to the else-branch by construction rather than by discipline.  This is
//! the difference between a checker that can read `if x > 0` and one that
//! cannot, and reading `if x > 0` is most of what dependent ATS is for.
//!
//! What it does *not* do is guess.  A demand it cannot instantiate stays
//! written in terms nobody can prove, and comes out of the solver as
//! `Unknown` — which the policy layer will report or forgive, but which
//! is never quietly discarded here.

use std::collections::HashMap;

use ats2_domain::ast::{BinOp, Def, Expr, FunDef, LetBind, Param, Pattern, Program, Ty};
use ats2_domain::obligation::{Obligation, Origin};
use ats2_domain::statics::{Quant, SExp, Sort};

use super::index_env::IndexEnv;
use super::prop::{negate, relation};
use super::signatures::{
    Arg, CallFacts, CtorTable, SELF, SigTable, Signature, claim_of, declared_for,
    entry_point_indices, is_singleton_indexed, strip_index,
};
use super::unify::Match;

/// Every obligation a program incurs.
///
/// `ambient` is checked for signatures and nothing else: it is where the
/// prelude's declarations come from, and the prelude's own bodies are
/// not this program's business.
pub fn obligations(program: &Program, ambient: &Program) -> Vec<Obligation> {
    // The program's own declarations are laid over the ambient ones, so
    // a name a program declares for itself is the program's.  The prelude
    // fills gaps; it does not shadow.
    let mut sigs = SigTable::of(ambient);
    sigs.extend(SigTable::of(program));
    let mut ctors = CtorTable::of(ambient);
    ctors.extend(CtorTable::of(program));
    // `#define N 1024` is not a variable: every mention of `N` *is* the
    // number, settled before the program runs.  Reading it as an unknown
    // would leave the checker unable to prove the one thing a named
    // constant is written to make obvious.
    let consts: HashMap<String, SExp> = ambient
        .defs()
        .iter()
        .chain(program.defs())
        .filter_map(|d| match d {
            Def::Const(c) => index_of_literal(&c.value).map(|t| (c.name.clone(), t)),
            _ => None,
        })
        .collect();
    let mut walk = Walk {
        sigs: &sigs,
        local_sigs: Vec::new(),
        ctors: &ctors,
        consts,
        out: Vec::new(),
        function: String::new(),
        metric: Vec::new(),
        last_call: None,
    };
    // Typed top-level values are in scope in every function, just as
    // top-level function declarations are. Their indices matter: the
    // canonical example is `val the_null_ptr: ptr(null)`, whose identity is
    // what lets a comparison produce `bool(l == null)`. Collect ambient
    // values first and let the program's own declaration of a name win.
    let global_types: HashMap<String, Ty> = ambient
        .defs()
        .iter()
        .chain(program.defs())
        .filter_map(|definition| match definition {
            Def::Val(value) => value
                .ty
                .as_ref()
                .map(|ty| (value.name.clone(), ty.clone())),
            _ => None,
        })
        .collect();
    let mut globals = IndexEnv::new();
    for (name, ty) in global_types {
        walk.bind_param(&name, &ty, &mut globals);
    }
    for def in program.defs() {
        match def {
            Def::Fun(f) => walk.function_def(f, globals.clone()),
            Def::Implement(im) => {
                // An implementation answers to the declaration it fills
                // in, which is where the quantifiers were written.
                let (universals, params, existentials, ret) = declared_for(sigs.get(&im.name), im);
                walk.body(
                    &im.name,
                    &universals,
                    &params,
                    ret,
                    &existentials,
                    &im.body,
                    globals.clone(),
                    // An `implement` fills in a function, never a proof.
                    false,
                );
            }
            Def::Val(val) => {
                let mut env = globals.clone();
                walk.function = val.name.clone();
                let _ = walk.expr(&val.value, &mut env);
            }
            _ => {}
        }
    }
    walk.out
}

pub(crate) struct Walk<'a> {
    pub(crate) sigs: &'a SigTable,
    /// Function signatures introduced by nested `let fun` groups.
    ///
    /// The innermost scope comes last. Postiats deliberately reuses names
    /// such as `loop`, `aux` and `auxlst`; putting those in the global table
    /// makes an unrelated helper elsewhere in the module overwrite them.
    pub(crate) local_sigs: Vec<HashMap<String, Signature>>,
    /// What each constructor takes apart into.
    pub(crate) ctors: &'a CtorTable,
    /// The `#define`d constants, by name.
    pub(crate) consts: HashMap<String, SExp>,
    pub(crate) out: Vec<Obligation>,
    /// Whose body is being walked — the half of a diagnostic no solver
    /// could reconstruct.
    pub(crate) function: String,
    /// That function's `.<n>.` metric, read at its entry.  A recursive
    /// call must be shown to have come down from this.
    pub(crate) metric: Vec<SExp>,
    /// What the most recent call reported.
    ///
    /// A binding needs more than the single index a value has: a *proof*
    /// carries one index per number its proposition is about, and an
    /// *opening* names the witness the call invented.  Both are on the
    /// call's own report, and the binding is the next thing to run.
    pub(crate) last_call: Option<CallFacts>,
}

impl<'a> Walk<'a> {
    /// Make a mutually recursive local function group visible as one lexical
    /// scope. Both ordinary and result-directed expression walks must use the
    /// same operation or dependent return checking loses local signatures.
    fn enter_local_functions(&mut self, funs: &[FunDef]) {
        let scope = funs
            .iter()
            .map(|f| (f.name.clone(), Signature::of_fun(f)))
            .collect();
        self.local_sigs.push(scope);
    }

    fn leave_local_functions(&mut self) {
        self.local_sigs.pop();
    }

    fn demand(&mut self, goal: SExp, origin: Origin, env: &IndexEnv) {
        self.out
            .push(Obligation::new(env.hyps().to_vec(), goal, origin));
    }

    /// Check one `fun`, starting from `enclosing` — the scope it was
    /// written inside.
    ///
    /// A nested function reads the names around it, and those names have
    /// types and indices at the point it was written.  Checking it in a
    /// scope of its own makes every captured value an unknown, and a
    /// nested loop — which is how ATS writes nearly every one — goes
    /// unchecked. A top-level `fun` captures nothing, and starts empty.
    fn function_def(&mut self, f: &FunDef, enclosing: IndexEnv) {
        let outer = std::mem::replace(&mut self.metric, f.metric.clone());
        self.body(
            &f.name,
            &f.universals,
            &f.params,
            f.ret.clone(),
            &f.existentials,
            &f.body,
            enclosing,
            f.proof,
        );
        self.metric = outer;
    }

    /// Check one body against one signature.
    ///
    /// The universals arrive as *hypotheses*: a caller had to establish
    /// them, so the body may spend them.  That asymmetry — demanded
    /// outside, assumed inside — is the whole content of a dependent
    /// function type.
    fn body(
        &mut self,
        name: &str,
        universals: &[Quant],
        params: &[Param],
        ret: Ty,
        existentials: &[Quant],
        body: &Expr,
        mut env: IndexEnv,
        // Whether the body is a *derivation* rather than a computation.
        proof: bool,
    ) {
        for q in universals {
            for (var, sort) in &q.vars {
                env.declare(var, sort);
            }
            env.assume_all(q.guard.clone());
        }
        for p in params {
            self.bind_param(&p.name, &p.ty, &mut env);
        }
        // The entry point's own signature, which its source never writes.
        if let Some(entry) = entry_point_indices(name, params) {
            // `argv[0]` is the program's own name, so the count is
            // never zero.  A `nat` here would leave the fallback branch
            // of every `if argc >= 2` unable to reach `argv[0]`.
            env.declare(&entry.count.1.to_string(), &Sort::Pos);
            env.bind(&entry.count.0, entry.count.1);
            env.bind_size(&entry.argv.0, entry.argv.1);
        }
        let outer = std::mem::replace(&mut self.function, name.to_string());
        match claim_of(&ret) {
            Some(claim) => {
                let promise = Promise {
                    claim,
                    proposition: ret.proof().and_then(proposition_indices),
                    witnesses: witnesses_of(existentials),
                    hypotheses: existentials.iter().flat_map(Quant::hypotheses).collect(),
                    origin: Origin::Return {
                        function: name.to_string(),
                    },
                };
                self.check_against(body, &promise, &mut env);
            }
            // Nothing was promised about the value, so there is nothing
            // to check — but the body still has to be walked, because
            // everything *inside* it makes claims of its own.
            None => {
                // Unless the body is a proof.  A proposition makes no
                // claim about a *value* — a proof is not one — so
                // `claim_of` has nothing to say about `FACT(0, 1)` and
                // the walk would pass over the one thing a `prfun`
                // asserts.  What it asserts is that the derivation
                // establishes *these* indices, so that is what is
                // demanded: term by term, the proof term's own indices
                // against the ones the proposition was written with.
                //
                // Without this a `prfun` is a `praxi` that took longer
                // to write, and every derivation is believed because it
                // was offered.
                if proof {
                    self.derives(&ret, body, name, &mut env);
                } else {
                    self.expr(body, &mut env);
                }
            }
        }
        self.function = outer;
    }

    /// A derivation, held against the proposition it claims to prove.
    ///
    /// The proof term is read for the indices it actually establishes
    /// and each is demanded equal to the one the proposition was written
    /// with.  A term whose indices are unknown demands nothing: the walk
    /// reports the program's mistakes, not its own ignorance.
    fn derives(&mut self, ret: &Ty, body: &Expr, name: &str, env: &mut IndexEnv) {
        let promised = proposition_indices(ret).unwrap_or_default();
        let (supplied, open) = self.proof_indices(body, env);
        if promised.is_empty() || supplied.len() != promised.len() {
            return;
        }
        // A derivation may carry variables of its own that nothing
        // determined.  `MULbas` witnesses `{n:int} MUL(0, n, 0)` and
        // takes no argument, so `n` comes back unspellable and the
        // demand reads `n == n%0` — unprovable, and refused under the
        // strict policy, which is every nullary proof constructor with a
        // quantifier of its own.
        //
        // The proposition being promised is where the answer is.  The
        // constructor is universally quantified over those variables, so
        // reading them off the promise is instantiating it, not assuming
        // it: whatever `MUL(0, n, 0)` the caller asked for, that is the
        // `n` the derivation was offered at.
        let mut m = Match::default();
        for (p, a) in promised.iter().zip(&supplied) {
            m.against(a, p, &open);
        }
        let subst = m.subst();
        let origin = Origin::Return {
            function: name.to_string(),
        };
        for (p, a) in promised.iter().zip(&supplied) {
            self.demand(
                SExp::App("==".into(), vec![p.clone(), a.substitute(&subst)]),
                origin.clone(),
                env,
            );
        }
    }

    /// Give a parameter the indices its type wrote, or a name of its own
    /// when the type wrote none.
    ///
    /// An unindexed parameter is not *nothing* — `fun f (x: int)` still
    /// hands the body one particular integer, and naming it is what lets
    /// `f` prove that `x` equals `x`.
    fn bind_param(&mut self, name: &str, ty: &Ty, env: &mut IndexEnv) {
        // The whole type is kept, because indices live at every depth of
        // one and a call matches the whole of a parameter's type against
        // the whole of an argument's.
        env.bind_type(name, ty.clone());
        let indices = ty.indices();
        if !indices.is_empty() {
            env.bind_all(name, indices.to_vec());
        }
        // `int(n)`: the value *is* `n`, and nothing else need be said.
        if let Ty::Index(base, _) = ty {
            if is_singleton_indexed(base) {
                env.bind(name, indices[0].clone());
                return;
            }
        }
        // Everything else has an identity of its own.  What the type
        // then says about it is either a bound — `natLt(n)` and bare
        // `Nat` alike, which is what makes `xs[i]` safe — or a measure,
        // which is its length.  An unindexed type may still bound it:
        // the whole content of `Nat` is its refinement.
        let me = env.fresh(name);
        env.bind(name, me.clone());
        match claim_of(ty) {
            Some(claim) => env.assume(about(&claim, &me)),
            None => {
                if let Some(size) = indices.last() {
                    env.bind_size(name, size.clone());
                    // A value of this type exists, so its length counted
                    // something: lengths are not negative.  ATS makes a
                    // program ask for this with `prval () =
                    // lemma_list_param (xs)`; it follows from the value
                    // being there at all, so it is simply known.
                    env.assume(SExp::App(">=".into(), vec![size.clone(), SExp::IntLit(0)]));
                }
            }
        }
    }

    /// Check an expression *against* a promise, rather than asking what
    /// its index is and comparing afterwards.
    ///
    /// The distinction is the difference between a checker that reads
    /// `if` and one that walks past it.  A branch, a `case` and a `let`
    /// have no index of their own worth speaking of — the arms disagree,
    /// so any single answer is a fresh unknown and the promise becomes
    /// unprovable.  Pushed *inward*, each arm answers for the promise
    /// under its own guard, which is exactly the reasoning the source
    /// was written with.
    ///
    /// Everything else has an index, and there the promise is settled.
    fn check_against(&mut self, e: &Expr, promise: &Promise, env: &mut IndexEnv) {
        let (claim, witnesses, hypotheses, origin) = (
            &promise.claim,
            &promise.witnesses,
            &promise.hypotheses,
            &promise.origin,
        );
        match e {
            // `(pf | v)` — the proof half is what determines the
            // existential the signature promised.  `[r:int] (P(n,r) |
            // int(r*k))` names `r` in the proposition *and* multiplies
            // by it in the value; reading it out of the arithmetic would
            // need division, and reading it out of the proposition needs
            // only a match.  This is what a `dataprop` is for.
            Expr::ProofPair(proof, value) => {
                let (supplied, _) = self.proof_indices(proof, env);
                let mut m = Match::default();
                if let (Some(promised), false) = (&promise.proposition, supplied.is_empty()) {
                    for (p, a) in promised.iter().zip(&supplied) {
                        m.against(p, a, witnesses);
                    }
                }
                let subst = m.subst();
                let settled = Promise {
                    claim: claim.substitute(&subst),
                    proposition: None,
                    witnesses: witnesses
                        .iter()
                        .filter(|w| m.get(w).is_none())
                        .cloned()
                        .collect(),
                    hypotheses: hypotheses.iter().map(|h| h.substitute(&subst)).collect(),
                    origin: origin.clone(),
                };
                self.check_against(value, &settled, env);
            }
            Expr::IfThenElse(c, t, f) => {
                let guard = self.expr(c, env);
                let mut taken = env.clone();
                let mut untaken = env.clone();
                if let Some(g) = &guard {
                    taken.assume(g.clone());
                    untaken.assume(negate(g));
                }
                self.check_against(t, promise, &mut taken);
                self.check_against(f, promise, &mut untaken);
            }
            Expr::Case(scrutinee, arms) => {
                let subject = self.expr(scrutinee, env);
                let subject_ty = type_of_expr(scrutinee, env);
                for (pattern, body) in arms {
                    let mut arm = env.clone();
                    self.refine(pattern, subject.as_ref(), subject_ty.as_ref(), &mut arm);
                    self.check_against(body, promise, &mut arm);
                }
            }
            // A body is usually `let ... in <the answer> end`, so the
            // promise has to travel through the bindings to reach it.
            Expr::Let(binds, rest) => {
                for b in binds {
                    self.let_bind(b, env);
                }
                self.check_against(rest, promise, env);
            }
            Expr::LetFun(funs, rest) => {
                self.enter_local_functions(funs);
                for f in funs {
                    self.function_def(f, env.clone());
                }
                self.check_against(rest, promise, env);
                self.leave_local_functions();
            }
            Expr::Call(callee, args) => {
                let expected = match claim {
                    SExp::App(op, parts)
                        if op == "=="
                            && parts.len() == 2
                            && parts[0] == SExp::Var(SELF.into()) =>
                    {
                        Some(parts[1].clone())
                    }
                    _ => None,
                };
                let produced = self.call(callee, args, expected.as_ref(), env);
                self.settle(claim, witnesses, hypotheses, produced, origin, env);
            }
            _ => {
                let produced = self.expr(e, env);
                self.settle(claim, witnesses, hypotheses, produced, origin, env);
            }
        }
    }

    /// Every index a proof term is indexed by.
    ///
    /// A proof is not a value and has no single index: `FACT(n, n*r)`
    /// proves a claim about two numbers, and both are what the promised
    /// proposition is matched against.
    /// Every index a proof term is indexed by, and the variables of its
    /// own that are still open.
    ///
    /// A derivation may carry variables the call could not determine —
    /// `{n:int} MULbas (0, n, 0)` has one, and no argument to read it
    /// from.  They come back under unspellable names, and naming them is
    /// what lets the caller determine them from the proposition it
    /// promised.
    fn proof_indices(&mut self, e: &Expr, env: &mut IndexEnv) -> (Vec<SExp>, Vec<String>) {
        if let Expr::Var(name) = e {
            return (env.indices_of(name), Vec::new());
        }
        self.last_call = None;
        self.expr(e, env);
        self.last_call
            .take()
            .map(|f| (f.result_indices, f.renamed))
            .unwrap_or_default()
    }

    /// One value against one claim.
    ///
    /// With existentials the direction reverses: `: [r:nat] int r` does
    /// not demand a particular `r`, it demands that the one the body
    /// produced satisfies the guard.  So the body's term *determines* the
    /// witness, and what is left over is the claim.
    fn settle(
        &mut self,
        claim: &SExp,
        witnesses: &[String],
        hypotheses: &[SExp],
        produced: Option<SExp>,
        origin: &Origin,
        env: &IndexEnv,
    ) {
        let Some(produced) = produced else {
            // Nothing is known about what came back, so the claim cannot
            // be made good — say so in the claim's own terms.
            self.demand(claim.clone(), origin.clone(), env);
            return;
        };
        // A singleton claim — `%self == P` — also *determines* the
        // existential witnesses, by matching `P` against what the body
        // produced.  A refinement claim binds nothing and is simply
        // asked of the value.
        let mut m = Match::default();
        if let SExp::App(op, args) = claim {
            if op == "==" && args.len() == 2 && args[0] == SExp::Var(SELF.into()) {
                m.against(&args[1], &produced, witnesses);
            }
        }
        let subst = m.subst();
        for h in hypotheses {
            self.demand(h.substitute(&subst), origin.clone(), env);
        }
        self.demand(
            about(&claim.substitute(&subst), &produced),
            origin.clone(),
            env,
        );
    }

    /// The static term an expression's value has, recording on the way
    /// every claim reaching it requires.
    fn expr(&mut self, e: &Expr, env: &mut IndexEnv) -> Option<SExp> {
        match e {
            Expr::IntLit(n) => Some(SExp::IntLit(*n)),
            Expr::BoolLit(b) => Some(SExp::BoolLit(*b)),
            // A name is what the scope says it is; failing that, it may
            // be a compile-time constant, which is a number.
            Expr::Var(n) => env.index_of(n).or_else(|| self.consts.get(n).cloned()),
            Expr::UnaryNeg(a) => {
                let a = self.expr(a, env)?;
                Some(SExp::App("~".into(), vec![a]))
            }
            Expr::BinOp(op, l, r) => self.binop(*op, l, r, env),
            Expr::Call(callee, args) => self.call(callee, args, None, env),
            Expr::Index(subject, at) => self.subscript(subject, at, env),
            Expr::IfThenElse(c, t, f) => self.conditional(c, t, f, env),
            Expr::Case(scrutinee, arms) => self.case(scrutinee, arms, env),
            Expr::Let(binds, rest) => {
                for b in binds {
                    self.let_bind(b, env);
                }
                self.expr(rest, env)
            }
            Expr::LetFun(funs, rest) => {
                self.enter_local_functions(funs);
                for f in funs {
                    self.function_def(f, env.clone());
                }
                let result = self.expr(rest, env);
                self.leave_local_functions();
                result
            }
            Expr::Lam(params, ret, body) => {
                let mut inner = env.clone();
                for p in params {
                    self.bind_param(&p.name, &p.ty, &mut inner);
                }
                match ret.as_ref().map(Ty::indices) {
                    Some([promised]) => {
                        let promise = Promise {
                            claim: SExp::App(
                                "==".into(),
                                vec![SExp::Var(SELF.into()), promised.clone()],
                            ),
                            proposition: None,
                            witnesses: Vec::new(),
                            hypotheses: Vec::new(),
                            origin: Origin::Return {
                                function: self.function.clone(),
                            },
                        };
                        self.check_against(body, &promise, &mut inner);
                    }
                    _ => {
                        self.expr(body, &mut inner);
                    }
                }
                None
            }
            // `e : t` outside a binding is still a claim, and still
            // checked; what it evaluates to is `e`.
            Expr::Ascribe(inner, ty) => {
                let produced = self.expr(inner, env);
                if let (Some(claim), Some(actual)) = (claim_of(ty), &produced) {
                    self.demand(about(&claim, actual), Origin::Annotation, env);
                }
                produced
            }
            Expr::ProofPair(proof, value) => {
                self.expr(proof, env);
                self.expr(value, env)
            }
            Expr::Assign(name, value) => {
                let produced = self.expr(value, env);
                // The old facts are gone whatever happens; the new value
                // replaces them only when it is known.
                env.forget(name);
                if let Some(idx) = produced {
                    env.bind(name, idx);
                }
                None
            }
            Expr::While(cond, body) => self.loop_over(&[cond, body], env),
            Expr::For(init, cond, step, body) => {
                self.expr(init, env);
                self.loop_over(&[cond, step, body], env)
            }
            other => {
                other.each_subexpr(&mut |sub| {
                    self.expr(sub, env);
                });
                None
            }
        }
    }

    /// Arithmetic builds a term; a comparison builds a proposition.  Both
    /// are static terms — `bool` is a sort like any other — which is what
    /// lets `if x > 0` hand its condition straight to the branch.
    fn binop(&mut self, op: BinOp, l: &Expr, r: &Expr, env: &mut IndexEnv) -> Option<SExp> {
        let lhs = self.expr(l, env);
        let rhs = self.expr(r, env);
        let name = match op {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            other => relation(other)?,
        };
        Some(SExp::App(name.into(), vec![lhs?, rhs?]))
    }

    /// A call: instantiate the callee's promise from the arguments, owe
    /// what it demands, and keep what it gives back.
    fn call(
        &mut self,
        callee: &Expr,
        args: &[Expr],
        expected: Option<&SExp>,
        env: &mut IndexEnv,
    ) -> Option<SExp> {
        let supplied: Vec<Arg> = args
            .iter()
            .map(|a| {
                self.last_call = None;
                let value = self.expr(a, env);
                // A length-indexed parameter is determined by how long
                // the argument is, not by what it is, so every fact
                // travels to the signature and it takes the one it
                // wants.  An argument that was never given a name —
                // `g(mk(x))` — carries its indices only in the type the
                // call it came from reported.
                let size = match a {
                    Expr::Var(name) => env.size_of(name),
                    _ => None,
                };
                // A name's type, or what is behind a `!p` or an
                // ascription, or — failing all of those — the type the
                // call this argument came from reported.
                let ty = type_of_expr(a, env)
                    .or_else(|| self.last_call.as_ref().and_then(|f| f.result_ty.clone()));
                Arg { value, size, ty }
            })
            .collect();
        let Some((name, statics, ty_args)) = called_name(callee) else {
            self.expr(callee, env);
            return None;
        };
        // `assertexn(n >= 0)` is how ATS moves a check from run time
        // into the static world: past this line the program has either
        // stopped or the claim holds, so the claim holds.  Nothing else
        // asserts — an ordinary function taking a boolean would
        // otherwise make its argument true by being called.
        // `$UN.cast{T}(e)` — the programmer asserting a type the checker
        // cannot derive, and taking responsibility for it.  That is what
        // `$UNSAFE` means: the claim is *assumed*, the argument owes
        // nothing, and a checker that argued with it would reject every
        // program that reaches for the hatch on purpose.
        if is_unsafe_cast(&name) {
            if let [ty] = &ty_args[..] {
                let me = env.fresh("cast");
                if let Some(claim) = claim_of(ty) {
                    env.assume(about(&claim, &me));
                }
                self.last_call = Some(CallFacts {
                    result_ty: Some(ty.clone()),
                    ..CallFacts::default()
                });
                return Some(me);
            }
        }
        if is_assertion(&name) {
            if let [
                Arg {
                    value: Some(claim), ..
                },
            ] = &supplied[..]
            {
                env.assume(claim.clone());
            }
            return None;
        }
        let declared: &Signature = self
            .local_sigs
            .iter()
            .rev()
            .find_map(|scope| scope.get(&name))
            .or_else(|| self.sigs.get(&name))?;
        // A template's arguments choose which code is built, not which
        // claim is made.  Only a callee that abstracts over no types can
        // have meant an index by them.
        let statics = if declared.ty_params.is_empty() {
            statics
        } else {
            Vec::new()
        };
        // ...and where they *do* choose the code, they also choose what
        // it produces, which is the whole content of naming an instance.
        let sig = declared.at_instance(&ty_args);
        let facts = sig.at_call_against(&statics, &supplied, expected, &env.fresh_supply());
        for goal in facts.demands.clone() {
            self.demand(
                goal,
                Origin::Call {
                    callee: name.clone(),
                },
                env,
            );
        }
        if name == self.function {
            self.check_metric(&facts.metric, env);
        }
        // Only now: what the callee promised is available to whatever
        // reads its result, and not before.
        env.assume_all(facts.assumptions.clone());
        self.last_call = Some(facts);
        self.last_call.as_ref().and_then(|f| f.result.clone())
    }

    /// What an arm learns from having matched.
    fn refine(
        &mut self,
        pattern: &Pattern,
        subject: Option<&SExp>,
        subject_ty: Option<&Ty>,
        env: &mut IndexEnv,
    ) {
        match pattern {
            Pattern::Var(name) => {
                match subject {
                    Some(s) => env.bind(name, s.clone()),
                    None => env.forget(name),
                }
                if let Some(ty) = subject_ty {
                    self.bind_param(name, ty, env);
                }
            }
            // Matching a literal is an equation: inside the arm, the
            // scrutinee *is* that number.
            Pattern::Int(k) => {
                if let Some(s) = subject {
                    env.assume(SExp::App("==".into(), vec![s.clone(), SExp::IntLit(*k)]));
                }
            }
            Pattern::InPlace(inner) => self.refine(inner, subject, subject_ty, env),
            // A constructor takes its value apart, and the pieces have
            // types: the tail of a list is a list of the same thing, of
            // a length the scrutinee was carrying.  Binding them as
            // unknowns is what leaves every recursion over an indexed
            // datatype unchecked.
            Pattern::Ctor(ctor, fields) => {
                let matched = self.ctors.match_pattern(
                    ctor,
                    fields.len(),
                    subject_ty,
                    &env.fresh_supply(),
                );
                if let Some(matched) = &matched {
                    for (name, sort) in &matched.variables {
                        env.declare(name, sort);
                    }
                    env.assume_all(matched.assumptions.clone());
                }
                for (i, field) in fields.iter().enumerate() {
                    let ty = matched
                        .as_ref()
                        .and_then(|matched| matched.fields.get(i))
                        .cloned();
                    self.refine(field, None, ty.as_ref(), env);
                }
            }
            Pattern::Tuple(items) => {
                let declared = subject_ty.and_then(|t| match strip_index(t) {
                    Ty::Tuple(parts) => Some(parts.clone()),
                    _ => None,
                });
                for (i, item) in items.iter().enumerate() {
                    let ty = declared.as_ref().and_then(|tys| tys.get(i)).cloned();
                    self.refine(item, None, ty.as_ref(), env);
                }
            }
            Pattern::Wildcard | Pattern::Bool(_) | Pattern::Char(_) | Pattern::Str(_) => {}
        }
    }

    /// A recursive call, against the metric its function was given.
    ///
    /// Two claims, and both are needed.  The metric must *decrease*, or
    /// the recursion may run forever; and it must be *bounded below*, or
    /// it can decrease forever, which is the same thing.  A function that
    /// promises `int(n)` and never returns has proved nothing, so
    /// termination is part of the type, not a separate virtue.
    ///
    /// Several components are lexicographic: the claim is that some
    /// component falls while every earlier one holds still.  That is a
    /// disjunction, which the solver decides by cases.
    fn check_metric(&mut self, at_call: &[SExp], env: &IndexEnv) {
        if self.metric.is_empty() || at_call.len() != self.metric.len() {
            return;
        }
        let origin = Origin::Metric {
            function: self.function.clone(),
        };
        let entry = self.metric.clone();
        for component in &entry {
            self.demand(
                SExp::App(">=".into(), vec![component.clone(), SExp::IntLit(0)]),
                origin.clone(),
                env,
            );
        }
        let lt = |a: &SExp, b: &SExp| SExp::App("<".into(), vec![a.clone(), b.clone()]);
        let eq = |a: &SExp, b: &SExp| SExp::App("==".into(), vec![a.clone(), b.clone()]);
        let mut alternatives: Vec<SExp> = Vec::new();
        for (i, (called, component)) in at_call.iter().zip(&entry).enumerate() {
            // This component falls, and every earlier one stands still.
            let mut claim = lt(called, component);
            for (earlier_call, earlier_entry) in at_call.iter().zip(&entry).take(i) {
                claim = SExp::App("&&".into(), vec![eq(earlier_call, earlier_entry), claim]);
            }
            alternatives.push(claim);
        }
        let Some(goal) = alternatives
            .into_iter()
            .reduce(|a, b| SExp::App("||".into(), vec![a, b]))
        else {
            return;
        };
        self.demand(goal, origin, env);
    }

    /// `xs[i]` — the obligation ATS exists to make.
    fn subscript(&mut self, subject: &Expr, at: &Expr, env: &mut IndexEnv) -> Option<SExp> {
        let size = match subject {
            Expr::Var(name) => env.size_of(name),
            _ => {
                self.expr(subject, env);
                None
            }
        };
        let index = self.expr(at, env)?;
        let (Some(size), Expr::Var(name)) = (size, subject) else {
            return None;
        };
        let origin = Origin::Bound {
            subject: name.clone(),
        };
        self.demand(
            SExp::App(">=".into(), vec![index.clone(), SExp::IntLit(0)]),
            origin.clone(),
            env,
        );
        self.demand(SExp::App("<".into(), vec![index, size]), origin, env);
        None
    }

    /// A branch: each arm reasons under its own guard, and neither can
    /// see what the other learned.
    fn conditional(&mut self, c: &Expr, t: &Expr, f: &Expr, env: &mut IndexEnv) -> Option<SExp> {
        let guard = self.expr(c, env);
        let mut taken = env.clone();
        let mut untaken = env.clone();
        if let Some(g) = &guard {
            taken.assume(g.clone());
            untaken.assume(negate(g));
        }
        let a = self.expr(t, &mut taken);
        let b = self.expr(f, &mut untaken);
        self.join(a, b, env)
    }

    /// What is known about a value that came from more than one path.
    ///
    /// Only what the paths agree on: anything else would be a claim one
    /// of them never made.  Disagreement is a fresh unknown, not a
    /// disjunction, because the solver holds conjunctions.
    fn join(&mut self, a: Option<SExp>, b: Option<SExp>, env: &mut IndexEnv) -> Option<SExp> {
        match (a, b) {
            (Some(a), Some(b)) if a == b => Some(a),
            _ => Some(env.fresh("join")),
        }
    }

    fn case(
        &mut self,
        scrutinee: &Expr,
        arms: &[(Pattern, Expr)],
        env: &mut IndexEnv,
    ) -> Option<SExp> {
        let subject = self.expr(scrutinee, env);
        let subject_ty = type_of_expr(scrutinee, env);
        let mut results: Vec<Option<SExp>> = Vec::new();
        for (pattern, body) in arms {
            let mut arm = env.clone();
            self.refine(pattern, subject.as_ref(), subject_ty.as_ref(), &mut arm);
            results.push(self.expr(body, &mut arm));
        }
        let mut produced = results.first().cloned().flatten();
        for r in results.iter().skip(1) {
            produced = self.join(produced, r.clone(), env);
        }
        produced
    }

    pub(crate) fn let_bind(&mut self, b: &LetBind, env: &mut IndexEnv) {
        // `val y = (e : t)` and `val y: t = e` are the same statement
        // written two ways, so they are read the same way.
        let (value, ascribed) = match &b.value {
            Expr::Ascribe(inner, ty) => (&**inner, Some(ty)),
            other => (other, None),
        };
        let annotation = b.ty.as_ref().or(ascribed);
        // An annotation says what the value's type *is*, whether or not
        // that type makes a claim about the value: `val xs: list(int, 5)`
        // is the only place a list built out of constructors says how
        // long it is.
        if let (Some(ty), Some(name)) = (annotation, &b.name) {
            env.bind_type(name, (*ty).clone());
        }
        let claim = annotation.and_then(claim_of);
        self.last_call = None;
        // An annotation reaches into the branches exactly as a result
        // type does: `val n = (if n >= 0 then n else 0): intGte(0)` is
        // how the corpus bounds an integer, and joining the arms first
        // makes it unprovable.
        let produced = match &claim {
            Some(claim) if is_branching(value) => {
                let name = b.name.clone().unwrap_or_default();
                let promise = Promise {
                    claim: claim.clone(),
                    proposition: None,
                    witnesses: Vec::new(),
                    hypotheses: Vec::new(),
                    origin: Origin::Annotation,
                };
                self.check_against(value, &promise, env);
                let me = env.fresh(&name);
                env.assume(about(claim, &me));
                Some(me)
            }
            _ => self.expr(value, env),
        };
        // `val [r1:int] (pf | x) = f(...)` — the callee refused to name
        // its witness, and this is the caller naming it.  Every fact the
        // call brought back is already stated about that fresh variable,
        // so the name is an alias for it and the body may reason with it.
        let reported = self.last_call.take();
        if let Some(facts) = &reported {
            for ((name, sort), witness) in b.opened.iter().zip(&facts.witnesses) {
                env.bind(name, witness.clone());
                env.assume_all(sort.refinement(name));
                // The name and the witness are the same number.
                env.assume(SExp::App(
                    "==".into(),
                    vec![SExp::Var(name.to_string()), witness.clone()],
                ));
            }
        }
        // A proof is indexed by every number its proposition is about,
        // and none of them is "the" value: `FACT(n, n*r)` proves a claim
        // about two, and keeping one would prove half of it.
        // A binding is the same value with a name on it, so it keeps
        // the type the call reported — unless the source wrote one
        // down, which is the more specific statement and the one the
        // reader is looking at.
        if let (None, Some(name), Some(facts)) = (annotation, &b.name, &reported) {
            if let Some(ty) = &facts.result_ty {
                env.bind_type(name, ty.clone());
            }
        }
        if let (Some(name), Some(facts)) = (&b.name, &reported) {
            if facts.result_indices.len() > 1 {
                env.bind_all(name, facts.result_indices.clone());
                return;
            }
        }
        match (&b.ty.as_ref().or(ascribed), &b.name) {
            // An annotation is a claim about the value, and the only
            // place a mistyped `val` can ever be caught.
            (Some(ty), name) if claim.is_some() => {
                let claim = claim.expect("checked");
                if let Some(actual) = &produced {
                    self.demand(about(&claim, actual), Origin::Annotation, env);
                }
                if let Some(name) = name {
                    env.bind_all(name, ty.indices().to_vec());
                    match &produced {
                        Some(actual) => env.bind(name, actual.clone()),
                        None => {
                            // The value is unknown, but the annotation
                            // still holds of it — which is the whole
                            // reason the annotation was written.
                            let me = env.fresh(name);
                            env.assume(about(&claim, &me));
                            env.bind(name, me);
                        }
                    }
                }
            }
            (_, Some(name)) => match produced {
                Some(idx) => env.bind(name, idx),
                None => env.forget(name),
            },
            _ => {}
        }
    }

    /// A loop runs an unknown number of times, so nothing known about a
    /// cell it writes survives it — not before the loop, not after.
    ///
    /// Dropping those facts is the difference between a checker that is
    /// merely weak about loops and one that is wrong about them.
    fn loop_over(&mut self, parts: &[&Expr], env: &mut IndexEnv) -> Option<SExp> {
        let mut written = Vec::new();
        for part in parts {
            collect_assigned(part, &mut written);
        }
        env.forget_all(written);
        let mut inner = env.clone();
        for part in parts {
            self.expr(part, &mut inner);
        }
        None
    }
}

/// The name a call is calling, and the static terms it was written with.
///
/// Two spellings reach here.  `ax{n, 0}()` could only ever be static, so
/// the parser kept it as such.  `ax{n}()` is indistinguishable from a
/// template instantiation — `{int}` and `{n}` are the same shape — so the
/// parser called it types, and it is re-read here, where the callee's
/// quantifiers are finally in view.  Only a bare name can be an index; a
/// `list(a)` in that position was a type argument and stays one.
fn called_name(callee: &Expr) -> Option<(String, Vec<SExp>, Vec<Ty>)> {
    match callee {
        Expr::Var(name) => Some((name.clone(), Vec::new(), Vec::new())),
        Expr::Inst(name, tys) => {
            let at = tys
                .iter()
                .map(|t| match t {
                    Ty::Name(n) => SExp::Var(n.clone()),
                    // Not a name, so not an index.  A place-holder keeps
                    // the *positions* right, and an unspellable name
                    // cannot be mistaken for a term anyone meant.
                    _ => SExp::Var(format!("%ty{t:?}")),
                })
                .collect();
            Some((name.clone(), at, tys.clone()))
        }
        Expr::StaticInst(inner, at) => {
            let (name, _, tys) = called_name(inner)?;
            Some((name, at.clone(), tys))
        }
        _ => None,
    }
}

/// What a result type promises the caller, in one piece.
///
/// It grew to five things, which is four more than a parameter list
/// wants: the claim about the value, the proposition carried beside it,
/// the witnesses the body must supply, what the caller may then assume,
/// and where the demand came from.  They travel together because they
/// are read together, and because a branch must hand all five to each of
/// its arms unchanged.
#[derive(Debug, Clone)]
struct Promise {
    /// What must hold of the value, in terms of [`SELF`].
    claim: SExp,
    /// The indices of the proposition the value carries a proof of, when
    /// it carries one.
    proposition: Option<Vec<SExp>>,
    /// The existential variables the body is to witness.
    witnesses: Vec<String>,
    /// What the caller may assume once the body has witnessed them.
    hypotheses: Vec<SExp>,
    origin: Origin,
}

/// The index terms a proposition is applied to.
///
/// A proposition reaches here spelled two ways.  A `dataprop`
/// constructor's result is built from index terms directly —
/// `FACT(n, n*r)` — while a proposition written in a signature parses as
/// an ordinary type application, `FACT(n, r)`, whose arguments are plain
/// names.  Both are the same claim, so both are read the same way.
fn proposition_indices(ty: &Ty) -> Option<Vec<SExp>> {
    match ty {
        Ty::Index(_, idx) => Some(idx.clone()),
        Ty::App(_, args) => args
            .iter()
            .map(|a| match a {
                Ty::Name(n) => Some(SExp::Var(n.clone())),
                _ => None,
            })
            .collect(),
        _ => None,
    }
}

/// Whether a name is one of ATS's unchecked casts.
///
/// `$UN.cast`, `$UNSAFE.castvwtp0` and their kin reach the checker under
/// their bare names, the module prefix having been read off already.
fn is_unsafe_cast(name: &str) -> bool {
    matches!(
        name,
        "cast" | "cast0" | "cast1" | "castvwtp0" | "castvwtp1" | "ptrcast" | "castto"
    )
}

/// Whether a name is one of ATS's assertion forms.
///
/// They are the bridge from the dynamic language to the static one: the
/// program checks at run time what the checker could not establish, and
/// everything after the check may rely on it.
fn is_assertion(name: &str) -> bool {
    matches!(
        name,
        "assertexn" | "assertloc" | "assert" | "assert_errmsg" | "assert_bool"
    )
}

/// The number a `#define` names, when it names one.
///
/// A constant may be any expression at all — `#define GREETING "hi"` —
/// and only the numeric ones are the checker's business.
fn index_of_literal(e: &Expr) -> Option<SExp> {
    match e {
        Expr::IntLit(n) => Some(SExp::IntLit(*n)),
        Expr::UnaryNeg(inner) => Some(SExp::App("~".into(), vec![index_of_literal(inner)?])),
        _ => None,
    }
}

/// A claim, said of one particular value.
fn about(claim: &SExp, value: &SExp) -> SExp {
    claim.substitute(&[(SELF.to_string(), value.clone())])
}

/// Whether an expression's value comes from more than one path, and so
/// has no single index worth comparing an annotation against.
fn is_branching(e: &Expr) -> bool {
    matches!(e, Expr::IfThenElse(..) | Expr::Case(..))
}

/// The existential variables a result type leaves for the body to
/// witness.  Type-sorted ones bind types, not numbers, and take no part.
fn witnesses_of(existentials: &[Quant]) -> Vec<String> {
    existentials
        .iter()
        .flat_map(|q| &q.vars)
        .filter(|(_, s)| s.is_arithmetic())
        .map(|(n, _)| n.clone())
        .collect()
}

/// The type an expression was declared with, when a name carries one.
fn type_of_expr(e: &Expr, env: &IndexEnv) -> Option<Ty> {
    match e {
        Expr::Var(name) => env.type_of(name),
        // `!p` reads through a pointer, and what is behind it is as long
        // as it ever was: a pointer to an array is not shorter than the
        // array.
        Expr::Deref(inner) | Expr::Ascribe(inner, _) => type_of_expr(inner, env),
        Expr::ProofPair(_, value) => type_of_expr(value, env),
        _ => None,
    }
}

/// Every cell an expression assigns to.
fn collect_assigned(e: &Expr, out: &mut Vec<String>) {
    if let Expr::Assign(name, _) = e {
        if !out.contains(name) {
            out.push(name.clone());
        }
    }
    e.each_subexpr(&mut |sub| collect_assigned(sub, out));
}

