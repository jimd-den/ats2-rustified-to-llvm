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
        ctors: &ctors,
        consts,
        out: Vec::new(),
        function: String::new(),
        metric: Vec::new(),
        last_call: None,
    };
    for def in program.defs() {
        match def {
            Def::Fun(f) => walk.function_def(f, IndexEnv::new()),
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
                    IndexEnv::new(),
                    // An `implement` fills in a function, never a proof.
                    false,
                );
            }
            Def::Val(val) => {
                let mut env = IndexEnv::new();
                walk.function = val.name.clone();
                let _ = walk.expr(&val.value, &mut env);
            }
            _ => {}
        }
    }
    walk.out
}

struct Walk<'a> {
    sigs: &'a SigTable,
    /// What each constructor takes apart into.
    ctors: &'a CtorTable,
    /// The `#define`d constants, by name.
    consts: HashMap<String, SExp>,
    out: Vec<Obligation>,
    /// Whose body is being walked — the half of a diagnostic no solver
    /// could reconstruct.
    function: String,
    /// That function's `.<n>.` metric, read at its entry.  A recursive
    /// call must be shown to have come down from this.
    metric: Vec<SExp>,
    /// What the most recent call reported.
    ///
    /// A binding needs more than the single index a value has: a *proof*
    /// carries one index per number its proposition is about, and an
    /// *opening* names the witness the call invented.  Both are on the
    /// call's own report, and the binding is the next thing to run.
    last_call: Option<CallFacts>,
}

impl<'a> Walk<'a> {
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
                for f in funs {
                    self.function_def(f, env.clone());
                }
                self.check_against(rest, promise, env);
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
            Expr::Call(callee, args) => self.call(callee, args, env),
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
                for f in funs {
                    self.function_def(f, env.clone());
                }
                self.expr(rest, env)
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
    fn call(&mut self, callee: &Expr, args: &[Expr], env: &mut IndexEnv) -> Option<SExp> {
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
        let declared: &Signature = self.sigs.get(&name)?;
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
        let facts = sig.at_call(&statics, &supplied, &env.fresh_supply());
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
                let declared = self.ctors.fields_of(ctor, fields.len(), subject_ty);
                for (i, field) in fields.iter().enumerate() {
                    let ty = declared.as_ref().and_then(|tys| tys.get(i)).cloned();
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

    fn let_bind(&mut self, b: &LetBind, env: &mut IndexEnv) {
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
                    vec![SExp::Var(name.clone()), witness.clone()],
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

#[cfg(test)]
mod tests {
    use super::*;
    use ats2_domain::ast::{
        BinOp, Ctor, DatatypeDef, Def, FunDef, ImplementDef, LetBind, Param, Pattern, Program,
    };
    use ats2_domain::obligation::Obligation;
    use ats2_domain::statics::{Quant, Sort};

    fn v(n: &str) -> SExp {
        SExp::Var(n.into())
    }
    fn i(n: i64) -> SExp {
        SExp::IntLit(n)
    }
    fn app(op: &str, a: SExp, b: SExp) -> SExp {
        SExp::App(op.into(), vec![a, b])
    }
    fn int_of(idx: SExp) -> Ty {
        Ty::Index(Box::new(Ty::Name("int".into())), vec![idx])
    }
    fn var(n: &str) -> Expr {
        Expr::Var(n.into())
    }
    fn call(f: &str, args: Vec<Expr>) -> Expr {
        Expr::Call(Box::new(var(f)), args)
    }
    fn nat() -> Quant {
        Quant {
            vars: vec![("n".into(), Sort::Nat)],
            guard: None,
        }
    }

    /// `fun f {n:nat} (x: int n): <ret> = <body>`
    fn fun(name: &str, quants: Vec<Quant>, params: Vec<Param>, ret: Ty, body: Expr) -> Def {
        Def::Fun(FunDef {
            metric: vec![],
            ty_params: vec![],
            universals: quants,
            existentials: vec![],
            name: name.into(),
            params,
            ret,
            body,
            proof: false,
        })
    }

    fn p(name: &str, ty: Ty) -> Param {
        Param {
            name: name.into(),
            ty,
            borrowed: false,
        }
    }

    /// A `nat`-demanding function, and a `main0` whose body is `body`.
    fn with_main(body: Expr) -> Program {
        Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            Def::Implement(ImplementDef {
                ty_params: vec![],
                instance: vec![],
                name: "main0".into(),
                params: vec![],
                ret: None,
                body,
            }),
        ])
    }

    fn goals(program: &Program) -> Vec<String> {
        obligations(program, &Program::new(vec![]))
            .iter()
            .map(|o| o.goal.to_string())
            .collect()
    }

    /// The hypotheses in force at the first obligation mentioning `needle`.
    fn hyps_at(program: &Program, needle: &str) -> Vec<String> {
        obligations(program, &Program::new(vec![]))
            .iter()
            .find(|o| o.goal.to_string().contains(needle))
            .map(|o| o.hyps.iter().map(|h| h.to_string()).collect())
            .unwrap_or_else(|| panic!("no obligation mentioning {needle} in {:?}", goals(program)))
    }

    #[test]
    fn a_call_in_main_owes_the_callees_demand() {
        let program = with_main(call(
            "needs_nat",
            vec![Expr::UnaryNeg(Box::new(Expr::IntLit(1)))],
        ));
        assert!(
            goals(&program).contains(&"~1 >= 0".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_body_may_assume_what_its_own_signature_demanded() {
        // This is what makes dependent types compose: `f`'s promise that
        // `n` is a nat is exactly what lets `f` call `g` with it.
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![nat()],
                vec![p("y", int_of(v("n")))],
                Ty::Name("int".into()),
                call("needs_nat", vec![var("y")]),
            ),
        ]);
        assert!(hyps_at(&program, "n >= 0").contains(&"n >= 0".to_string()));
    }

    #[test]
    fn the_then_branch_assumes_the_condition_and_the_else_branch_denies_it() {
        // `if x > 0 then f(x-1)` is the shape every recursive function
        // over `nat` takes, and it is unprovable without the guard.
        let cond = Expr::BinOp(BinOp::Gt, Box::new(var("x")), Box::new(Expr::IntLit(0)));
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![],
                vec![p("x", int_of(v("k")))],
                Ty::Name("int".into()),
                Expr::IfThenElse(
                    Box::new(cond),
                    Box::new(call(
                        "needs_nat",
                        vec![Expr::BinOp(
                            BinOp::Sub,
                            Box::new(var("x")),
                            Box::new(Expr::IntLit(1)),
                        )],
                    )),
                    Box::new(call("needs_nat", vec![var("x")])),
                ),
            ),
        ]);
        assert!(hyps_at(&program, "k - 1 >= 0").contains(&"k > 0".to_string()));
        assert!(hyps_at(&program, "k >= 0").contains(&"k <= 0".to_string()));
    }

    #[test]
    fn a_let_binding_names_the_index_of_what_it_bound() {
        let program = with_main(Expr::Let(
            vec![LetBind {
                opened: Vec::new(),
                proof: false,
                name: Some("y".into()),
                ty: None,
                value: Expr::IntLit(7),
                mutable: false,
            }],
            Box::new(call("needs_nat", vec![var("y")])),
        ));
        assert!(
            goals(&program).contains(&"7 >= 0".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn an_annotated_binding_is_checked_against_its_annotation() {
        // `val x: int(3) = 4` is a lie, and the annotation is the only
        // place that can catch it.
        let program = with_main(Expr::Let(
            vec![LetBind {
                opened: Vec::new(),
                proof: false,
                name: Some("y".into()),
                ty: Some(int_of(i(3))),
                value: Expr::IntLit(4),
                mutable: false,
            }],
            Box::new(Expr::Unit),
        ));
        assert!(
            goals(&program).contains(&"4 == 3".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_result_type_is_a_claim_the_body_must_make_good() {
        // The half of the checker the README said was missing: a
        // signature that promises `int(n+1)` and returns `x` is wrong,
        // and nothing about the call sites will ever say so.
        let program = Program::new(vec![fun(
            "succ",
            vec![nat()],
            vec![p("x", int_of(v("n")))],
            int_of(app("+", v("n"), i(1))),
            var("x"),
        )]);
        assert!(
            goals(&program).contains(&"n == n + 1".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_result_type_the_body_honours_is_owed_but_provable() {
        let program = Program::new(vec![fun(
            "succ",
            vec![nat()],
            vec![p("x", int_of(v("n")))],
            int_of(app("+", v("n"), i(1))),
            Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(Expr::IntLit(1))),
        )]);
        assert!(
            goals(&program).contains(&"n + 1 == n + 1".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn writing_to_a_cell_stops_the_checker_believing_what_it_held_before() {
        // `var x = 3; x := ~1; needs_nat(x)` must not be proved by the 3.
        let program = with_main(Expr::Let(
            vec![LetBind {
                opened: Vec::new(),
                proof: false,
                name: Some("x".into()),
                ty: None,
                value: Expr::IntLit(3),
                mutable: true,
            }],
            Box::new(Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: None,
                    ty: None,
                    value: Expr::Assign(
                        "x".into(),
                        Box::new(Expr::UnaryNeg(Box::new(Expr::IntLit(1)))),
                    ),
                    mutable: false,
                }],
                Box::new(call("needs_nat", vec![var("x")])),
            )),
        ));
        assert!(
            !goals(&program).contains(&"3 >= 0".to_string()),
            "stale: {:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_loop_forgets_the_cells_its_body_writes() {
        // Facts established before a loop do not survive it, because the
        // body runs an unknown number of times.
        let body = Expr::Assign(
            "x".into(),
            Box::new(Expr::UnaryNeg(Box::new(Expr::IntLit(1)))),
        );
        let program = with_main(Expr::Let(
            vec![LetBind {
                opened: Vec::new(),
                proof: false,
                name: Some("x".into()),
                ty: None,
                value: Expr::IntLit(3),
                mutable: true,
            }],
            Box::new(Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: None,
                    ty: None,
                    value: Expr::While(Box::new(Expr::BoolLit(true)), Box::new(body)),
                    mutable: false,
                }],
                Box::new(call("needs_nat", vec![var("x")])),
            )),
        ));
        assert!(
            !goals(&program).contains(&"3 >= 0".to_string()),
            "stale after loop: {:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_literal_pattern_tells_its_arm_what_the_scrutinee_was() {
        // `case x of | 0 => f(x)` knows `x` is zero inside the arm.
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![],
                vec![p("x", int_of(v("k")))],
                Ty::Name("int".into()),
                Expr::Case(
                    Box::new(var("x")),
                    vec![(Pattern::Int(0), call("needs_nat", vec![var("x")]))],
                ),
            ),
        ]);
        assert!(hyps_at(&program, "k >= 0").contains(&"k == 0".to_string()));
    }

    #[test]
    fn a_variable_pattern_binds_the_scrutinees_index_to_the_name() {
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![],
                vec![p("x", int_of(v("k")))],
                Ty::Name("int".into()),
                Expr::Case(
                    Box::new(var("x")),
                    vec![(Pattern::Var("y".into()), call("needs_nat", vec![var("y")]))],
                ),
            ),
        ]);
        assert!(
            goals(&program).contains(&"k >= 0".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_subscript_owes_both_ends_of_the_array_it_reaches_into() {
        // `xs[i]` on an `array(int, n)` is only safe for `0 <= i < n`,
        // and this is the obligation ATS exists to make.
        let arr = Ty::Index(
            Box::new(Ty::App("array".into(), vec![Ty::Name("int".into())])),
            vec![v("n")],
        );
        let program = Program::new(vec![fun(
            "get",
            vec![],
            vec![p("xs", arr), p("i", int_of(v("k")))],
            Ty::Name("int".into()),
            Expr::Index(Box::new(var("xs")), Box::new(var("i"))),
        )]);
        let g = goals(&program);
        assert!(g.contains(&"k >= 0".to_string()), "{g:?}");
        assert!(g.contains(&"k < n".to_string()), "{g:?}");
    }

    #[test]
    fn a_nested_function_is_checked_under_its_own_quantifiers() {
        // A `let fun` has a signature and a body like any other, and
        // skipping it would leave most real ATS unchecked.
        let inner = FunDef {
            ty_params: vec![],
            universals: vec![nat()],
            existentials: vec![],
            metric: vec![],
            name: "loop".into(),
            params: vec![p("x", int_of(v("n")))],
            ret: int_of(app("+", v("n"), i(1))),
            body: var("x"),
            proof: false,
        };
        let program = with_main(Expr::LetFun(vec![inner], Box::new(Expr::Unit)));
        assert!(
            goals(&program).contains(&"n == n + 1".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_call_may_assume_what_an_existential_result_promised() {
        // `g(): [r:nat] int r` followed by `needs_nat(g())` is provable
        // only if the existential's guard came back with the value.
        let g = Def::Fun(FunDef {
            metric: vec![],
            ty_params: vec![],
            universals: vec![],
            existentials: vec![Quant {
                vars: vec![("r".into(), Sort::Nat)],
                guard: None,
            }],
            name: "g".into(),
            params: vec![],
            ret: int_of(v("r")),
            body: Expr::IntLit(0),
            proof: false,
        });
        let mut defs = vec![g];
        defs.extend(
            with_main(call("needs_nat", vec![call("g", vec![])]))
                .defs()
                .to_vec(),
        );
        let program = Program::new(defs);
        let o = obligations(&program, &Program::new(vec![]));
        let call_ob = o
            .iter()
            .find(|o| matches!(o.origin, Origin::Call { ref callee } if callee == "needs_nat"))
            .expect("the call");
        assert!(
            call_ob.hyps.iter().any(|h| h.to_string().starts_with("r%")),
            "the witness's nat-ness must be in scope: {:?}",
            call_ob.hyps
        );
    }

    #[test]
    fn a_datatype_declaration_does_not_derail_the_walk() {
        let program = Program::new(vec![Def::Datatype(DatatypeDef {
            linear: false,
            name: "opt".into(),
            ty_params: vec!["a".into()],
            ctors: vec![Ctor {
                name: "none".into(),
                fields: vec![],
            }],
        })]);
        assert!(obligations(&program, &Program::new(vec![])).is_empty());
    }

    #[test]
    fn a_promised_result_is_pushed_into_each_branch_rather_than_joined() {
        // `if c then a else b` checked as a *whole* loses everything:
        // the two arms disagree, so the join is an unknown and the
        // promise becomes unprovable.  Checked branch by branch, each arm
        // answers for itself under its own guard — which is the whole
        // difference between a checker that reads `if` and one that only
        // walks past it.
        let x = var("x");
        let plus1 = Expr::BinOp(BinOp::Add, Box::new(x.clone()), Box::new(Expr::IntLit(1)));
        let program = Program::new(vec![fun(
            "succ",
            vec![nat()],
            vec![p("x", int_of(v("n")))],
            int_of(app("+", v("n"), i(1))),
            Expr::IfThenElse(
                Box::new(Expr::BinOp(
                    BinOp::Gt,
                    Box::new(x),
                    Box::new(Expr::IntLit(0)),
                )),
                Box::new(plus1.clone()),
                Box::new(plus1),
            ),
        )]);
        let g = goals(&program);
        assert!(
            !g.iter().any(|goal| goal.contains("join%")),
            "the arms were joined: {g:?}"
        );
        assert_eq!(g, vec!["n + 1 == n + 1".to_string(); 2], "{g:?}");
    }

    #[test]
    fn a_promised_result_is_pushed_through_a_let_to_the_value_it_ends_with() {
        // A body is usually `let ... in <the answer> end`, and a checker
        // that stopped at the `let` would check almost nothing.
        let program = Program::new(vec![fun(
            "succ",
            vec![nat()],
            vec![p("x", int_of(v("n")))],
            int_of(app("+", v("n"), i(1))),
            Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: Some("y".into()),
                    ty: None,
                    value: Expr::IntLit(1),
                    mutable: false,
                }],
                Box::new(Expr::BinOp(
                    BinOp::Add,
                    Box::new(var("x")),
                    Box::new(var("y")),
                )),
            ),
        )]);
        assert!(
            goals(&program).contains(&"n + 1 == n + 1".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn each_arm_of_a_case_answers_for_the_promise_on_its_own() {
        let program = Program::new(vec![fun(
            "id",
            vec![nat()],
            vec![p("x", int_of(v("n")))],
            int_of(v("n")),
            Expr::Case(
                Box::new(var("x")),
                vec![
                    (Pattern::Int(0), Expr::IntLit(0)),
                    (Pattern::Var("y".into()), var("y")),
                ],
            ),
        )]);
        let g = goals(&program);
        assert!(g.contains(&"0 == n".to_string()), "{g:?}");
        assert!(g.contains(&"n == n".to_string()), "{g:?}");
    }

    #[test]
    fn main0_knows_that_argv_is_as_long_as_argc_says() {
        // ATS gives the entry point `main0 {n:nat} (argc: int n, argv:
        // !argv(n))`: the count and the array are indexed by the *same*
        // variable.  Without that, `if argc >= 2 then argv[1]` — which is
        // how a third of the corpus reads its arguments — is unprovable,
        // and the checker's first impression of real code is a false
        // alarm on every one of them.
        let guard = Expr::BinOp(BinOp::Ge, Box::new(var("argc")), Box::new(Expr::IntLit(2)));
        let read = Expr::Index(Box::new(var("argv")), Box::new(Expr::IntLit(1)));
        let program = Program::new(vec![Def::Implement(ImplementDef {
            ty_params: vec![],
            instance: vec![],
            name: "main0".into(),
            params: vec![
                p("argc", Ty::Name("int".into())),
                p("argv", Ty::Name("argv".into())),
            ],
            ret: None,
            body: Expr::IfThenElse(Box::new(guard), Box::new(read), Box::new(Expr::Unit)),
        })]);
        let obs = obligations(&program, &Program::new(vec![]));
        let upper = obs
            .iter()
            .find(|o| o.goal.to_string().starts_with("1 <"))
            .unwrap_or_else(|| panic!("no upper-bound check in {:?}", goals(&program)));
        assert_eq!(
            crate::constraints::entails(&upper.hyps, &upper.goal),
            crate::constraints::Verdict::Proved,
            "goal {} from {:?}",
            upper.goal,
            upper.hyps
        );
    }

    #[test]
    fn argv_zero_is_always_there_because_argc_is_never_zero() {
        // `argv[0]` is the program's own name, so `main0`'s count is a
        // `pos`, not merely a `nat`.  Without that, the else-branch of
        // every `if argc >= 2` — the one that falls back on defaults —
        // cannot reach `argv[0]`, which is where the corpus keeps the
        // program name.
        let guard = Expr::BinOp(BinOp::Ge, Box::new(var("argc")), Box::new(Expr::IntLit(2)));
        let read = Expr::Index(Box::new(var("argv")), Box::new(Expr::IntLit(0)));
        let program = Program::new(vec![Def::Implement(ImplementDef {
            ty_params: vec![],
            instance: vec![],
            name: "main0".into(),
            params: vec![
                p("argc", Ty::Name("int".into())),
                p("argv", Ty::Name("argv".into())),
            ],
            ret: None,
            body: Expr::IfThenElse(Box::new(guard), Box::new(Expr::Unit), Box::new(read)),
        })]);
        let obs = obligations(&program, &Program::new(vec![]));
        let upper = obs
            .iter()
            .find(|o| o.goal.to_string().starts_with("0 <"))
            .expect("an upper bound");
        assert_eq!(
            crate::constraints::entails(&upper.hyps, &upper.goal),
            crate::constraints::Verdict::Proved,
            "goal {} from {:?}",
            upper.goal,
            upper.hyps
        );
    }

    #[test]
    fn an_implementation_is_checked_against_the_signature_it_was_declared_with() {
        // `extern fun f {n:nat} (x: int n): int` followed by
        // `implement f (x) = ...` writes the quantifier once.  A checker
        // that read only the `implement` would see an unindexed
        // parameter and could prove nothing about the body at all.
        let program = Program::new(vec![
            Def::Extern(ats2_domain::ast::FunDecl {
                linear: false,
                proof: false,
                name: "f".into(),
                ty_params: vec![],
                universals: vec![nat()],
                existentials: vec![],
                params: vec![p("x", int_of(v("n")))],
                ret: int_of(app("+", v("n"), i(1))),
            }),
            Def::Implement(ImplementDef {
                ty_params: vec![],
                instance: vec![],
                name: "f".into(),
                params: vec![p("x", Ty::Name("int".into()))],
                ret: None,
                body: var("x"),
            }),
        ]);
        // The declared result is `int(n+1)` and the body returns `x`,
        // which is `n`: the promise is broken, and only the declaration
        // could have said so.
        assert!(
            goals(&program).contains(&"n == n + 1".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn an_implementation_that_annotates_its_own_parameters_keeps_them() {
        // Where the `implement` says what it means, it wins: the
        // declaration fills gaps, it does not overrule.
        let program = Program::new(vec![
            Def::Extern(ats2_domain::ast::FunDecl {
                linear: false,
                proof: false,
                name: "f".into(),
                ty_params: vec![],
                universals: vec![nat()],
                existentials: vec![],
                params: vec![p("x", int_of(v("n")))],
                ret: Ty::Name("int".into()),
            }),
            Def::Implement(ImplementDef {
                ty_params: vec![],
                instance: vec![],
                name: "f".into(),
                params: vec![p("x", int_of(i(7)))],
                ret: Some(int_of(i(7))),
                body: var("x"),
            }),
        ]);
        assert!(
            goals(&program).contains(&"7 == 7".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_function_that_merely_happens_to_be_called_argc_gets_no_such_gift() {
        // The convention belongs to the entry point, not to the names.
        // Granting it anywhere else would be inventing a fact.
        let read = Expr::Index(Box::new(var("argv")), Box::new(Expr::IntLit(1)));
        let program = Program::new(vec![fun(
            "not_main",
            vec![],
            vec![
                p("argc", Ty::Name("int".into())),
                p("argv", Ty::Name("argv".into())),
            ],
            Ty::Name("void".into()),
            read,
        )]);
        assert!(
            !goals(&program).iter().any(|g| g.starts_with("1 <")),
            "an unindexed array has no size to check against: {:?}",
            goals(&program)
        );
    }

    /// `fun f {n:nat} .<metric>. (x: int n): int = <body>`
    fn recursive(metric: Vec<SExp>, body: Expr) -> Program {
        Program::new(vec![Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![nat()],
            existentials: vec![],
            metric,
            name: "f".into(),
            params: vec![p("x", int_of(v("n")))],
            ret: Ty::Name("int".into()),
            body,
            proof: false,
        })])
    }

    /// `f(x - 1)`
    fn call_smaller() -> Expr {
        call(
            "f",
            vec![Expr::BinOp(
                BinOp::Sub,
                Box::new(var("x")),
                Box::new(Expr::IntLit(1)),
            )],
        )
    }

    #[test]
    fn a_recursive_call_must_decrease_the_metric_it_was_given() {
        // Without this a function may promise anything at all and keep
        // the promise by never returning, which is not a proof of
        // anything.  The claim is `n - 1 < n`, and it is the program's to
        // make, not the compiler's to assume.
        let program = recursive(vec![v("n")], call_smaller());
        let metric: Vec<&Obligation> = obligations(&program, &Program::new(vec![]))
            .iter()
            .filter(|o| matches!(o.origin, Origin::Metric { .. }))
            .cloned()
            .collect::<Vec<_>>()
            .leak()
            .iter()
            .collect();
        assert!(
            !metric.is_empty(),
            "no metric was checked: {:?}",
            goals(&program)
        );
        for o in metric {
            assert_eq!(
                crate::constraints::entails(&o.hyps, &o.goal),
                crate::constraints::Verdict::Proved,
                "goal {} from {:?}",
                o.goal,
                o.hyps
            );
        }
    }

    #[test]
    fn a_recursive_call_that_grows_the_metric_is_caught() {
        let grows = call(
            "f",
            vec![Expr::BinOp(
                BinOp::Add,
                Box::new(var("x")),
                Box::new(Expr::IntLit(1)),
            )],
        );
        let program = recursive(vec![v("n")], grows);
        let bad = obligations(&program, &Program::new(vec![]))
            .into_iter()
            .find(|o| matches!(o.origin, Origin::Metric { .. }) && o.goal.to_string().contains('<'))
            .expect("a decrease obligation");
        assert_eq!(
            crate::constraints::entails(&bad.hyps, &bad.goal),
            crate::constraints::Verdict::Refuted
        );
    }

    #[test]
    fn a_function_given_no_metric_is_asked_for_no_proof_of_termination() {
        // `.<>.` and a bare `fun` both claim nothing, and a checker that
        // invented the claim would reject every loop written without one.
        let program = recursive(vec![], call_smaller());
        assert!(
            !obligations(&program, &Program::new(vec![]))
                .iter()
                .any(|o| matches!(o.origin, Origin::Metric { .. }))
        );
    }

    #[test]
    fn a_call_to_someone_else_is_not_a_recursion_and_owes_no_decrease() {
        let program = with_main(call("needs_nat", vec![Expr::IntLit(1)]));
        assert!(
            !obligations(&program, &Program::new(vec![]))
                .iter()
                .any(|o| matches!(o.origin, Origin::Metric { .. }))
        );
    }

    #[test]
    fn the_metric_must_be_well_founded_as_well_as_decreasing() {
        // A metric that decreases forever proves nothing: `n` must also
        // be bounded below, or `n-1 < n` is satisfied by descending into
        // the negatives without end.
        let program = recursive(vec![v("n")], call_smaller());
        let goals: Vec<String> = obligations(&program, &Program::new(vec![]))
            .iter()
            .filter(|o| matches!(o.origin, Origin::Metric { .. }))
            .map(|o| o.goal.to_string())
            .collect();
        assert!(
            goals.iter().any(|g| g.contains(">= 0")),
            "no well-foundedness: {goals:?}"
        );
    }

    #[test]
    fn a_lexicographic_metric_decreases_when_a_later_component_does() {
        // `.<m, n>.` allows `m` to stay put as long as `n` falls.  That
        // is a disjunction, and refusing it would reject every nested
        // recursion in the language.
        let program = Program::new(vec![Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("m".into(), Sort::Nat), ("n".into(), Sort::Nat)],
                guard: None,
            }],
            existentials: vec![],
            metric: vec![v("m"), v("n")],
            name: "f".into(),
            params: vec![p("a", int_of(v("m"))), p("b", int_of(v("n")))],
            ret: Ty::Name("int".into()),
            body: call(
                "f",
                vec![
                    var("a"),
                    Expr::BinOp(BinOp::Sub, Box::new(var("b")), Box::new(Expr::IntLit(1))),
                ],
            ),
            proof: false,
        })]);
        for o in obligations(&program, &Program::new(vec![]))
            .iter()
            .filter(|o| matches!(o.origin, Origin::Metric { .. }))
        {
            assert_eq!(
                crate::constraints::entails(&o.hyps, &o.goal),
                crate::constraints::Verdict::Proved,
                "goal {} from {:?}",
                o.goal,
                o.hyps
            );
        }
    }

    #[test]
    fn a_templates_type_argument_is_never_read_as_an_index() {
        // `f<int>(3)` names which *code* to build.  Reading `int` as an
        // index and handing it to a `{n:nat}` would fix `n` to a type
        // name and prove whatever followed from nonsense.
        let program = Program::new(vec![
            Def::Fun(FunDef {
                ty_params: vec!["a".into()],
                universals: vec![nat()],
                existentials: vec![],
                metric: vec![],
                name: "g".into(),
                params: vec![p("x", int_of(v("n")))],
                ret: Ty::Name("int".into()),
                body: Expr::IntLit(0),
                proof: false,
            }),
            Def::Implement(ImplementDef {
                ty_params: vec![],
                instance: vec![],
                name: "main0".into(),
                params: vec![],
                ret: None,
                body: Expr::Call(
                    Box::new(Expr::Inst("g".into(), vec![Ty::Name("int".into())])),
                    vec![Expr::IntLit(3)],
                ),
            }),
        ]);
        // `n` comes from the argument, not from the type argument.
        assert!(
            goals(&program).contains(&"3 >= 0".to_string()),
            "{:?}",
            goals(&program)
        );
    }

    #[test]
    fn a_refinement_result_is_a_bound_the_body_must_meet_not_a_value() {
        // `fun f (): intGte(0) = 7` is correct: seven is at least
        // nought.  Reading the index as the value would demand `7 == 0`
        // and reject every program written with a bounded type.
        let ret = Ty::Index(Box::new(Ty::Name("intGte".into())), vec![i(0)]);
        let program = Program::new(vec![fun("f", vec![], vec![], ret, Expr::IntLit(7))]);
        assert_eq!(goals(&program), vec!["7 >= 0".to_string()]);
    }

    #[test]
    fn a_refinement_parameter_is_a_fact_the_body_may_use() {
        // `(i: natLt(n))` is what makes `xs[i]` safe, and it says so
        // twice: not below nought, and below `n`.
        let arr = Ty::Index(
            Box::new(Ty::App("array".into(), vec![Ty::Name("int".into())])),
            vec![v("n")],
        );
        let idx = Ty::Index(Box::new(Ty::Name("natLt".into())), vec![v("n")]);
        let program = Program::new(vec![fun(
            "get",
            vec![],
            vec![p("xs", arr), p("i", idx)],
            Ty::Name("int".into()),
            Expr::Index(Box::new(var("xs")), Box::new(var("i"))),
        )]);
        for o in obligations(&program, &Program::new(vec![]))
            .iter()
            .filter(|o| matches!(o.origin, Origin::Bound { .. }))
        {
            assert_eq!(
                crate::constraints::entails(&o.hyps, &o.goal),
                crate::constraints::Verdict::Proved,
                "goal {} from {:?}",
                o.goal,
                o.hyps
            );
        }
    }

    #[test]
    fn an_annotated_binding_is_checked_branch_by_branch() {
        // `val n = (if n >= 0 then n else 0): intGte(0)` is how the
        // corpus turns an unbounded integer into a bounded one.  Joining
        // the arms first makes it unprovable, so the annotation has to
        // reach into them exactly as a result type does.
        let x = var("x");
        let annotated = Expr::IfThenElse(
            Box::new(Expr::BinOp(
                BinOp::Ge,
                Box::new(x.clone()),
                Box::new(Expr::IntLit(0)),
            )),
            Box::new(x),
            Box::new(Expr::IntLit(0)),
        );
        let program = Program::new(vec![fun(
            "clamp",
            vec![],
            vec![p("x", int_of(v("k")))],
            Ty::Name("int".into()),
            Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: Some("y".into()),
                    ty: Some(Ty::Index(Box::new(Ty::Name("intGte".into())), vec![i(0)])),
                    value: annotated,
                    mutable: false,
                }],
                Box::new(Expr::Unit),
            ),
        )]);
        for o in obligations(&program, &Program::new(vec![])) {
            assert_eq!(
                crate::constraints::entails(&o.hyps, &o.goal),
                crate::constraints::Verdict::Proved,
                "goal {} from {:?}",
                o.goal,
                o.hyps
            );
        }
    }

    #[test]
    fn opening_an_existential_names_the_witness_the_callee_would_not() {
        // `val [r1:nat] (pf | y) = g()` says: whatever `g` produced,
        // call its witness `r1`.  From then on `r1` is a variable the
        // caller can reason about — and `needs_nat(y)` goes through
        // because `r1` is known to be a nat.
        let g = Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![],
            existentials: vec![Quant {
                vars: vec![("r".into(), Sort::Nat)],
                guard: None,
            }],
            metric: vec![],
            name: "g".into(),
            params: vec![],
            ret: int_of(v("r")),
            body: Expr::IntLit(0),
            proof: false,
        });
        let body = Expr::Let(
            vec![LetBind {
                opened: vec![("r1".into(), Sort::Nat)],
                proof: false,
                name: Some("y".into()),
                ty: None,
                value: call("g", vec![]),
                mutable: false,
            }],
            Box::new(call("needs_nat", vec![var("y")])),
        );
        let mut defs = vec![g];
        defs.extend(with_main(body).defs().to_vec());
        let program = Program::new(defs);
        let opened = obligations(&program, &Program::new(vec![]))
            .into_iter()
            .find(|o| matches!(o.origin, Origin::Call { ref callee } if callee == "needs_nat"))
            .expect("the call");
        assert!(
            opened.hyps.iter().any(|h| h.to_string() == "r1 >= 0"),
            "the witness was not named: {:?}",
            opened.hyps
        );
    }

    #[test]
    fn a_proof_keeps_every_index_its_proposition_is_about() {
        // `prval pf = FACTind{3}{2}(...)` proves `FACT(3, 6)`.  Binding
        // only the first index would leave a proof that says half of
        // what it says, and nothing downstream could use it.
        let ctor = Def::Extern(ats2_domain::ast::FunDecl {
            linear: false,
            proof: false,
            name: "FACTind".into(),
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("n".into(), Sort::Pos), ("r".into(), Sort::Int)],
                guard: None,
            }],
            existentials: vec![],
            params: vec![],
            ret: Ty::Index(
                Box::new(Ty::Name("FACT".into())),
                vec![v("n"), app("*", v("n"), v("r"))],
            ),
        });
        let body = Expr::Let(
            vec![LetBind {
                opened: vec![],
                proof: true,
                name: Some("pf".into()),
                ty: None,
                value: Expr::Call(
                    Box::new(Expr::StaticInst(Box::new(var("FACTind")), vec![i(3), i(2)])),
                    vec![],
                ),
                mutable: false,
            }],
            Box::new(Expr::Unit),
        );
        let mut defs = vec![ctor];
        defs.extend(with_main(body).defs().to_vec());
        let program = Program::new(defs);
        // The walk records both indices; nothing is demanded, but the
        // proof is in scope with everything it proves.
        assert!(
            obligations(&program, &Program::new(vec![]))
                .iter()
                .all(|o| o.goal.to_string() != "3 > 0"
                    || crate::constraints::entails(&o.hyps, &o.goal)
                        == crate::constraints::Verdict::Proved)
        );
        assert_eq!(
            proof_indices(&program, "pf"),
            vec!["3".to_string(), "3 * 2".to_string()]
        );
    }

    /// The indices the walk gave a proof binding — reached by re-walking
    /// with a probe, since obligations alone do not show an environment.
    fn proof_indices(program: &Program, name: &str) -> Vec<String> {
        let sigs = SigTable::of(program);
        let ctors = CtorTable::default();
        let mut walk = Walk {
            sigs: &sigs,
            ctors: &ctors,
            consts: HashMap::new(),
            out: Vec::new(),
            function: String::new(),
            metric: Vec::new(),
            last_call: None,
        };
        let mut env = IndexEnv::new();
        for def in program.defs() {
            if let Def::Implement(im) = def {
                if let Expr::Let(binds, _) = &im.body {
                    for b in binds {
                        walk.let_bind(b, &mut env);
                    }
                }
            }
        }
        env.indices_of(name).iter().map(|t| t.to_string()).collect()
    }

    #[test]
    fn a_proof_determines_the_witness_the_arithmetic_cannot() {
        // `fun f {n:nat} (x: int n): [r:int] (P(n, r) | int(r*k)) =
        // (pf | v)` — the existential `r` appears multiplied in the value
        // half, and no linear solver divides.  The proposition names it
        // directly: matching `P(n, r)` against the proof's own
        // `P(n, 3)` fixes `r` at three, and the value half is then an
        // ordinary equation.  This is what a `dataprop` is *for*.
        let ctor = Def::Extern(ats2_domain::ast::FunDecl {
            linear: false,
            proof: true,
            name: "mk".into(),
            ty_params: vec![],
            universals: vec![],
            existentials: vec![],
            params: vec![],
            ret: Ty::Index(Box::new(Ty::Name("P".into())), vec![v("n"), i(3)]),
        });
        let body = Expr::Let(
            vec![LetBind {
                opened: vec![],
                proof: true,
                name: Some("pf".into()),
                ty: None,
                value: call("mk", vec![]),
                mutable: false,
            }],
            Box::new(Expr::ProofPair(
                Box::new(var("pf")),
                Box::new(Expr::BinOp(
                    BinOp::Mul,
                    Box::new(Expr::IntLit(3)),
                    Box::new(var("k")),
                )),
            )),
        );
        let f = Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![nat()],
            existentials: vec![Quant {
                vars: vec![("r".into(), Sort::Int)],
                guard: None,
            }],
            metric: vec![],
            name: "f".into(),
            params: vec![p("x", int_of(v("n"))), p("k", int_of(v("k")))],
            ret: Ty::Proof(
                Box::new(Ty::Index(
                    Box::new(Ty::Name("P".into())),
                    vec![v("n"), v("r")],
                )),
                Box::new(int_of(app("*", v("r"), v("k")))),
            ),
            body,
            proof: false,
        });
        let program = Program::new(vec![ctor, f]);
        for o in obligations(&program, &Program::new(vec![]))
            .iter()
            .filter(|o| matches!(o.origin, Origin::Return { .. }))
        {
            assert_eq!(
                crate::constraints::entails(&o.hyps, &o.goal),
                crate::constraints::Verdict::Proved,
                "goal {} from {:?}",
                o.goal,
                o.hyps
            );
        }
    }

    #[test]
    fn a_pair_without_a_matching_proof_still_answers_for_its_value() {
        // No proposition to read the witness from, so the value half is
        // all there is — and it must still be checked.
        let f = Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![nat()],
            existentials: vec![],
            metric: vec![],
            name: "f".into(),
            params: vec![p("x", int_of(v("n")))],
            ret: int_of(app("+", v("n"), i(1))),
            body: Expr::ProofPair(Box::new(var("pf")), Box::new(var("x"))),
            proof: false,
        });
        assert!(
            goals(&Program::new(vec![f])).contains(&"n == n + 1".to_string()),
            "{:?}",
            goals(&Program::new(vec![f2()]))
        );
    }

    fn f2() -> Def {
        Def::Fun(FunDef {
            ty_params: vec![],
            universals: vec![nat()],
            existentials: vec![],
            metric: vec![],
            name: "f".into(),
            params: vec![p("x", int_of(v("n")))],
            ret: int_of(app("+", v("n"), i(1))),
            body: Expr::ProofPair(Box::new(var("pf")), Box::new(var("x"))),
            proof: false,
        })
    }

    #[test]
    fn an_assertion_establishes_what_it_asserts() {
        // `val () = assertexn(n >= 0)` is how ATS moves a check from run
        // time into the static world: past that line the program either
        // stopped or `n` is a nat, and a checker that ignored it would
        // reject the argument handling of half the corpus.
        let assertion = Expr::Call(
            Box::new(var("assertexn")),
            vec![Expr::BinOp(
                BinOp::Ge,
                Box::new(var("x")),
                Box::new(Expr::IntLit(0)),
            )],
        );
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![],
                vec![p("x", int_of(v("k")))],
                Ty::Name("int".into()),
                Expr::Let(
                    vec![LetBind {
                        opened: vec![],
                        proof: false,
                        name: None,
                        ty: None,
                        value: assertion,
                        mutable: false,
                    }],
                    Box::new(call("needs_nat", vec![var("x")])),
                ),
            ),
        ]);
        let owed = obligations(&program, &Program::new(vec![]))
            .into_iter()
            .find(|o| matches!(o.origin, Origin::Call { ref callee } if callee == "needs_nat"))
            .expect("the call");
        assert_eq!(
            crate::constraints::entails(&owed.hyps, &owed.goal),
            crate::constraints::Verdict::Proved,
            "goal {} from {:?}",
            owed.goal,
            owed.hyps
        );
    }

    #[test]
    fn an_ordinary_call_establishes_nothing_merely_by_being_made() {
        // Only the assertions assert.  Any other function taking a
        // boolean would otherwise make its argument true by being called.
        let checked = Expr::Call(
            Box::new(var("check")),
            vec![Expr::BinOp(
                BinOp::Ge,
                Box::new(var("x")),
                Box::new(Expr::IntLit(0)),
            )],
        );
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![],
                vec![p("x", int_of(v("k")))],
                Ty::Name("int".into()),
                Expr::Let(
                    vec![LetBind {
                        opened: vec![],
                        proof: false,
                        name: None,
                        ty: None,
                        value: checked,
                        mutable: false,
                    }],
                    Box::new(call("needs_nat", vec![var("x")])),
                ),
            ),
        ]);
        let owed = obligations(&program, &Program::new(vec![]))
            .into_iter()
            .find(|o| matches!(o.origin, Origin::Call { ref callee } if callee == "needs_nat"))
            .expect("the call");
        assert_ne!(
            crate::constraints::entails(&owed.hyps, &owed.goal),
            crate::constraints::Verdict::Proved
        );
    }

    #[test]
    fn an_ascription_is_checked_branch_by_branch_like_any_other_claim() {
        // `val n = (if n >= 0 then n else 0): intGte(0)` is how the
        // corpus bounds an integer it read from the command line.  The
        // claim has to reach into the arms, exactly as a result type
        // does — joined first, it is unprovable.
        let x = var("x");
        let inner = Expr::IfThenElse(
            Box::new(Expr::BinOp(
                BinOp::Ge,
                Box::new(x.clone()),
                Box::new(Expr::IntLit(0)),
            )),
            Box::new(x),
            Box::new(Expr::IntLit(0)),
        );
        let bounded = Expr::Ascribe(
            Box::new(inner),
            Ty::Index(Box::new(Ty::Name("intGte".into())), vec![i(0)]),
        );
        let program = Program::new(vec![
            fun(
                "needs_nat",
                vec![nat()],
                vec![p("x", int_of(v("n")))],
                Ty::Name("int".into()),
                Expr::IntLit(0),
            ),
            fun(
                "caller",
                vec![],
                vec![p("x", int_of(v("k")))],
                Ty::Name("int".into()),
                Expr::Let(
                    vec![LetBind {
                        opened: vec![],
                        proof: false,
                        name: Some("y".into()),
                        ty: None,
                        value: bounded,
                        mutable: false,
                    }],
                    Box::new(call("needs_nat", vec![var("y")])),
                ),
            ),
        ]);
        for o in obligations(&program, &Program::new(vec![])) {
            assert_eq!(
                crate::constraints::entails(&o.hyps, &o.goal),
                crate::constraints::Verdict::Proved,
                "goal {} from {:?}",
                o.goal,
                o.hyps
            );
        }
    }

    #[test]
    fn every_obligation_says_which_function_it_came_from() {
        let program = Program::new(vec![fun(
            "succ",
            vec![nat()],
            vec![p("x", int_of(v("n")))],
            int_of(app("+", v("n"), i(1))),
            var("x"),
        )]);
        assert_eq!(
            obligations(&program, &Program::new(vec![]))[0].origin,
            Origin::Return {
                function: "succ".into()
            }
        );
    }
}
