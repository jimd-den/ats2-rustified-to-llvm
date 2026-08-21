//! # Signatures, and what a call site owes one
//!
//! *Literate note.*  This module answers one question: given a callee's
//! declared type and the indices of the arguments actually handed to it,
//! what must the caller prove, and what may it then believe?
//!
//! Keeping that separate from the walk matters because the two change for
//! different reasons.  The walk grows when the *language* grows — a new
//! expression form, a new binder.  This grows when the *signature*
//! language grows — an existential result, a guard, a metric.  A module
//! that did both would be edited by everyone.
//!
//! The one rule it will not bend: nothing is invented.  An argument whose
//! index nobody knows leaves the callee's variable *undetermined*, and it
//! says so rather than quietly skolemising the demand away.  Whether an
//! undetermined variable is an error is a policy question, and policy
//! lives at the edge of the checker, not in its middle.

use std::collections::HashMap;

#[cfg(test)]
use ats2_domain::ast::Expr;
use ats2_domain::ast::{Def, Program, Ty};
use ats2_domain::statics::{Quant, SExp};

use super::index_env::Fresh;
use super::unify::Match;

/// A function's promise, stripped of its body.
///
/// Definitions and bare declarations become the same thing here: a call
/// site cannot tell them apart, and should not have to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signature {
    pub name: String,
    /// The `a` of `fun{a:t@ype} f` — the types this definition abstracts
    /// over.
    ///
    /// It is here to say what a brace or angle group at a call site
    /// *meant*: a template's arguments choose which code is built, and
    /// reading one as an index would fix a `{n:nat}` to a type name and
    /// prove whatever followed from nonsense.
    pub ty_params: Vec<String>,
    /// `{n:nat | n > 0}` — what the caller must establish.
    pub universals: Vec<Quant>,
    /// `[r:int]` on the result — what the caller may then assume.
    pub existentials: Vec<Quant>,
    pub params: Vec<Ty>,
    /// Which parameters are *lent* rather than given — the `!` and `&`
    /// of `(xs: !list_vt(a))`.
    ///
    /// It is here beside the types because it is part of the same
    /// promise: what a function asks for includes whether it means to
    /// keep it.
    pub borrowed: Vec<bool>,
    pub ret: Ty,
    /// `.<n>.` — the term a recursive call must decrease.
    pub metric: Vec<SExp>,
}

/// What the walk could say about one argument.
///
/// Two facts, and a parameter's type decides which of them is wanted.
/// `int(n)` asks what the argument *is*; `string(n)` asks how *long* it
/// is; `intGte(0)` asks neither and demands a bound instead.  Carrying
/// only the first is why a length-indexed parameter left its variable
/// undetermined and every promise about the result unprovable.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Arg {
    /// The static term the argument's value equals, when one is known.
    pub value: Option<SExp>,
    /// How long the argument is, when its type said.
    pub size: Option<SExp>,
    /// The whole type the argument was declared with.
    ///
    /// Indices sit at every depth of a type — `list0(list(int, n))`
    /// buries one inside its element — so the general rule is to match
    /// the declared type against the actual one and take the equations
    /// wherever they fall.  A single length is that rule read at depth
    /// nought.
    pub ty: Option<Ty>,
}

impl Arg {
    pub fn value(term: SExp) -> Arg {
        Arg {
            value: Some(term),
            size: None,
            ty: None,
        }
    }

    pub fn unknown() -> Arg {
        Arg::default()
    }
}

/// What one call site produced: its debts, and its dividends.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CallFacts {
    /// Propositions the caller must prove.
    pub demands: Vec<SExp>,
    /// The index of the value returned, when the signature pins one down.
    pub result: Option<SExp>,
    /// What the caller may assume of that value afterwards.
    pub assumptions: Vec<SExp>,
    /// The callee's arithmetic variables that this call did not determine.
    pub undetermined: Vec<String>,
    /// What those variables are called in [`Self::result_indices`].
    ///
    /// `undetermined` records what the *callee* named them; these are
    /// the unspellable names they were renamed to.  Keeping them is what
    /// lets a caller who knows the answer the call was supposed to give
    /// work backwards to them — a nullary proof constructor determines
    /// its own variables from nowhere else.
    pub renamed: Vec<String>,
    /// The metric, instantiated at this call — what a recursive call must
    /// be shown to have decreased.
    pub metric: Vec<SExp>,
    /// Every index the result carries.
    ///
    /// One is the ordinary case — `int(n)` — but a *proof* is indexed by
    /// every number its proposition is about, and `FACT(n, n*r)` keeping
    /// only the first would be a proof that says half of what it says.
    pub result_indices: Vec<SExp>,
    /// The type of what came back, with every index the call settled
    /// filled in.
    ///
    /// A value that was never given a name — `g(mk(x))` — carries its
    /// indices only in its type, and a checker that learns types from
    /// names alone cannot follow one.
    pub result_ty: Option<Ty>,
    /// The fresh variables this call invented for the callee's
    /// existentials, in the order they were declared.
    ///
    /// `val [r1:int] (pf | x) = f(...)` gives one of them a name in the
    /// caller's scope, and can only do so if the call says which it was.
    pub witnesses: Vec<SExp>,
}

impl Signature {
    /// Read the callable contract of a function definition.
    ///
    /// This deliberately says nothing about where the definition is visible.
    /// The global table and the lexical walk own that policy; both use the
    /// same representation of the contract.
    pub(super) fn of_fun(f: &ats2_domain::ast::FunDef) -> Signature {
        Signature {
            name: f.name.clone(),
            ty_params: f.ty_params.clone(),
            universals: f.universals.clone(),
            existentials: f.existentials.clone(),
            params: f.params.iter().map(|p| p.ty.clone()).collect(),
            borrowed: f.params.iter().map(|p| p.borrowed).collect(),
            ret: f.ret.clone(),
            metric: f.metric.clone(),
        }
    }

    /// This signature at one instance of its type parameters.
    ///
    /// `nth<N2>(...)` returns an `N2`, and `N2` is `intGte(2)` — an
    /// integer known to be at least two.  Reading the result as the bare
    /// parameter `a` learns nothing from a call that says precisely what
    /// it produces, which is what naming an instance is *for*.
    ///
    /// Given the wrong number of arguments it declines and hands back
    /// the signature as written: a call that does not say which instance
    /// it means teaches nothing, and inventing one would be worse.
    pub fn at_instance(&self, ty_args: &[Ty]) -> Signature {
        if ty_args.is_empty() || ty_args.len() != self.ty_params.len() {
            return self.clone();
        }
        let subst: HashMap<String, Ty> = self
            .ty_params
            .iter()
            .cloned()
            .zip(ty_args.iter().cloned())
            .collect();
        Signature {
            name: self.name.clone(),
            // Its parameters are chosen; it abstracts over nothing now.
            ty_params: Vec::new(),
            universals: self.universals.clone(),
            existentials: self.existentials.clone(),
            params: self
                .params
                .iter()
                .map(|p| substitute_ty(p, &subst))
                .collect(),
            borrowed: self.borrowed.clone(),
            ret: substitute_ty(&self.ret, &subst),
            metric: self.metric.clone(),
        }
    }

    /// Every arithmetic variable the universals bind.  Type-sorted ones
    /// are not indices and take no part in any of this.
    fn universal_vars(&self) -> Vec<String> {
        self.universals
            .iter()
            .flat_map(|q| &q.vars)
            .filter(|(_, s)| s.is_arithmetic())
            .map(|(n, _)| n.clone())
            .collect()
    }

    /// Every variable the universals bind, arithmetic or not, in the
    /// order they were written.
    ///
    /// The order is what `f{a}{n}` means: one term per quantifier, in
    /// sequence, and a type-sorted one takes its place in that sequence
    /// without becoming an index.
    fn universal_slots(&self) -> Vec<(String, bool)> {
        self.universals
            .iter()
            .flat_map(|q| &q.vars)
            .map(|(n, s)| (n.clone(), s.is_arithmetic()))
            .collect()
    }

    /// Match the declared parameter types against the argument indices,
    /// and report the debts and dividends that follow.
    ///
    /// `statics` are the terms written in braces — `ax{3}()` — and they
    /// outrank anything unification would have worked out, because they
    /// are what the source said.  A proof function is the case that
    /// needs them: it takes no value arguments at all, so unification has
    /// nothing to work from and the braces are the only thing saying
    /// *which* instance of the axiom is being invoked.
    ///
    /// `args` is one entry per argument: `None` where the walk could not
    /// say what the argument's index is.
    pub fn at_call(&self, statics: &[SExp], args: &[Arg], fresh: &Fresh) -> CallFacts {
        self.at_call_against(statics, args, None, fresh)
    }

    /// Instantiate a call whose surrounding context may require one result.
    ///
    /// `fun {n:nat} choose(): int n` has no dynamic argument from which to
    /// infer `n`, but in `val x: int 3 = choose()` the expected result does.
    /// Matching it before obligations are produced turns the call into
    /// `choose{3}()` while retaining the obligation that `3` is a natural.
    pub fn at_call_against(
        &self,
        statics: &[SExp],
        args: &[Arg],
        expected: Option<&SExp>,
        fresh: &Fresh,
    ) -> CallFacts {
        let vars = self.universal_vars();
        let mut m = Match::default();
        let mut asked: Vec<SExp> = Vec::new();
        // Written first, so that unification finds them already settled
        // and any disagreement becomes an equation the call must justify
        // rather than silently overwriting what was written down.
        for ((name, arithmetic), term) in self.universal_slots().iter().zip(statics) {
            if *arithmetic {
                m.against(&SExp::Var(name.clone()), term, &vars);
            }
        }
        for (declared, actual) in self.params.iter().zip(args) {
            match claim_of(declared) {
                // `int(n)` — the argument *is* the index, so the index
                // is what the argument determines.
                Some(SExp::App(ref op, ref parts))
                    if op == "==" && parts.len() == 2 && parts[0] == SExp::Var(SELF.into()) =>
                {
                    let Some(value) = &actual.value else { continue };
                    m.against(&parts[1], value, &vars);
                }
                // `intGte(0)` — a bound, which the *caller* owes.  There
                // is nothing here to unify: unifying against the `0`
                // would say the argument is nought, and refute every
                // call that passes anything else.
                Some(claim) => {
                    if let Some(value) = &actual.value {
                        asked.push(claim.substitute(&[(SELF.to_string(), value.clone())]));
                    }
                }
                // `string(n)`, `array(a, n)`, `list0(list(int, n))` —
                // the indices measure the argument rather than naming
                // it, and they may sit at any depth.  Matching the two
                // types against each other takes them wherever they fall.
                None => match &actual.ty {
                    Some(actual) => match_types(declared, actual, &vars, &mut m),
                    None => {
                        let ([pattern], Some(size)) = (declared.indices(), &actual.size) else {
                            continue;
                        };
                        m.against(pattern, size, &vars);
                    }
                },
            }
        }
        if let Some(expected) = expected {
            if let Some(SExp::App(op, parts)) = claim_of(&self.ret) {
                if op == "==" && parts.len() == 2 && parts[0] == SExp::Var(SELF.into()) {
                    let open: Vec<String> = vars
                        .iter()
                        .filter(|v| m.get(v).is_none())
                        .cloned()
                        .collect();
                    if parts[1].vars().iter().any(|v| open.contains(v)) {
                        m.against(&parts[1], expected, &open);
                    }
                }
            }
        }
        let undetermined: Vec<String> = vars
            .iter()
            .filter(|v| m.get(v).is_none())
            .cloned()
            .collect();
        // A variable the call did not determine is still the *callee's*
        // variable, and it must not be readable as the caller's one of
        // the same name.  Renaming it to something unspellable is what
        // turns "I could not work this out" into `Unknown` instead of
        // into a refutation drawn from facts about a different variable
        // entirely — the one wrong answer a checker may never give.
        let renaming: Vec<(String, SExp)> = undetermined
            .iter()
            .map(|v| (v.clone(), fresh.var(v)))
            .collect();
        let renamed: Vec<String> = renaming
            .iter()
            .filter_map(|(_, e)| match e {
                SExp::Var(n) => Some(n.clone()),
                _ => None,
            })
            .collect();
        let mut subst = m.subst();
        subst.extend(renaming);

        // The debt: what the quantifiers demand, plus what matching could
        // not settle by binding.  Both are read in the caller's terms.
        let mut demands: Vec<SExp> = self
            .universals
            .iter()
            .flat_map(Quant::hypotheses)
            .chain(m.equations.iter().cloned())
            .chain(asked)
            .map(|h| h.substitute(&subst))
            .collect();
        demands.retain(|d| !matches!(d, SExp::BoolLit(true)));
        demands.dedup();

        // The dividend: the result's index, with the existentials given
        // names the caller cannot spell — it knows a witness exists, and
        // nothing more.
        let mut result_subst = subst.clone();
        let mut assumptions = Vec::new();
        let mut witnesses = Vec::new();
        for q in &self.existentials {
            let renaming: Vec<(String, SExp)> = q
                .vars
                .iter()
                .filter(|(_, s)| s.is_arithmetic())
                .map(|(n, _)| (n.clone(), fresh.var(n)))
                .collect();
            for h in q.hypotheses() {
                assumptions.push(h.substitute(&renaming).substitute(&subst));
            }
            witnesses.extend(renaming.iter().map(|(_, w)| w.clone()));
            result_subst.extend(renaming);
        }

        let result_indices: Vec<SExp> = self
            .ret
            .indices()
            .iter()
            .map(|t| t.substitute(&result_subst))
            .collect();
        // A value has one index; a proof has one per number its
        // proposition is about, and none of them is "the" result.
        let result = match result_indices.as_slice() {
            [only] => Some(only.clone()),
            _ => None,
        };
        let metric = self.metric.iter().map(|m| m.substitute(&subst)).collect();
        let result_ty = Some(substitute_indices(&self.ret, &result_subst));
        CallFacts {
            demands,
            result,
            result_ty,
            assumptions,
            undetermined,
            renamed,
            metric,
            result_indices,
            witnesses,
        }
    }
}

/// Every signature a program declares, by name.
#[derive(Debug, Clone, Default)]
pub struct SigTable {
    by_name: HashMap<String, Signature>,
}

impl SigTable {
    /// Collect the signatures a program exposes at its top level.
    ///
    /// Nested functions are lexical declarations. The expression walk keeps
    /// those in a scope stack so repeated helper names cannot collide and a
    /// local declaration cannot leak outside the `let` that introduced it.
    pub fn of(program: &Program) -> Self {
        let mut table = SigTable::default();
        for def in program.defs() {
            match def {
                Def::Fun(f) => table.add_fun(f),
                Def::Extern(d) => {
                    table.insert(Signature {
                        name: d.name.clone(),
                        ty_params: d.ty_params.clone(),
                        universals: d.universals.clone(),
                        existentials: d.existentials.clone(),
                        params: d.params.iter().map(|p| p.ty.clone()).collect(),
                        borrowed: d.params.iter().map(|p| p.borrowed).collect(),
                        ret: d.ret.clone(),
                        metric: vec![],
                    });
                }
                _ => {}
            }
        }
        table
    }

    fn add_fun(&mut self, f: &ats2_domain::ast::FunDef) {
        self.insert(Signature::of_fun(f));
    }

    /// Lay another table over this one: what `other` declares wins.
    ///
    /// This is how a program's own declaration beats the prelude's — the
    /// prelude fills gaps, it does not shadow.
    pub fn extend(&mut self, other: SigTable) {
        self.by_name.extend(other.by_name);
    }

    pub fn insert(&mut self, sig: Signature) {
        self.by_name.insert(sig.name.clone(), sig);
    }

    pub fn get(&self, name: &str) -> Option<&Signature> {
        self.by_name.get(name)
    }
}

/// The indices ATS's entry point carries but never writes down.
///
/// `main0` and `main` are declared by the prelude as
/// `{n:nat} (argc: int n, argv: !argv(n))`: the count and the argument
/// array are indexed by the *same* variable, and the array is as long as
/// the count says.  A program's source never repeats that, so a checker
/// that only reads what is written cannot prove `if argc >= 2 then
/// argv[1]` — which is how much of the corpus reads its arguments.
///
/// It lives here, beside the other knowledge about signatures, rather
/// than in the walk: it is a fact about one particular type, and the walk
/// is not allowed to know any.
pub fn entry_point_indices(name: &str, params: &[ats2_domain::ast::Param]) -> Option<EntryPoint> {
    if !matches!(name, "main0" | "main") {
        return None;
    }
    let [argc, argv] = params else { return None };
    let n = SExp::Var(format!("{}%argc", argc.name));
    Some(EntryPoint {
        count: (argc.name.clone(), n.clone()),
        // The array's *length* is that same term — not its value.
        argv: (argv.name.clone(), n),
    })
}

/// What a datatype's constructors take apart into.
///
/// `case xs of list0_cons (x, rest)` needs to know that `rest` is a list
/// of whatever `xs` was a list of — and its *length*, which is where a
/// recursion over an indexed list is checked or is not.
#[derive(Debug, Clone, Default)]
pub struct CtorTable {
    /// constructor name -> (the datatype it builds, its type parameters,
    /// the types of its fields)
    by_name: HashMap<String, (String, Vec<String>, Vec<Ty>)>,
    /// datatype name -> (its type parameters, one entry per constructor)
    ///
    /// Kept so that a constructor written under one of its *other* names
    /// can still be found.  ATS spells the list constructors several
    /// ways — `cons`, `list_cons`, `list_vt_cons` — and which one a
    /// program wrote says nothing about what the value is made of.
    by_datatype: HashMap<String, (Vec<String>, Vec<Vec<Ty>>)>,
}

impl CtorTable {
    /// Collect every constructor a program's datatypes declare.
    pub fn of(program: &Program) -> Self {
        let mut table = CtorTable::default();
        for def in program.defs() {
            if let Def::Datatype(d) = def {
                for ctor in &d.ctors {
                    table.by_name.insert(
                        ctor.name.clone(),
                        (d.name.clone(), d.ty_params.clone(), ctor.fields.clone()),
                    );
                }
                table.by_datatype.insert(
                    d.name.clone(),
                    (
                        d.ty_params.clone(),
                        d.ctors.iter().map(|c| c.fields.clone()).collect(),
                    ),
                );
            }
        }
        table
    }

    pub fn extend(&mut self, other: CtorTable) {
        self.by_name.extend(other.by_name);
        self.by_datatype.extend(other.by_datatype);
    }

    /// The types this constructor's fields have, given the type the
    /// value being taken apart was known to have.
    ///
    /// `None` when the constructor is unknown or the subject's type does
    /// not name the datatype it builds — in which case the fields are
    /// unknowns, exactly as before. The rule adds knowledge where there
    /// is some, and invents none.
    pub fn fields_of(&self, ctor: &str, arity: usize, subject: Option<&Ty>) -> Option<Vec<Ty>> {
        let (datatype, params, fields) = match self.by_name.get(ctor) {
            Some(found) => found.clone(),
            // A name this table does not hold — one of the several
            // spellings ATS gives the same constructor.  What the value
            // is made of is decided by the *datatype*, so if the subject
            // names one and exactly one of its constructors takes this
            // many fields, that is the one that was written.  Two of the
            // same arity is a genuine ambiguity and is declined rather
            // than guessed at.
            None => {
                let name = match subject.map(strip_index)? {
                    Ty::App(name, _) | Ty::Name(name) => name.clone(),
                    _ => return None,
                };
                let (params, ctors) = self.by_datatype.get(&name)?;
                let mut fits = ctors.iter().filter(|f| f.len() == arity);
                let only = fits.next()?;
                if fits.next().is_some() {
                    return None;
                }
                (name, params.clone(), only.clone())
            }
        };
        let args = match subject.map(strip_index) {
            Some(Ty::App(name, args)) if *name == datatype => args.clone(),
            Some(Ty::Name(name)) if *name == datatype => Vec::new(),
            // The subject's type is unknown or is not this datatype:
            // the field types stand as declared, which for a
            // parameterised datatype means they stay abstract.
            _ => Vec::new(),
        };
        let subst: HashMap<String, Ty> = params.iter().cloned().zip(args).collect();
        Some(fields.iter().map(|f| substitute_ty(f, &subst)).collect())
    }
}

/// Rewrite every index in a type, at every depth.
///
/// A result type is written in the callee's variables; what comes back
/// is that type in the caller's, and the difference is one substitution
/// applied wherever an index appears.
pub fn substitute_indices(ty: &Ty, subst: &[(String, SExp)]) -> Ty {
    match ty {
        Ty::Index(base, idx) => Ty::Index(
            Box::new(substitute_indices(base, subst)),
            idx.iter().map(|t| t.substitute(subst)).collect(),
        ),
        Ty::App(n, args) => Ty::App(
            n.clone(),
            args.iter().map(|a| substitute_indices(a, subst)).collect(),
        ),
        Ty::Tuple(items) => Ty::Tuple(items.iter().map(|i| substitute_indices(i, subst)).collect()),
        Ty::Proof(p, v) => Ty::Proof(
            Box::new(substitute_indices(p, subst)),
            Box::new(substitute_indices(v, subst)),
        ),
        Ty::Fun(ps, r) => Ty::Fun(
            ps.iter().map(|p| substitute_indices(p, subst)).collect(),
            Box::new(substitute_indices(r, subst)),
        ),
        Ty::Record(fs) => Ty::Record(
            fs.iter()
                .map(|(n, t)| (n.clone(), substitute_indices(t, subst)))
                .collect(),
        ),
        Ty::Name(_) => ty.clone(),
    }
}

/// Replace a datatype's type parameters throughout a field's type.
fn substitute_ty(ty: &Ty, subst: &HashMap<String, Ty>) -> Ty {
    match ty {
        Ty::Name(n) => subst.get(n).cloned().unwrap_or_else(|| ty.clone()),
        Ty::App(n, args) => Ty::App(
            n.clone(),
            args.iter().map(|a| substitute_ty(a, subst)).collect(),
        ),
        Ty::Tuple(items) => Ty::Tuple(items.iter().map(|i| substitute_ty(i, subst)).collect()),
        Ty::Index(base, idx) => Ty::Index(Box::new(substitute_ty(base, subst)), idx.clone()),
        Ty::Proof(p, v) => Ty::Proof(
            Box::new(substitute_ty(p, subst)),
            Box::new(substitute_ty(v, subst)),
        ),
        Ty::Fun(ps, r) => Ty::Fun(
            ps.iter().map(|p| substitute_ty(p, subst)).collect(),
            Box::new(substitute_ty(r, subst)),
        ),
        Ty::Record(fs) => Ty::Record(
            fs.iter()
                .map(|(n, t)| (n.clone(), substitute_ty(t, subst)))
                .collect(),
        ),
    }
}

/// Match a declared type against an actual one, taking the index
/// equations wherever they fall.
///
/// The two types have the same *shape* — that is the type checker's
/// business, not this one's — so the walk is a parallel descent, and
/// every pair of index lists it meets on the way is an equation the call
/// determines or owes.  Reaching only the outermost pair is what left a
/// list of lists unchecked.
pub fn match_types(declared: &Ty, actual: &Ty, vars: &[String], m: &mut Match) {
    for (pattern, supplied) in declared.indices().iter().zip(actual.indices()) {
        m.against(pattern, supplied, vars);
    }
    match (strip_index(declared), strip_index(actual)) {
        (Ty::App(dn, dargs), Ty::App(an, aargs)) if dn == an && dargs.len() == aargs.len() => {
            for (d, a) in dargs.iter().zip(aargs) {
                match_types(d, a, vars, m);
            }
        }
        (Ty::Tuple(ds), Ty::Tuple(as_)) if ds.len() == as_.len() => {
            for (d, a) in ds.iter().zip(as_) {
                match_types(d, a, vars, m);
            }
        }
        (Ty::Fun(dps, dr), Ty::Fun(aps, ar)) if dps.len() == aps.len() => {
            for (d, a) in dps.iter().zip(aps) {
                match_types(d, a, vars, m);
            }
            match_types(dr, ar, vars, m);
        }
        (Ty::Proof(_, dv), Ty::Proof(_, av)) => match_types(dv, av, vars, m),
        _ => {}
    }
}

/// A type with its own outermost indices set aside.
pub fn strip_index(ty: &Ty) -> &Ty {
    match ty {
        Ty::Index(base, _) => strip_index(base),
        _ => ty,
    }
}

/// The signature an `implement` is answering to.
///
/// `extern fun f {n:nat} (x: int n): int (n+1)` followed by
/// `implement f (x) = ...` writes the quantifier once, at the
/// declaration.  The implementation repeats the parameter *names* and
/// nothing else, so a checker that read only the `implement` would see an
/// unindexed parameter and could prove nothing about the body.
///
/// The declaration fills gaps; it does not overrule.  Where the
/// implementation annotates a parameter itself, that annotation wins —
/// it is the more specific statement, and the one the reader is looking
/// at.
pub fn declared_for(
    sig: Option<&Signature>,
    im: &ats2_domain::ast::ImplementDef,
) -> (Vec<Quant>, Vec<ats2_domain::ast::Param>, Vec<Quant>, Ty) {
    let ret = im.ret.clone();
    let Some(sig) = sig else {
        return (
            Vec::new(),
            im.params.clone(),
            Vec::new(),
            ret.unwrap_or(Ty::Name("void".into())),
        );
    };
    let params = im
        .params
        .iter()
        .enumerate()
        .map(
            |(i, p)| match (p.ty.indices().is_empty(), sig.params.get(i)) {
                (true, Some(declared)) => {
                    // A borrow is the declaration's word too: an
                    // implementation that repeats only the names inherits
                    // whether each one was lent or given.
                    ats2_domain::ast::Param {
                        name: p.name.clone(),
                        ty: declared.clone(),
                        borrowed: p.borrowed,
                    }
                }
                _ => p.clone(),
            },
        )
        .collect();
    let ret = ret
        .filter(|t| !t.indices().is_empty())
        .unwrap_or_else(|| sig.ret.clone());
    (
        sig.universals.clone(),
        params,
        sig.existentials.clone(),
        ret,
    )
}

/// What `main0`'s two parameters are, statically.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EntryPoint {
    /// The argument count, and the term it equals.
    pub count: (String, SExp),
    /// The argument array, and the term it is as long as.
    pub argv: (String, SExp),
}

/// The name a claim uses for the value it is about.
///
/// `%` is in it because ATS cannot spell it, so no source term can be
/// mistaken for the value the claim is speaking of.
pub const SELF: &str = "%self";

/// What a type demands of the value that has it, written in terms of
/// [`SELF`].
///
/// Three answers, and the difference between them is the difference
/// between a checker that reads ATS's types and one that reads their
/// syntax:
///
/// * `int(n+1)` is a *singleton*: the value **is** the term.
/// * `intGte(0)`, `sizeLte(k)`, `natLt(n)` are *refinements*: the value
///   is any integer satisfying a bound.  Reading the index as the value
///   here is how a checker convinces itself that every `intGte(0)` is
///   nought.
/// * `string(n)`, `array(a, n)` *measure* the value: `n` is its length,
///   and about the value itself the type says nothing.
pub fn claim_of(ty: &Ty) -> Option<SExp> {
    // `Nat` and `Pos` carry a refinement with no index at all: the name
    // *is* the claim.  Collapsing them to `int` throws away the only
    // thing they say.
    if let Ty::Name(n) = ty {
        let me = SExp::Var(SELF.into());
        return match n.as_str() {
            "nat" | "Nat" => Some(SExp::App(">=".into(), vec![me, SExp::IntLit(0)])),
            "pos" | "Pos" => Some(SExp::App(">".into(), vec![me, SExp::IntLit(0)])),
            _ => None,
        };
    }
    let Ty::Index(base, indices) = ty else {
        return None;
    };
    let name = match &**base {
        Ty::Name(n) => n.as_str(),
        Ty::App(n, _) => n.as_str(),
        _ => return None,
    };
    let me = SExp::Var(SELF.into());
    let rel = |op: &str, k: &SExp| SExp::App(op.into(), vec![me.clone(), k.clone()]);
    if is_singleton_indexed(base) {
        let [only] = indices.as_slice() else {
            return None;
        };
        return Some(rel("==", only));
    }
    let (flavour, bound) = split_refinement(name)?;
    let [limit] = indices.as_slice() else {
        return None;
    };
    let claim = rel(bound, limit);
    // `natLt(n)` is `0 <= i < n`, and the lower half is the half that
    // makes a subscript safe.
    Some(match flavour {
        "nat" => SExp::App("&&".into(), vec![rel(">=", &SExp::IntLit(0)), claim]),
        _ => claim,
    })
}

/// `intGte` → `("int", ">=")`, and the like.
///
/// ATS names these types rather than writing the bound out, so the
/// relation has to be read back out of the name.
fn split_refinement(name: &str) -> Option<(&str, &'static str)> {
    for (suffix, op) in [("Gte", ">="), ("Gt", ">"), ("Lte", "<="), ("Lt", "<")] {
        if let Some(flavour) = name.strip_suffix(suffix) {
            if matches!(flavour, "int" | "nat" | "size" | "ssize" | "uint" | "usize") {
                return Some((flavour, op));
            }
        }
    }
    None
}

/// Whether a type's index *is* its value, rather than a measure of it.
///
/// `int(n)` is the type of the single integer `n`; `string(n)` is the
/// type of *any* string of length `n`.  Both are written the same way, so
/// the difference has to be known rather than derived — and getting it
/// wrong in either direction produces a checker that reasons confidently
/// about the wrong number.
pub fn is_singleton_indexed(base: &Ty) -> bool {
    let name = match base {
        Ty::Name(n) => n.as_str(),
        Ty::App(n, _) => n.as_str(),
        _ => return false,
    };
    matches!(
        name,
        "int"
            | "uint"
            | "bool"
            | "char"
            | "size_t"
            | "ssize_t"
            | "sint"
            | "lint"
            | "llint"
            | "nat"
            | "pos"
            | "g0int"
            | "g1int"
            | "g0uint"
            | "g1uint"
            | "double"
            | "float"
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use ats2_domain::ast::{Def, FunDef, Param, Program};
    use ats2_domain::statics::Sort;

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

    /// `fun f {n:nat} (x: int n): int (n+1)`
    fn succ_sig() -> Signature {
        Signature {
            name: "f".into(),
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("n".into(), Sort::Nat)],
                guard: None,
            }],
            existentials: vec![],
            params: vec![int_of(v("n"))],
            borrowed: Vec::new(),
            ret: int_of(app("+", v("n"), i(1))),
            metric: vec![],
        }
    }

    #[test]
    fn a_call_owes_what_the_callees_quantifier_demands() {
        let facts = succ_sig().at_call(&[], &[Arg::value(i(-1))], &Fresh::default());
        assert!(
            facts.demands.contains(&app(">=", i(-1), i(0))),
            "the nat-ness of the argument is the debt: {:?}",
            facts.demands
        );
    }

    #[test]
    fn a_call_learns_the_index_of_what_it_gets_back() {
        // Without this the checker can type one call and nothing that
        // reads its result, which is every interesting program.
        let facts = succ_sig().at_call(&[], &[Arg::value(i(5))], &Fresh::default());
        assert_eq!(facts.result, Some(app("+", i(5), i(1))));
    }

    #[test]
    fn an_argument_whose_index_is_unknown_leaves_the_variable_undetermined() {
        // Nothing may be invented here: an unknown argument means the
        // demand is about a value nobody can name, and saying so honestly
        // is what lets the policy layer decide whether that is an error.
        let facts = succ_sig().at_call(&[], &[Arg::unknown()], &Fresh::default());
        assert!(facts.undetermined.contains(&"n".to_string()));
    }

    #[test]
    fn an_existential_result_is_named_freshly_and_its_guard_may_be_assumed() {
        // `: [r:nat] int r` tells the caller nothing about *which* r —
        // only that one exists, and that it is a nat.
        let sig = Signature {
            name: "g".into(),
            ty_params: vec![],
            universals: vec![],
            existentials: vec![Quant {
                vars: vec![("r".into(), Sort::Nat)],
                guard: None,
            }],
            params: vec![],
            borrowed: Vec::new(),
            ret: int_of(v("r")),
            metric: vec![],
        };
        let facts = sig.at_call(&[], &[], &Fresh::default());
        let Some(SExp::Var(name)) = facts.result.clone() else {
            panic!("a variable result")
        };
        assert_ne!(name, "r", "the caller must not be able to name the witness");
        assert_eq!(facts.assumptions, vec![app(">=", SExp::Var(name), i(0))]);
    }

    #[test]
    fn a_guard_on_the_universal_is_owed_alongside_the_sorts_promise() {
        let sig = Signature {
            name: "h".into(),
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("n".into(), Sort::Int)],
                guard: Some(app("<", v("n"), i(10))),
            }],
            existentials: vec![],
            params: vec![int_of(v("n"))],
            borrowed: Vec::new(),
            ret: Ty::Name("int".into()),
            metric: vec![],
        };
        let facts = sig.at_call(&[], &[Arg::value(v("k"))], &Fresh::default());
        assert_eq!(facts.demands, vec![app("<", v("k"), i(10))]);
    }

    #[test]
    fn two_parameters_sharing_a_variable_owe_their_agreement() {
        let sig = Signature {
            name: "pair".into(),
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("n".into(), Sort::Int)],
                guard: None,
            }],
            existentials: vec![],
            params: vec![int_of(v("n")), int_of(v("n"))],
            borrowed: Vec::new(),
            ret: Ty::Name("int".into()),
            metric: vec![],
        };
        let facts = sig.at_call(
            &[],
            &[Arg::value(v("a")), Arg::value(v("b"))],
            &Fresh::default(),
        );
        assert!(facts.demands.contains(&app("==", v("a"), v("b"))));
    }

    /// `praxi ax {n:pos} (): [fact(n) == n * fact(n-1)] void`
    fn axiom() -> Signature {
        let claim = SExp::App(
            "==".into(),
            vec![
                SExp::App("fact".into(), vec![v("n")]),
                app(
                    "*",
                    v("n"),
                    SExp::App("fact".into(), vec![app("-", v("n"), i(1))]),
                ),
            ],
        );
        Signature {
            name: "ax".into(),
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("n".into(), Sort::Pos)],
                guard: None,
            }],
            existentials: vec![Quant {
                vars: vec![],
                guard: Some(claim),
            }],
            params: vec![],
            borrowed: Vec::new(),
            ret: Ty::Name("void".into()),
            metric: vec![],
        }
    }

    #[test]
    fn a_proof_carries_every_index_its_proposition_is_about() {
        // `FACTind{n}{r} (pf) : FACT(n, n*r)` proves a claim about *two*
        // numbers.  Keeping only the first would leave a proof that says
        // half of what it says.
        let sig = Signature {
            name: "FACTind".into(),
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("n".into(), Sort::Pos), ("r".into(), Sort::Int)],
                guard: None,
            }],
            existentials: vec![],
            params: vec![],
            borrowed: Vec::new(),
            ret: Ty::Index(
                Box::new(Ty::Name("FACT".into())),
                vec![v("n"), app("*", v("n"), v("r"))],
            ),
            metric: vec![],
        };
        let facts = sig.at_call(&[i(3), i(2)], &[], &Fresh::default());
        assert_eq!(facts.result_indices, vec![i(3), app("*", i(3), i(2))]);
    }

    #[test]
    fn the_witnesses_a_call_invented_are_offered_by_name() {
        // `val [r1:int] (pf | x) = f(...)` gives the callee's existential
        // a name in the caller's scope.  It can only do that if the call
        // says which fresh variable it invented for it.
        let sig = Signature {
            name: "f".into(),
            ty_params: vec![],
            universals: vec![],
            existentials: vec![Quant {
                vars: vec![("r".into(), Sort::Nat)],
                guard: None,
            }],
            params: vec![],
            borrowed: Vec::new(),
            ret: int_of(v("r")),
            metric: vec![],
        };
        let facts = sig.at_call(&[], &[], &Fresh::default());
        assert_eq!(facts.witnesses.len(), 1);
        assert_eq!(facts.result, Some(facts.witnesses[0].clone()));
    }

    #[test]
    fn a_refinement_parameter_is_demanded_of_the_argument_not_unified_with_it() {
        // `(i: intGte(0))` does not say the argument *is* nought — it
        // says the argument is at least nought.  Unifying against the
        // `0` turns every call into `arg == 0`, and the recursive call
        // `f(i-1)` is then refuted for a program that is correct.
        let sig = Signature {
            name: "nth".into(),
            ty_params: vec![],
            universals: vec![],
            existentials: vec![],
            params: vec![Ty::Index(Box::new(Ty::Name("intGte".into())), vec![i(0)])],
            borrowed: Vec::new(),
            ret: Ty::Name("int".into()),
            metric: vec![],
        };
        let facts = sig.at_call(
            &[],
            &[Arg::value(app("-", v("i"), i(1)))],
            &Fresh::default(),
        );
        assert_eq!(facts.demands, vec![app(">=", app("-", v("i"), i(1)), i(0))]);
    }

    #[test]
    fn a_measured_parameter_is_matched_against_the_arguments_length() {
        // `(s: string(n1))` says the argument is `n1` long.  Matching
        // `n1` against the string's *value* leaves it undetermined and
        // every promise about the result unprovable.
        let sig = Signature {
            name: "len".into(),
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("n".into(), Sort::Nat)],
                guard: None,
            }],
            existentials: vec![],
            params: vec![Ty::Index(Box::new(Ty::Name("string".into())), vec![v("n")])],
            borrowed: Vec::new(),
            ret: int_of(v("n")),
            metric: vec![],
        };
        let facts = sig.at_call(
            &[],
            &[Arg {
                value: Some(v("s")),
                size: Some(v("k")),
                ty: None,
            }],
            &Fresh::default(),
        );
        assert_eq!(facts.result, Some(v("k")));
        assert!(facts.undetermined.is_empty(), "{:?}", facts.undetermined);
    }

    #[test]
    fn matching_reaches_an_index_buried_in_a_type_argument() {
        // `list0(list(int, n))` carries its index a level down.  Reading
        // only the outermost pair leaves `n` undetermined, and every
        // promise about the result unprovable.
        let listed = |inner: Ty| Ty::App("list0".into(), vec![inner]);
        let inner = |k: SExp| {
            Ty::Index(
                Box::new(Ty::App("list0".into(), vec![Ty::Name("int".into())])),
                vec![k],
            )
        };
        let mut m = Match::default();
        match_types(
            &listed(inner(v("n"))),
            &listed(inner(v("k"))),
            &["n".to_string()],
            &mut m,
        );
        assert_eq!(m.get("n"), Some(v("k")));
    }

    #[test]
    fn matching_two_types_of_different_shapes_claims_nothing() {
        let mut m = Match::default();
        match_types(
            &Ty::Name("int".into()),
            &Ty::App("list0".into(), vec![]),
            &["n".to_string()],
            &mut m,
        );
        assert!(m.get("n").is_none());
        assert!(m.equations.is_empty());
    }

    #[test]
    fn a_singleton_type_claims_that_the_value_is_its_index() {
        assert_eq!(
            claim_of(&int_of(app("+", v("n"), i(1)))),
            Some(app("==", SExp::Var(SELF.into()), app("+", v("n"), i(1))))
        );
    }

    #[test]
    fn a_named_refinement_claims_a_bound_rather_than_a_value() {
        // `intGte(0)` is not the type of nought — it is the type of any
        // integer that is at least nought.  Reading its index as the
        // value is how a checker convinces itself that every `intGte(0)`
        // is zero.
        let ty = |n: &str, a: SExp| Ty::Index(Box::new(Ty::Name(n.into())), vec![a]);
        let self_ = SExp::Var(SELF.into());
        assert_eq!(
            claim_of(&ty("intGte", i(0))),
            Some(app(">=", self_.clone(), i(0)))
        );
        assert_eq!(
            claim_of(&ty("intGt", v("k"))),
            Some(app(">", self_.clone(), v("k")))
        );
        assert_eq!(
            claim_of(&ty("intLt", v("k"))),
            Some(app("<", self_.clone(), v("k")))
        );
        assert_eq!(
            claim_of(&ty("sizeLte", v("k"))),
            Some(app("<=", self_.clone(), v("k")))
        );
    }

    #[test]
    fn a_nat_flavoured_refinement_is_non_negative_as_well_as_bounded() {
        // `natLt(n)` is `0 <= i < n`, and the lower half is the half
        // that makes a subscript safe.
        let ty = Ty::Index(Box::new(Ty::Name("natLt".into())), vec![v("n")]);
        let self_ = SExp::Var(SELF.into());
        assert_eq!(
            claim_of(&ty),
            Some(SExp::App(
                "&&".into(),
                vec![app(">=", self_.clone(), i(0)), app("<", self_, v("n"))]
            ))
        );
    }

    #[test]
    fn a_type_with_no_index_claims_nothing() {
        assert_eq!(claim_of(&Ty::Name("int".into())), None);
        assert_eq!(claim_of(&Ty::Name("string".into())), None);
    }

    #[test]
    fn a_measured_type_claims_nothing_about_the_value_it_measures() {
        // `string(n)` says the string is `n` long, not that it *is* `n`.
        let ty = Ty::Index(Box::new(Ty::Name("string".into())), vec![v("n")]);
        assert_eq!(claim_of(&ty), None);
    }

    #[test]
    fn a_static_argument_determines_a_variable_no_parameter_could_have() {
        // `ax{3}()` takes no value arguments at all, so unification has
        // nothing to work from.  The index in braces is the only thing
        // that says *which* instance of the axiom is being invoked, and
        // an axiom applied at the wrong index is the one mistake a proof
        // language exists to catch.
        let facts = axiom().at_call(&[i(3)], &[], &Fresh::default());
        assert!(facts.undetermined.is_empty(), "{:?}", facts.undetermined);
        assert_eq!(facts.demands, vec![app(">", i(3), i(0))]);
        assert_eq!(
            facts.assumptions,
            vec![SExp::App(
                "==".into(),
                vec![
                    SExp::App("fact".into(), vec![i(3)]),
                    app(
                        "*",
                        i(3),
                        SExp::App("fact".into(), vec![app("-", i(3), i(1))])
                    ),
                ]
            )]
        );
    }

    #[test]
    fn static_arguments_are_positional_across_every_quantifier() {
        // `f{a}{n}` supplies one term per quantifier in the order
        // written, and a type-sorted one takes its place in that order
        // without becoming an index.
        let sig = Signature {
            name: "f".into(),
            ty_params: vec![],
            universals: vec![
                Quant {
                    vars: vec![("a".into(), Sort::Type)],
                    guard: None,
                },
                Quant {
                    vars: vec![("n".into(), Sort::Nat)],
                    guard: None,
                },
            ],
            existentials: vec![],
            params: vec![],
            borrowed: Vec::new(),
            ret: int_of(v("n")),
            metric: vec![],
        };
        let facts = sig.at_call(&[v("int"), i(7)], &[], &Fresh::default());
        assert_eq!(facts.result, Some(i(7)));
    }

    #[test]
    fn a_static_argument_outranks_what_unification_would_have_guessed() {
        // The source said which instance it meant.  Nothing inferred may
        // overrule it — that is what writing it down is for.
        let facts = succ_sig().at_call(&[i(2)], &[Arg::value(i(9))], &Fresh::default());
        assert_eq!(facts.result, Some(app("+", i(2), i(1))));
    }

    #[test]
    fn fewer_static_arguments_than_quantifiers_still_bind_what_they_reach() {
        let facts = axiom().at_call(&[], &[], &Fresh::default());
        assert_eq!(facts.undetermined, vec!["n".to_string()]);
    }

    #[test]
    fn an_undetermined_variable_is_renamed_so_it_cannot_collide_with_the_callers() {
        // The callee's `n` and the caller's `n` are different variables
        // that happen to share a spelling.  If a call cannot determine
        // the callee's, leaving the name in place lets the caller's
        // facts be read as facts about it — and then a demand the
        // checker merely could not instantiate comes back *refuted*,
        // which is the one answer a checker may never give wrongly.
        let facts = succ_sig().at_call(&[], &[Arg::unknown()], &Fresh::default());
        assert_eq!(facts.demands.len(), 1);
        let goal = facts.demands[0].to_string();
        assert!(
            goal.contains('%'),
            "the callee's variable was left nameable: {goal}"
        );
        assert!(!goal.starts_with("n >="), "{goal}");
    }

    #[test]
    fn a_metric_mentioning_an_undetermined_variable_is_renamed_too() {
        // `loop (A, succ i, pred j)` determines nothing when `succ` and
        // `pred` have no indexed signature.  The metric then reads
        // `j < j` — false — and a working program is rejected.
        let sig = Signature {
            name: "loop".into(),
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("j".into(), Sort::Nat)],
                guard: None,
            }],
            existentials: vec![],
            params: vec![int_of(v("j"))],
            borrowed: Vec::new(),
            ret: Ty::Name("void".into()),
            metric: vec![v("j")],
        };
        let facts = sig.at_call(&[], &[Arg::unknown()], &Fresh::default());
        assert_ne!(
            facts.metric,
            vec![v("j")],
            "the metric names the caller's own `j`"
        );
    }

    #[test]
    fn a_type_sorted_quantifier_is_not_an_arithmetic_demand() {
        // `{a:t@ype}` binds a type, not a number.  Treating it as an
        // index would make every template call unprovable.
        let sig = Signature {
            name: "id".into(),
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("a".into(), Sort::Type)],
                guard: None,
            }],
            existentials: vec![],
            params: vec![Ty::Name("a".into())],
            borrowed: Vec::new(),
            ret: Ty::Name("a".into()),
            metric: vec![],
        };
        let facts = sig.at_call(&[], &[Arg::unknown()], &Fresh::default());
        assert!(facts.demands.is_empty());
        assert!(facts.undetermined.is_empty());
    }

    #[test]
    fn the_table_finds_a_function_by_the_name_it_is_called_by() {
        let program = Program::new(vec![Def::Fun(FunDef {
            metric: vec![],
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("n".into(), Sort::Nat)],
                guard: None,
            }],
            existentials: vec![],
            name: "fact".into(),
            params: vec![Param {
                borrowed: false,
                name: "x".into(),
                ty: int_of(v("n")),
            }],
            ret: Ty::Name("int".into()),
            body: Expr::IntLit(1),
            proof: false,
        })]);
        let table = SigTable::of(&program);
        assert_eq!(
            table.get("fact").map(|s| s.name.clone()),
            Some("fact".into())
        );
        assert!(table.get("nope").is_none());
    }

    #[test]
    fn a_nested_function_does_not_leak_into_the_global_table() {
        let nested = FunDef {
            metric: vec![],
            ty_params: vec![],
            universals: vec![],
            existentials: vec![],
            name: "aux".into(),
            params: vec![],
            ret: Ty::Name("int".into()),
            body: Expr::IntLit(0),
            proof: false,
        };
        let outer = FunDef {
            metric: vec![],
            ty_params: vec![],
            universals: vec![],
            existentials: vec![],
            name: "outer".into(),
            params: vec![],
            ret: Ty::Name("int".into()),
            body: Expr::LetFun(vec![nested], Box::new(Expr::IntLit(0))),
            proof: false,
        };
        let table = SigTable::of(&Program::new(vec![Def::Fun(outer)]));
        assert!(table.get("outer").is_some());
        assert!(table.get("aux").is_none());
    }

    #[test]
    fn a_declaration_keeps_the_quantifiers_it_was_written_with() {
        // `extern fun f {n:nat} (int n): int` promises exactly what a
        // definition would, and a call site owes it just the same.
        // Dropping the quantifier does not merely weaken the check: the
        // callee's variable is then a *free* name, so every call comes
        // back as an equation nobody can prove.
        let program = Program::new(vec![Def::Extern(ats2_domain::ast::FunDecl {
            linear: false,
            proof: false,
            name: "ext".into(),
            ty_params: vec![],
            universals: vec![Quant {
                vars: vec![("n".into(), Sort::Nat)],
                guard: None,
            }],
            existentials: vec![],
            params: vec![Param {
                borrowed: false,
                name: "x".into(),
                ty: int_of(v("n")),
            }],
            ret: Ty::Name("int".into()),
        })]);
        let sig = SigTable::of(&program)
            .get("ext")
            .expect("a signature")
            .clone();
        let facts = sig.at_call(&[], &[Arg::value(i(-1))], &Fresh::default());
        assert_eq!(facts.demands, vec![app(">=", i(-1), i(0))]);
        assert!(facts.undetermined.is_empty(), "{:?}", facts.undetermined);
    }

    #[test]
    fn a_declaration_without_a_body_is_a_signature_too() {
        // `extern fun` and prelude declarations promise as much as a
        // definition does, and a call site owes them just the same.
        let program = Program::new(vec![Def::Extern(ats2_domain::ast::FunDecl {
            linear: false,
            proof: false,
            name: "sqrt".into(),
            ty_params: vec![],
            universals: vec![],
            existentials: vec![],
            params: vec![Param {
                borrowed: false,
                name: "x".into(),
                ty: Ty::Name("int".into()),
            }],
            ret: Ty::Name("int".into()),
        })]);
        assert!(SigTable::of(&program).get("sqrt").is_some());
    }
}
