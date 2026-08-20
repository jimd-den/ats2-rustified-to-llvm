//! # The constraint solver — deciding claims, and nothing else
//!
//! *Literate note.*  A dependent type is a claim, and a claim nobody
//! checks is a comment.  [`crate::checking`] is what finds the claims a
//! program makes; this module is what decides them, and it is kept
//! separate because the two change for entirely different reasons — one
//! when the *language* grows, the other when the *arithmetic* does.  The
//! solver has no idea what a function is.
//!
//! The language of claims here is linear arithmetic over the integers,
//! which is what the corpus actually indexes with: sizes, lengths,
//! bounds, and the occasional product.  Three deliberate choices keep it
//! honest:
//!
//! * **Rational refutation, integer strengthening.**  A goal is proved by
//!   showing its negation unsatisfiable, using Fourier–Motzkin
//!   elimination over the rationals.  Rational unsatisfiability implies
//!   integer unsatisfiability, so every proof is sound.  Strict
//!   inequalities are tightened first (`n > 0` becomes `n >= 1`), which
//!   recovers most of what integrality buys.
//! * **Nonlinearity is abstracted, never guessed.**  `m*n` becomes an
//!   opaque variable — the same one every time it appears — so a claim
//!   that only needs it to be itself still goes through, and one that
//!   needs to know its value does not.
//! * **Three verdicts, not two.**  Anything outside the fragment is
//!   `Unknown`, never a failure.  A checker that rejects what it merely
//!   fails to understand is a checker people turn off.

use std::collections::BTreeMap;

use ats2_domain::statics::SExp;

/// What the checker was able to establish.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// The hypotheses entail the goal.
    Proved,
    /// The hypotheses entail its *negation*: the claim is definitely false.
    Refuted,
    /// Outside the fragment, or simply undecided.  Not an error.
    Unknown,
}

/// A product of atoms, in a canonical order.
///
/// This is the thing a [`Linear`] is linear *in*.  A plain variable is a
/// monomial of one; `m*n` is a monomial of two, and so is `n*m`, because
/// the atoms are sorted.  That sorting is the whole point: abstracting a
/// product to its printed form made those two spellings unrelated
/// variables, and no one who wrote both in one file would expect that.
///
/// An atom is a static variable, or the printed form of a term the
/// solver cannot read at all — `fact(n)` and its kind.  Those are opaque
/// but stably opaque, exactly as before, and now they multiply like
/// anything else.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Mono(Vec<String>);

impl Mono {
    fn atom(name: impl Into<String>) -> Mono {
        Mono(vec![name.into()])
    }

    /// The product of two monomials, canonical again.
    fn times(&self, other: &Mono) -> Mono {
        let mut atoms = self.0.clone();
        atoms.extend(other.0.iter().cloned());
        atoms.sort();
        Mono(atoms)
    }
}

/// A polynomial `sum(coeff * monomial) + constant`, read as `>= 0`.
///
/// It is still solved as though it were linear — each distinct monomial
/// is eliminated as if it were a free variable of its own.  That is the
/// same abstraction as before, and sound for the same reason: treating
/// `m*n` as unconstrained by `m` and `n` admits *more* solutions, and a
/// system with no solutions under a relaxation had none to begin with.
/// What multiplying out adds is that terms which are equal really do
/// come out equal, which the printed form could not manage.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Linear {
    terms: BTreeMap<Mono, i64>,
    konst: i64,
}

impl Linear {
    fn constant(k: i64) -> Linear {
        Linear {
            terms: BTreeMap::new(),
            konst: k,
        }
    }

    fn var(mono: Mono) -> Linear {
        let mut terms = BTreeMap::new();
        terms.insert(mono, 1);
        Linear { terms, konst: 0 }
    }

    /// Every arithmetic result is checked, and `None` means *out of
    /// range* rather than any claim about the program.
    ///
    /// Exact integer arithmetic overflows, and it overflows soonest
    /// inside the elimination below, where coefficients multiply once
    /// per round.  Wrapping would turn a large constant into a false
    /// proof, and panicking would turn it into a compiler crash; a
    /// solver that shrugs and answers `Unknown` is the only one of the
    /// three that is both honest and usable.
    fn scale(&self, k: i64) -> Option<Linear> {
        let mut terms = BTreeMap::new();
        for (v, c) in &self.terms {
            let scaled = c.checked_mul(k)?;
            if scaled != 0 {
                terms.insert(v.clone(), scaled);
            }
        }
        Some(Linear {
            terms,
            konst: self.konst.checked_mul(k)?,
        })
    }

    fn add(&self, other: &Linear) -> Option<Linear> {
        let mut terms = self.terms.clone();
        for (v, c) in &other.terms {
            let e = terms.entry(v.clone()).or_insert(0);
            *e = e.checked_add(*c)?;
            if *e == 0 {
                terms.remove(v);
            }
        }
        Some(Linear {
            terms,
            konst: self.konst.checked_add(other.konst)?,
        })
    }

    fn sub(&self, other: &Linear) -> Option<Linear> {
        self.add(&other.scale(-1)?)
    }

    /// The product of two polynomials, multiplied out.
    ///
    /// This is what makes `(n+1)*m` and `n*m + m` the same term, which
    /// is the shape every induction over a product has.
    fn mul(&self, other: &Linear) -> Option<Linear> {
        let mut out = Linear::constant(self.konst.checked_mul(other.konst)?);
        let mut term = |mono: Mono, coeff: i64| -> Option<()> {
            if coeff != 0 {
                let e = out.terms.entry(mono.clone()).or_insert(0);
                *e = e.checked_add(coeff)?;
                if *e == 0 {
                    out.terms.remove(&mono);
                }
            }
            Some(())
        };
        for (m, c) in &self.terms {
            for (n, d) in &other.terms {
                term(m.times(n), c.checked_mul(*d)?)?;
            }
            term(m.clone(), c.checked_mul(other.konst)?)?;
        }
        for (n, d) in &other.terms {
            term(n.clone(), self.konst.checked_mul(*d)?)?;
        }
        Some(out)
    }

    /// The same constraint with the common factor divided out.
    ///
    /// `2a + 4b + 6 >= 0` says exactly what `a + 2b + 3 >= 0` says, and
    /// says it in numbers a third the size.  That matters because
    /// elimination multiplies coefficients together once per variable
    /// removed, so without this the arithmetic runs out of range on
    /// systems that are otherwise perfectly ordinary.
    ///
    /// When the factor divides the terms but not the constant, the
    /// constant is *floored* rather than left alone: over the integers
    /// `2a + 3 >= 0` is `a >= -1.5` is `a >= -1`, which is a stronger
    /// claim and a true one.  It is the same trick as reading `n > 0` as
    /// `n >= 1`, one level down.
    fn reduced(&self) -> Linear {
        let mut g = 0i64;
        for c in self.terms.values() {
            g = gcd(g, *c);
        }
        if g <= 1 {
            return self.clone();
        }
        Linear {
            terms: self.terms.iter().map(|(v, c)| (v.clone(), c / g)).collect(),
            // Floor division, which for a negative constant means
            // rounding away from zero — `div_euclid` is exactly that.
            konst: self.konst.div_euclid(g),
        }
    }

    fn coeff(&self, var: &Mono) -> i64 {
        self.terms.get(var).copied().unwrap_or(0)
    }

    /// `>= 0` with no variables left: either trivially true or false.
    fn is_false_constant(&self) -> bool {
        self.terms.is_empty() && self.konst < 0
    }
}

/// Read a static term as a linear form, abstracting what it cannot read.
///
/// `abstracted` is shared across every term in one query so that the
/// same opaque subterm gets the same variable — that consistency is the
/// whole value of the abstraction.
fn linearize(e: &SExp) -> Option<Linear> {
    match e {
        SExp::IntLit(n) => Some(Linear::constant(*n)),
        SExp::Var(n) => Some(Linear::var(Mono::atom(n.clone()))),
        SExp::BoolLit(_) => None,
        SExp::App(op, args) => match (op.as_str(), args.len()) {
            ("+", 2) => linearize(&args[0])?.add(&linearize(&args[1])?),
            ("-", 2) => linearize(&args[0])?.sub(&linearize(&args[1])?),
            ("~", 1) => linearize(&args[0])?.scale(-1),
            // Multiplied out, rather than abstracted away.  Both sides
            // are polynomials already, so the product is one too — and
            // the monomials it produces are canonical, which is what
            // makes `m*n` and `n*m` the same term and `(n+1)*m` the same
            // term as `n*m + m`.
            ("*", 2) => linearize(&args[0])?.mul(&linearize(&args[1])?),
            _ => Some(Linear::var(Mono::atom(opaque_name(e)))),
        },
    }
}

/// The name an unreadable subterm is abstracted to.
///
/// Derived from the term's own printed form, so two occurrences of
/// `m*n` abstract to one variable and `m*n` and `n*m` do not — which is
/// a loss of strength, never of soundness.
fn opaque_name(e: &SExp) -> String {
    format!("#{e}")
}

/// The greatest common divisor, on magnitudes, with `gcd(0, n) == |n|`.
fn gcd(a: i64, b: i64) -> i64 {
    let (mut a, mut b) = (a.saturating_abs(), b.saturating_abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// A conjunction of `Linear >= 0` atoms, or `None` if the proposition
/// falls outside the fragment.
fn atoms(e: &SExp) -> Option<Vec<Linear>> {
    let SExp::App(op, args) = e else { return None };
    match (op.as_str(), args.len()) {
        ("&&", 2) => {
            let mut out = atoms(&args[0])?;
            out.extend(atoms(&args[1])?);
            Some(out)
        }
        (">=", 2) => Some(vec![difference(&args[0], &args[1])?]),
        // Over the integers `a > b` is `a - b - 1 >= 0`.  Tightening
        // here is what lets the rational elimination below decide goals
        // that are only true because the variables are whole numbers.
        (">", 2) => Some(vec![
            difference(&args[0], &args[1])?.add(&Linear::constant(-1))?,
        ]),
        ("<=", 2) => Some(vec![difference(&args[1], &args[0])?]),
        ("<", 2) => Some(vec![
            difference(&args[1], &args[0])?.add(&Linear::constant(-1))?,
        ]),
        ("==", 2) | ("=", 2) => {
            let d = difference(&args[0], &args[1])?;
            Some(vec![d.scale(-1)?, d])
        }
        // `!=` and `||` are disjunctions, which a conjunctive system
        // cannot hold.  Dropping them costs strength, not soundness.
        _ => None,
    }
}

/// `a - b` as a polynomial, or `None` if either side is unreadable or
/// the arithmetic will not fit.
fn difference(a: &SExp, b: &SExp) -> Option<Linear> {
    linearize(a)?.sub(&linearize(b)?)
}

/// The negations of a proposition, as alternatives.
///
/// `¬(A ∧ B)` is `¬A ∨ ¬B`, so a conjunction negates to several
/// single-atom systems, each of which must be refuted separately.
fn negations(e: &SExp) -> Option<Vec<Linear>> {
    // `¬(L >= 0)` is `L <= -1`, i.e. `-L - 1 >= 0`.
    atoms(e)?
        .into_iter()
        .map(|l| l.scale(-1)?.add(&Linear::constant(-1)))
        .collect()
}

/// Whether a system of `>= 0` constraints has no rational solution.
///
/// Fourier–Motzkin: eliminate one variable at a time by combining every
/// lower bound with every upper bound.  The combination count can grow
/// quadratically per variable, so it is capped — an exhausted budget
/// reports "satisfiable as far as we know", which keeps the caller's
/// verdict `Unknown` rather than inventing a proof.
fn is_unsatisfiable(system: &[Linear]) -> bool {
    const BUDGET: usize = 4000;
    let mut system: Vec<Linear> = system.to_vec();
    loop {
        if system.iter().any(Linear::is_false_constant) {
            return true;
        }
        let Some(var) = system.iter().flat_map(|l| l.terms.keys()).next().cloned() else {
            return false;
        };
        let mut zero = Vec::new();
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for l in &system {
            match l.coeff(&var) {
                0 => zero.push(l.clone()),
                c if c > 0 => pos.push(l.clone()),
                _ => neg.push(l.clone()),
            }
        }
        if pos.len() * neg.len() > BUDGET {
            return false;
        }
        let mut next = zero;
        for p in &pos {
            for n in &neg {
                // Scale both so the variable cancels exactly, then
                // divide out whatever factor the two happened to share.
                // A combination whose arithmetic will not fit is simply
                // dropped: a system missing a constraint has *more*
                // solutions, so if the remainder is still unsatisfiable
                // the original certainly was.
                let a = p.coeff(&var);
                let b = -n.coeff(&var);
                let combined = p.scale(b).and_then(|p| n.scale(a).and_then(|n| p.add(&n)));
                if let Some(l) = combined {
                    next.push(l.reduced());
                }
            }
        }
        if next.len() > BUDGET {
            return false;
        }
        system = next;
    }
}

/// Every uninterpreted application a term mentions.
///
/// These are the terms `linearize` abstracts to an opaque variable: a
/// named static function such as `fact(n)`, or a product it cannot read.
fn applications(e: &SExp, out: &mut Vec<SExp>) {
    if let SExp::App(op, args) = e {
        if linearize(e)
            .is_some_and(|l| l.terms.len() == 1 && l.terms.contains_key(&Mono::atom(opaque_name(e))))
            && !out.contains(e)
        {
            out.push(e.clone());
        }
        let _ = op;
        args.iter().for_each(|a| applications(a, out));
    }
}

/// The one thing every function satisfies, whatever else it does: equal
/// arguments, equal results.
///
/// `stacst fact: int -> int` gives the solver a function it knows nothing
/// about, and abstraction alone makes `fact(n)` and `fact(0)` two
/// unrelated variables — so `n == 0` and `fact(0) == 1` would say nothing
/// about `fact(n)`, and an inductive proof would discharge its step and
/// fail on its base.
///
/// So: whenever two applications share a head and their arguments are
/// *provably* equal under the hypotheses, the equation between them
/// joins the system.  The proof of equality uses the arithmetic already
/// there, which is what lets `fact(n-1)` meet `fact(2)` when `n` is
/// three.  It is done once rather than to a fixpoint: a second round
/// buys nothing the corpus asks for, and an unbounded one is a way to
/// spend an afternoon inside a compiler.
fn congruences(hyps: &[SExp], goal: Option<&SExp>, base: &[Linear]) -> Vec<Linear> {
    let mut terms = Vec::new();
    for h in hyps {
        applications(h, &mut terms);
    }
    if let Some(g) = goal {
        applications(g, &mut terms);
    }
    let proves = |claim: &Linear| {
        // `claim >= 0` is entailed when denying it is impossible.
        let mut sys = base.to_vec();
        let Some(denial) = claim.scale(-1).and_then(|c| c.add(&Linear::constant(-1))) else {
            // Out of range, so nothing was shown.
            return false;
        };
        sys.push(denial);
        is_unsatisfiable(&sys)
    };
    let mut out = Vec::new();
    for (i, a) in terms.iter().enumerate() {
        for b in terms.iter().skip(i + 1) {
            let (SExp::App(fa, xs), SExp::App(fb, ys)) = (a, b) else {
                continue;
            };
            if fa != fb || xs.len() != ys.len() {
                continue;
            }
            let agree = xs
                .iter()
                .zip(ys)
                .all(|(x, y)| match difference(x, y) {
                    Some(d) => {
                        d.scale(-1).is_some_and(|m| proves(&d) && proves(&m))
                    }
                    None => false,
                });
            if agree {
                let d = Linear::var(Mono::atom(opaque_name(a)))
                    .sub(&Linear::var(Mono::atom(opaque_name(b))));
                if let Some(d) = d {
                    if let Some(m) = d.scale(-1) {
                        out.push(d);
                        out.push(m);
                    }
                }
            }
        }
    }
    out
}

/// The alternative readings a hypothesis has, when it has more than one.
///
/// `a != b` is `a < b` or `a > b`: a disjunction, which a conjunctive
/// system cannot hold.  Dropping it is sound but costs the fact that
/// makes every `if i = 0 then ... else f(i-1)` legal — in the else
/// branch, `i >= 0` and `i != 0` together say `i >= 1`, and without the
/// second the recursion is unprovable.
///
/// So it is kept, as cases.  A system with `k` such hypotheses is `2^k`
/// systems, which is why the number taken is capped: past the cap the
/// remainder is simply dropped, exactly as before, and the answer is
/// weaker rather than wrong.
fn alternatives(e: &SExp) -> Option<Vec<Vec<Linear>>> {
    let SExp::App(op, args) = e else { return None };
    match (op.as_str(), args.len()) {
        ("!=", 2) => {
            let lt = atoms(&SExp::App("<".into(), args.clone()))?;
            let gt = atoms(&SExp::App(">".into(), args.clone()))?;
            Some(vec![lt, gt])
        }
        ("||", 2) => Some(vec![atoms(&args[0])?, atoms(&args[1])?]),
        _ => None,
    }
}

/// Split the hypotheses into what every case shares and the cases
/// themselves.
///
/// Returns one system per combination; a claim holds only if it holds in
/// all of them.
fn case_systems(hyps: &[SExp]) -> Vec<Vec<Linear>> {
    /// Past this many split hypotheses the combinations stop being worth
    /// their time; the rest are dropped, which weakens the answer and
    /// cannot falsify it.
    const MAX_SPLITS: usize = 4;
    let mut shared = Vec::new();
    let mut splits: Vec<Vec<Vec<Linear>>> = Vec::new();
    for h in hyps {
        if let Some(a) = atoms(h) {
            shared.extend(a);
        } else if let Some(cases) = alternatives(h) {
            if splits.len() < MAX_SPLITS {
                splits.push(cases);
            }
        }
    }
    let mut systems = vec![shared];
    for cases in splits {
        systems = systems
            .iter()
            .flat_map(|base| {
                cases.iter().map(|case| {
                    let mut next = base.clone();
                    next.extend(case.iter().cloned());
                    next
                })
            })
            .collect();
    }
    systems
}

/// Whether the hypotheses are jointly impossible.
///
/// Worth asking on its own: a branch whose hypotheses contradict is a
/// branch that cannot run, and reporting that is more useful than
/// silently proving every claim inside it.
pub fn is_contradictory(hyps: &[SExp]) -> bool {
    // Impossible in every case is impossible.
    case_systems(hyps).iter().all(|s| is_unsatisfiable(s))
}

/// Does `hyps` entail `goal`?
pub fn entails(hyps: &[SExp], goal: &SExp) -> Verdict {
    // A disjunction cannot be held as a conjunctive system, but it can be
    // *decided* by cases: it holds if either half does, and it is false
    // only if both are.  Splitting here rather than in `atoms` is what
    // keeps the system a conjunction while still deciding the goals a
    // lexicographic termination metric produces, which are disjunctions
    // by their nature.
    if let SExp::App(op, args) = goal {
        if op == "||" && args.len() == 2 {
            let (left, right) = (entails(hyps, &args[0]), entails(hyps, &args[1]));
            return match (left, right) {
                (Verdict::Proved, _) | (_, Verdict::Proved) => Verdict::Proved,
                (Verdict::Refuted, Verdict::Refuted) => Verdict::Refuted,
                _ => Verdict::Unknown,
            };
        }
    }
    let Some(goal_atoms) = atoms(goal) else {
        return Verdict::Unknown;
    };
    let Some(negated) = negations(goal) else {
        return Verdict::Unknown;
    };

    // One system per case the hypotheses leave open.  A claim holds only
    // if it holds in all of them, and is false only if it fails in all.
    let systems: Vec<Vec<Linear>> = case_systems(hyps)
        .into_iter()
        .map(|mut base| {
            // What the hypotheses say about the *functions* they
            // mention, which abstraction alone throws away.
            let extra = congruences(hyps, Some(goal), &base);
            base.extend(extra);
            base
        })
        .collect();

    // Proved when, in every case, every way of denying the goal is
    // impossible.
    let proved = systems.iter().all(|base| {
        negated.iter().all(|n| {
            let mut sys = base.clone();
            sys.push(n.clone());
            is_unsatisfiable(&sys)
        })
    });
    if proved {
        return Verdict::Proved;
    }
    // Refuted when asserting the goal is impossible in every case.
    let refuted = systems.iter().all(|base| {
        let mut with_goal = base.clone();
        with_goal.extend(goal_atoms.iter().cloned());
        is_unsatisfiable(&with_goal)
    });
    if refuted {
        return Verdict::Refuted;
    }
    Verdict::Unknown
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(n: &str) -> SExp {
        SExp::Var(n.into())
    }
    fn i(n: i64) -> SExp {
        SExp::IntLit(n)
    }
    fn app(op: &str, a: SExp, b: SExp) -> SExp {
        SExp::App(op.into(), vec![a, b])
    }

    #[test]
    fn a_goal_that_follows_from_the_hypotheses_is_proved() {
        // n >= 0  ⊢  n + 1 > 0
        let hyps = vec![app(">=", v("n"), i(0))];
        let goal = app(">", app("+", v("n"), i(1)), i(0));
        assert_eq!(entails(&hyps, &goal), Verdict::Proved);
    }

    #[test]
    fn a_goal_the_hypotheses_contradict_is_refuted() {
        // n > 0  ⊢  n - 1 < 0   is false for every n
        let hyps = vec![app(">", v("n"), i(0))];
        let goal = app("<", app("-", v("n"), i(1)), i(0));
        assert_eq!(entails(&hyps, &goal), Verdict::Refuted);
    }

    #[test]
    fn integrality_is_used_not_just_rational_bounds() {
        // n > 0 means n >= 1 over the integers, so n >= 1 follows.
        let hyps = vec![app(">", v("n"), i(0))];
        assert_eq!(entails(&hyps, &app(">=", v("n"), i(1))), Verdict::Proved);
    }

    #[test]
    fn an_undecided_goal_is_reported_as_unknown_rather_than_guessed() {
        let hyps = vec![app(">=", v("n"), i(0))];
        assert_eq!(entails(&hyps, &app(">", v("n"), i(3))), Verdict::Unknown);
    }

    #[test]
    fn a_conjunction_is_proved_only_when_both_halves_are() {
        let hyps = vec![app(">", v("n"), i(2))];
        let both = app("&&", app(">", v("n"), i(0)), app(">", v("n"), i(1)));
        assert_eq!(entails(&hyps, &both), Verdict::Proved);
        let mixed = app("&&", app(">", v("n"), i(0)), app(">", v("n"), i(9)));
        assert_eq!(entails(&hyps, &mixed), Verdict::Unknown);
    }

    #[test]
    fn an_uninterpreted_function_agrees_with_itself_on_equal_arguments() {
        // `stacst fact: int -> int` gives the solver a function it knows
        // nothing about — except the one thing every function satisfies:
        // equal arguments, equal results.  Without it, `fact(0) == 1`
        // and `n == 0` say nothing about `fact(n)`, and an inductive
        // proof discharges its step and fails on its base.
        let hyps = vec![
            app("==", SExp::App("fact".into(), vec![i(0)]), i(1)),
            app("==", v("n"), i(0)),
        ];
        let goal = app("==", i(1), SExp::App("fact".into(), vec![v("n")]));
        assert_eq!(entails(&hyps, &goal), Verdict::Proved);
    }

    #[test]
    fn an_uninterpreted_function_says_nothing_when_the_arguments_may_differ() {
        // Congruence is not a licence to identify everything: `fact(n)`
        // and `fact(0)` agree only when `n` is nought.
        let hyps = vec![app("==", SExp::App("fact".into(), vec![i(0)]), i(1))];
        let goal = app("==", i(1), SExp::App("fact".into(), vec![v("n")]));
        assert_ne!(entails(&hyps, &goal), Verdict::Proved);
    }

    #[test]
    fn congruence_reaches_arguments_that_are_equal_only_by_arithmetic() {
        // `fact(n-1)` and `fact(2)` are the same term when `n` is three,
        // and nothing in the source ever writes that equality down.
        let hyps = vec![
            app("==", v("n"), i(3)),
            app(
                "==",
                SExp::App("f".into(), vec![app("-", v("n"), i(1))]),
                i(7),
            ),
        ];
        let goal = app("==", SExp::App("f".into(), vec![i(2)]), i(7));
        assert_eq!(entails(&hyps, &goal), Verdict::Proved);
    }

    #[test]
    fn congruence_holds_for_functions_of_several_arguments() {
        let hyps = vec![
            app("==", v("a"), v("b")),
            app("==", SExp::App("g".into(), vec![v("a"), i(1)]), i(5)),
        ];
        let goal = app("==", SExp::App("g".into(), vec![v("b"), i(1)]), i(5));
        assert_eq!(entails(&hyps, &goal), Verdict::Proved);
    }

    #[test]
    fn a_hypothesis_of_inequality_is_split_rather_than_discarded() {
        // `i >= 0` and `i != 0` say `i >= 1`, which is what makes the
        // recursive call in every `if i = 0 then ... else f(i-1)` legal.
        // `!=` is a disjunction, so a conjunctive system cannot hold it —
        // but it can be *decided* by taking each side in turn.
        let hyps = vec![app(">=", v("i"), i(0)), app("!=", v("i"), i(0))];
        assert_eq!(
            entails(&hyps, &app(">=", app("-", v("i"), i(1)), i(0))),
            Verdict::Proved
        );
    }

    #[test]
    fn splitting_a_hypothesis_does_not_prove_what_only_one_side_gives() {
        // `i != 0` alone leaves `i` free to be negative.
        let hyps = vec![app("!=", v("i"), i(0))];
        assert_ne!(entails(&hyps, &app(">=", v("i"), i(1))), Verdict::Proved);
    }

    #[test]
    fn a_branch_whose_two_sides_are_both_impossible_is_unreachable() {
        let hyps = vec![app("==", v("i"), i(0)), app("!=", v("i"), i(0))];
        assert!(is_contradictory(&hyps));
    }

    #[test]
    fn a_nonlinear_term_is_abstracted_rather_than_misread() {
        // m*n is opaque, but it is *consistently* opaque, so a goal that
        // only needs it to equal itself still goes through.
        let hyps = vec![app(">=", app("*", v("m"), v("n")), i(0))];
        let goal = app(">=", app("+", app("*", v("m"), v("n")), i(1)), i(0));
        assert_eq!(entails(&hyps, &goal), Verdict::Proved);
    }

    #[test]
    fn a_product_is_the_same_product_written_backwards() {
        // Abstracting on the printed form made `m*n` and `n*m` two
        // unrelated variables, which is a loss of strength nobody
        // writing the two spellings in one file would expect.
        let hyps = vec![app("==", app("*", v("m"), v("n")), i(6))];
        let goal = app("==", app("*", v("n"), v("m")), i(6));
        assert_eq!(entails(&hyps, &goal), Verdict::Proved);
    }

    #[test]
    fn a_product_over_a_sum_is_the_sum_of_the_products() {
        // `(n+1)*m == n*m + m` is true of every integer pair and needs
        // no arithmetic beyond multiplying out.  It is also the exact
        // shape of an inductive step over a product, which is why it is
        // worth having: `fact(n+1) == (n+1)*fact(n)` is unprovable
        // without it.
        let lhs = app("*", app("+", v("n"), i(1)), v("m"));
        let rhs = app("+", app("*", v("n"), v("m")), v("m"));
        assert_eq!(entails(&[], &app("==", lhs, rhs)), Verdict::Proved);
    }

    #[test]
    fn a_product_of_three_does_not_care_how_it_was_bracketed() {
        let left = app("*", app("*", v("a"), v("b")), v("c"));
        let right = app("*", v("a"), app("*", v("b"), v("c")));
        assert_eq!(entails(&[], &app("==", left, right)), Verdict::Proved);
    }

    #[test]
    fn a_square_is_not_confused_with_its_root() {
        // Multiplying out must not quietly make `n*n` into `n`: the
        // whole value of the normal form is that distinct monomials
        // stay distinct.
        let goal = app("==", app("*", v("n"), v("n")), v("n"));
        assert_ne!(entails(&[], &goal), Verdict::Proved);
    }

    #[test]
    fn what_multiplying_out_cannot_reach_is_still_unknown() {
        // `m >= 0 && n >= 0` implies `m*n >= 0`, and no amount of
        // rearranging says so — it needs the sign rule for products,
        // which this solver does not have.  Unknown, never Refuted: a
        // solver that called this false would be lying.
        let hyps = vec![app(">=", v("m"), i(0)), app(">=", v("n"), i(0))];
        let goal = app(">=", app("*", v("m"), v("n")), i(0));
        assert_eq!(entails(&hyps, &goal), Verdict::Unknown);
    }

    #[test]
    fn a_product_too_big_to_hold_is_unknown_rather_than_a_panic() {
        // Multiplying out is exact arithmetic on `i64`, and exact
        // arithmetic overflows.  A compiler that panics on a large
        // literal is worse than one that shrugs at it.
        let big = i(i64::MAX / 2);
        let goal = app(">=", app("*", big.clone(), app("*", big.clone(), v("n"))), i(0));
        assert_eq!(entails(&[], &goal), Verdict::Unknown);
    }

    #[test]
    fn a_disjunction_is_proved_when_either_half_is() {
        // A lexicographic metric decreases when the first component
        // does, *or* when it stays equal and the second does.  That is a
        // disjunction, and a solver that could only hold conjunctions
        // would report every lexicographic recursion as unproved.
        let hyps = vec![app(">", v("n"), i(5))];
        let goal = SExp::App(
            "||".into(),
            vec![app("<", v("n"), i(0)), app(">", v("n"), i(3))],
        );
        assert_eq!(entails(&hyps, &goal), Verdict::Proved);
    }

    #[test]
    fn a_disjunction_neither_half_of_which_holds_is_not_proved() {
        let hyps = vec![app("==", v("n"), i(4))];
        let goal = SExp::App(
            "||".into(),
            vec![app("<", v("n"), i(0)), app(">", v("n"), i(9))],
        );
        assert_ne!(entails(&hyps, &goal), Verdict::Proved);
    }

    #[test]
    fn a_disjunction_both_halves_of_which_are_impossible_is_refuted() {
        let hyps = vec![app("==", v("n"), i(4))];
        let goal = SExp::App(
            "||".into(),
            vec![app("<", v("n"), i(0)), app(">", v("n"), i(9))],
        );
        // `n` is four, so neither disjunct can hold: the claim is false,
        // not merely unproved.
        assert_eq!(entails(&hyps, &goal), Verdict::Refuted);
    }

    #[test]
    fn a_form_outside_the_fragment_is_unknown_not_an_error() {
        let hyps = vec![];
        assert_eq!(entails(&hyps, &app("!=", v("n"), i(0))), Verdict::Unknown);
    }
}
