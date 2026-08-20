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
//! * **Nonlinearity is multiplied out, then bounded, never guessed.**  A
//!   product is rewritten as a canonical sum of monomials, and the only
//!   facts added about those monomials are the ones that follow from
//!   their factors' own bounds — a nonnegative product is nonnegative, a
//!   square is nonnegative, and a product inside known bounds is bounded.
//!   Anything the rules cannot reach stays `Unknown`.
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

/// The exact integer bounds every monomial is forced into by a
/// conjunction of `>= 0` polynomials, found by reading one variable off
/// one constraint at a time.  `None` on a side means unbounded.
///
/// From `c*x + R + k >= 0`, once the rest `R` is known to be no more
/// than `U`, `x` is at least `ceil((-U - k)/c)` when `c` is positive,
/// and at most `floor((U + k)/(-c))` when it is negative.  `U` is the
/// sum of each other term's own upper estimate — an over-approximation,
/// so every bound is weaker than the true optimum, never stronger, and
/// therefore sound.  Fractions round outward, which over the integers
/// only loosens the claim further.
fn interval_bounds(system: &[Linear]) -> BTreeMap<Mono, (Option<i64>, Option<i64>)> {
    let mut monos: Vec<Mono> = Vec::new();
    for l in system {
        for m in l.terms.keys() {
            if !monos.contains(m) {
                monos.push(m.clone());
            }
        }
    }
    let mut lo: BTreeMap<Mono, Option<i64>> = monos.iter().map(|m| (m.clone(), None)).collect();
    let mut hi: BTreeMap<Mono, Option<i64>> = monos.iter().map(|m| (m.clone(), None)).collect();

    // The bounds only ever tighten, so the fixed point is reached in a
    // bounded number of rounds; the cap is a backstop, not a plan.
    for _round in 0..256 {
        let mut updates: Vec<(Mono, Option<i64>, Option<i64>)> = Vec::new();
        for l in system {
            for (var, &ci) in &l.terms {
                // `rest_hi`: the largest the rest of the constraint can
                // reach, given the current intervals.  `None` once any
                // term it needs is unbounded, or the arithmetic will not
                // fit — both mean "no bound this way".
                let mut rest_hi: i128 = 0;
                let mut finite = true;
                for (m, &c) in &l.terms {
                    if m == var {
                        continue;
                    }
                    let side = if c >= 0 {
                        hi.get(m).copied().flatten()
                    } else {
                        lo.get(m).copied().flatten()
                    };
                    let Some(v) = side else {
                        finite = false;
                        break;
                    };
                    match (c as i128).checked_mul(v as i128).and_then(|p| rest_hi.checked_add(p)) {
                        Some(s) => rest_hi = s,
                        None => {
                            finite = false;
                            break;
                        }
                    }
                }
                if !finite {
                    continue;
                }
                let konst = l.konst as i128;
                let mut new_lo = None;
                let mut new_hi = None;
                if ci > 0 {
                    let num = rest_hi.checked_neg().and_then(|n| n.checked_sub(konst));
                    if let Some(n) = num {
                        if let Some(q) = ceil_div(n, ci as i128) {
                            new_lo = i64::try_from(q).ok();
                        }
                    }
                } else if ci < 0 {
                    let c = -(ci as i128);
                    let num = rest_hi.checked_add(konst);
                    if let Some(n) = num {
                        new_hi = i64::try_from(n.div_euclid(c)).ok();
                    }
                }
                updates.push((var.clone(), new_lo, new_hi));
            }
        }
        let mut changed = false;
        for (var, new_lo, new_hi) in updates {
            if let Some(v) = new_lo {
                if lo.get(&var).copied().flatten().map_or(true, |old| v > old) {
                    lo.insert(var.clone(), Some(v));
                    changed = true;
                }
            }
            if let Some(v) = new_hi {
                if hi.get(&var).copied().flatten().map_or(true, |old| v < old) {
                    hi.insert(var.clone(), Some(v));
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    monos
        .into_iter()
        .map(|m| {
            let l = lo.get(&m).copied().flatten();
            let h = hi.get(&m).copied().flatten();
            (m, (l, h))
        })
        .collect()
}

/// `ceil(a / b)` for `b > 0`, guarded against overflow.
fn ceil_div(a: i128, b: i128) -> Option<i128> {
    debug_assert!(b > 0);
    a.checked_add(b - 1).map(|x| x.div_euclid(b))
}

/// Every atom of a monomial appearing an even number of times: the
/// monomial is a perfect square, and so nonnegative no matter what its
/// root is.
fn is_square(atoms: &[String]) -> bool {
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for a in atoms {
        *counts.entry(a.as_str()).or_insert(0) += 1;
    }
    counts.values().all(|c| c % 2 == 0)
}

/// `pc*P + ac*A + bc*B + konst >= 0`, assembled with checked arithmetic.
fn triple(p: &Mono, pc: i64, a: &Mono, ac: i64, b: &Mono, bc: i64, konst: i64) -> Option<Linear> {
    let mut terms: BTreeMap<Mono, i64> = BTreeMap::new();
    for (m, c) in [(p, pc), (a, ac), (b, bc)] {
        if c == 0 {
            continue;
        }
        let e = terms.entry(m.clone()).or_insert(0);
        *e = e.checked_add(c)?;
        if *e == 0 {
            terms.remove(m);
        }
    }
    Some(Linear { terms, konst })
}

fn push_new(out: &[Linear], fresh: &mut Vec<Linear>, l: Linear) {
    if !out.contains(&l) && !fresh.contains(&l) {
        fresh.push(l);
    }
}

/// The sound consequences of multiplication, joined to a system before
/// it is decided.
///
/// FM elimination is linear: it treats every monomial as a free
/// dimension, so `m >= 0` and `n >= 0` never become `m*n >= 0` on their
/// own.  This pass adds the bridge, and nothing but the bridge:
///
/// * every factor nonnegative makes the product nonnegative;
/// * a perfect square is nonnegative whatever its root is;
/// * a two-atom product `a*b` obeys the four McCormick envelopes that
///   its factors' bounds imply — `a*b >= la*b + lb*a - la*lb`, its three
///   siblings, and the two upper-bounding ones.
///
/// Each addition is a plain consequence of the system already there, so
/// the answer is still an honest `Proved`/`Refuted`/`Unknown`; the
/// strengthened system just knows more of what it already knew.  A few
/// rounds let a bound derived for one product feed a later one.
fn strengthen(system: &[Linear]) -> Vec<Linear> {
    const ROUNDS: usize = 3;
    let mut out = system.to_vec();
    for _ in 0..ROUNDS {
        let bounds = interval_bounds(&out);
        let snapshot: Vec<Mono> = out.iter().flat_map(|l| l.terms.keys().cloned()).collect();
        let mut fresh: Vec<Linear> = Vec::new();
        for mono in &snapshot {
            let atoms = &mono.0;
            if atoms.len() < 2 {
                continue;
            }
            let b = |name: &str| {
                bounds
                    .get(&Mono::atom(name.to_string()))
                    .copied()
                    .unwrap_or((None, None))
            };
            // Every factor nonnegative makes the product nonnegative.
            if atoms.iter().all(|a| b(a).0.is_some_and(|v| v >= 0)) {
                push_new(&out, &mut fresh, Linear::var(mono.clone()));
            }
            // A perfect square is nonnegative whatever its root is.
            if is_square(atoms) {
                push_new(&out, &mut fresh, Linear::var(mono.clone()));
            }
            // Binary McCormick envelopes.
            if atoms.len() == 2 {
                let a = Mono::atom(atoms[0].clone());
                let bb = Mono::atom(atoms[1].clone());
                let (alo, ahi) = b(&atoms[0]);
                let (blo, bhi) = b(&atoms[1]);
                let prod = |x: i64, y: i64| {
                    (x as i128).checked_mul(y as i128).and_then(|p| i64::try_from(p).ok())
                };
                if let (Some(la), Some(lb)) = (alo, blo) {
                    if let Some(k) = prod(la, lb) {
                        if let Some(l) = triple(mono, 1, &a, -lb, &bb, -la, k) {
                            push_new(&out, &mut fresh, l);
                        }
                    }
                }
                if let (Some(ha), Some(hb)) = (ahi, bhi) {
                    if let Some(k) = prod(ha, hb) {
                        if let Some(l) = triple(mono, 1, &a, -hb, &bb, -ha, k) {
                            push_new(&out, &mut fresh, l);
                        }
                    }
                }
                if let (Some(ha), Some(lb)) = (ahi, blo) {
                    if let Some(nk) = prod(ha, lb).and_then(|k| k.checked_neg()) {
                        if let Some(l) = triple(mono, -1, &a, lb, &bb, ha, nk) {
                            push_new(&out, &mut fresh, l);
                        }
                    }
                }
                if let (Some(la), Some(hb)) = (alo, bhi) {
                    if let Some(nk) = prod(la, hb).and_then(|k| k.checked_neg()) {
                        if let Some(l) = triple(mono, -1, &a, hb, &bb, la, nk) {
                            push_new(&out, &mut fresh, l);
                        }
                    }
                }
            }
        }
        if fresh.is_empty() {
            break;
        }
        out.extend(fresh);
    }
    out
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
    let mut system: Vec<Linear> = strengthen(system);
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
    fn a_product_of_nonnegative_factors_is_nonnegative() {
        // `m >= 0 && n >= 0` implies `m*n >= 0`.  Rearranging alone
        // cannot say so — the product must be given a bound of its own,
        // which is what the sign rule for products provides.
        let hyps = vec![app(">=", v("m"), i(0)), app(">=", v("n"), i(0))];
        let goal = app(">=", app("*", v("m"), v("n")), i(0));
        assert_eq!(entails(&hyps, &goal), Verdict::Proved);
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


    #[test]
    fn a_product_by_one_is_the_factor_itself() {
        // Multiplying out must fold the unit away, not turn `n*1` into a
        // monomial that looks nothing like `n`.
        let goal = app("==", app("*", v("n"), i(1)), v("n"));
        assert_eq!(entails(&[], &goal), Verdict::Proved);
    }

    #[test]
    fn a_square_is_nonnegative_even_without_hypotheses() {
        // `x*x >= 0` needs no sign of `x`: the square of an integer is
        // nonnegative by itself, and a solver that could not say so
        // would fail every lemma about magnitude.
        let hyps: Vec<SExp> = vec![];
        assert_eq!(entails(&hyps, &app(">=", app("*", v("x"), v("x")), i(0))), Verdict::Proved);
    }

    #[test]
    fn a_product_is_bounded_below_by_the_product_of_lower_bounds() {
        // `m >= 2 && n >= 3` forces `m*n >= 6`.  This is the McCormick
        // lower envelope at work: the product's bound is read off the
        // factors' bounds, which no rearrangement of the two facts alone
        // could produce.
        let hyps = vec![app(">=", v("m"), i(2)), app(">=", v("n"), i(3))];
        assert_eq!(entails(&hyps, &app(">=", app("*", v("m"), v("n")), i(6))), Verdict::Proved);
    }

    #[test]
    fn a_product_with_one_zero_bounded_factor_is_nonnegative() {
        // `m >= 2 && n >= 0` gives `m*n >= 0`: one factor pinned away
        // from zero is enough once the other is merely nonnegative.
        let hyps = vec![app(">=", v("m"), i(2)), app(">=", v("n"), i(0))];
        assert_eq!(entails(&hyps, &app(">=", app("*", v("m"), v("n")), i(0))), Verdict::Proved);
    }

    #[test]
    fn a_product_with_a_factor_at_least_one_dominates_the_other() {
        // `n >= 1 && m >= 0` gives `m*n >= m`.  A factor of at least one
        // cannot shrink the other factor, which is the shape of every
        // "scaling does not decrease" argument.
        let hyps = vec![app(">=", v("n"), i(1)), app(">=", v("m"), i(0))];
        assert_eq!(entails(&hyps, &app(">=", app("*", v("m"), v("n")), v("m"))), Verdict::Proved);
    }

    #[test]
    fn a_product_of_nonnegative_and_nonpositive_factors_is_nonpositive() {
        // `m >= 0 && n <= 0` gives `m*n <= 0`: the upper envelope reads
        // the product's ceiling off the two opposite signs.
        let hyps = vec![app(">=", v("m"), i(0)), app("<=", v("n"), i(0))];
        assert_eq!(entails(&hyps, &app("<=", app("*", v("m"), v("n")), i(0))), Verdict::Proved);
    }

    #[test]
    fn a_product_bound_the_factors_do_not_force_is_unknown_not_guessed() {
        // `m >= 2 && n >= 3` does not force `m*n >= 10` (2*3 is six) nor
        // forbid it (5*3 is fifteen).  The envelope stays inside the
        // facts; it must not invent a tighter bound than they imply.
        let hyps = vec![app(">=", v("m"), i(2)), app(">=", v("n"), i(3))];
        assert_eq!(entails(&hyps, &app(">=", app("*", v("m"), v("n")), i(10))), Verdict::Unknown);
    }
}
