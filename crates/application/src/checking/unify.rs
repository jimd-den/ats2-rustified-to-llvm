//! # Matching a signature's indices against a call's
//!
//! *Literate note.*  A call site does two things at once, and confusing
//! them is how dependent checkers become unusable.  It *determines* the
//! callee's static variables — `fact {n:nat} (x: int n)` called on an
//! `int 5` fixes `n` to `5` — and it *owes* whatever the signature then
//! demands.  Determination is unification; the debt is a proposition.
//!
//! Both fall out of one walk, so both come back from it.  What cannot be
//! determined is not silently dropped: `int (m*n)` handed an `int 12`
//! determines nothing, but the call is still only correct when the
//! product is twelve, and that survives here as an equation for the
//! solver rather than as a hole in the reasoning.
//!
//! Inversion is deliberately shallow — offsets, and nothing more. ATS's
//! own elaborator is not much bolder, and every step past `n+1` trades a
//! rule you can predict for one you cannot.

use ats2_domain::statics::SExp;

/// What matching a signature against a call site produced.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Match {
    bindings: Vec<(String, SExp)>,
    /// Equalities the call must justify: what matching could not settle
    /// by binding a variable.
    pub equations: Vec<SExp>,
}

impl Match {
    /// The term a static variable was determined to be.
    pub fn get(&self, name: &str) -> Option<SExp> {
        self.bindings.iter().find(|(k, _)| k == name).map(|(_, v)| v.clone())
    }

    /// The bindings, in the shape [`SExp::substitute`] takes.
    pub fn subst(&self) -> Vec<(String, SExp)> {
        self.bindings.clone()
    }

    /// Determine `name` to be `value`, or — if it is already determined —
    /// record that the two must agree.
    fn bind(&mut self, name: &str, value: SExp) {
        match self.get(name) {
            Some(existing) if existing == value => {}
            Some(existing) => self.equate(existing, value),
            None => self.bindings.push((name.to_string(), value)),
        }
    }

    fn equate(&mut self, a: SExp, b: SExp) {
        let eq = SExp::App("==".into(), vec![a, b]);
        if !self.equations.contains(&eq) {
            self.equations.push(eq);
        }
    }

    /// Match one declared index term against the one actually supplied.
    ///
    /// `vars` is the callee's own static variables — the only names this
    /// is allowed to determine.  Everything else belongs to the caller's
    /// scope and may only be compared.
    pub fn against(&mut self, pattern: &SExp, actual: &SExp, vars: &[String]) {
        // The variable case comes first, even when the two sides are
        // already identical.  `f {n:nat} (x: int n)` called with an
        // `int n` from the caller's own scope determines `n` to be that
        // term — trivially, but really.  Returning early there would
        // leave it *undetermined*, and an undetermined variable is
        // renamed away from the caller's scope, which is precisely the
        // relationship the call had just established.
        if let SExp::Var(n) = pattern {
            if vars.iter().any(|v| v == n) {
                self.bind(n, actual.clone());
                return;
            }
        }
        if pattern == actual {
            return;
        }
        match pattern {
            SExp::App(op, args) if args.len() == 2 && self.invert(op, args, actual, vars) => {}
            SExp::App(op, args) => {
                // Same shape on both sides: match componentwise, which is
                // what settles `int (n+m)` against `int (3+4)`.
                if let SExp::App(aop, aargs) = actual {
                    if aop == op && aargs.len() == args.len() {
                        for (p, a) in args.iter().zip(aargs) {
                            self.against(p, a, vars);
                        }
                        return;
                    }
                }
                self.equate(pattern.clone(), actual.clone());
            }
            _ => self.equate(pattern.clone(), actual.clone()),
        }
    }

    /// `n + k` against `a` determines `n` as `a - k`, and the three other
    /// arrangements likewise.  Reports whether it applied.
    ///
    /// Only one side may mention the variables being determined — with
    /// both sides open there is nothing to solve for, and guessing which
    /// to invert is how a checker starts disagreeing with itself.
    fn invert(&mut self, op: &str, args: &[SExp], actual: &SExp, vars: &[String]) -> bool {
        let open = |e: &SExp| e.vars().iter().any(|v| vars.contains(v));
        let (left, right) = (&args[0], &args[1]);
        let (unknown, known, rebuilt) = match (op, open(left), open(right)) {
            ("+", true, false) => (left, right, SExp::App("-".into(), vec![actual.clone(), right.clone()])),
            ("+", false, true) => (right, left, SExp::App("-".into(), vec![actual.clone(), left.clone()])),
            ("-", true, false) => (left, right, SExp::App("+".into(), vec![actual.clone(), right.clone()])),
            // `k - n = a` gives `n = k - a`.
            ("-", false, true) => (right, left, SExp::App("-".into(), vec![left.clone(), actual.clone()])),
            _ => return false,
        };
        let _ = known;
        self.against(unknown, &rebuilt, vars);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(n: &str) -> SExp { SExp::Var(n.into()) }
    fn i(n: i64) -> SExp { SExp::IntLit(n) }
    fn app(op: &str, a: SExp, b: SExp) -> SExp { SExp::App(op.into(), vec![a, b]) }

    fn unify(pattern: SExp, actual: SExp, vars: &[&str]) -> Match {
        let names: Vec<String> = vars.iter().map(|s| s.to_string()).collect();
        let mut m = Match::default();
        m.against(&pattern, &actual, &names);
        m
    }

    #[test]
    fn a_bare_variable_takes_the_argument_it_is_handed() {
        let m = unify(v("n"), i(5), &["n"]);
        assert_eq!(m.get("n"), Some(i(5)));
        assert!(m.equations.is_empty(), "nothing needed proving");
    }

    #[test]
    fn a_variable_matched_against_itself_is_still_determined() {
        // `f {n:nat} (x: int n)` called with an `int n` from the
        // caller's scope determines `n` — trivially, but really.  Calling
        // it undetermined would rename it away from the very term the
        // call had just tied it to.
        let m = unify(v("n"), v("n"), &["n"]);
        assert_eq!(m.get("n"), Some(v("n")));
    }

    #[test]
    fn a_variable_that_is_not_the_callees_is_matched_not_bound() {
        // `k` belongs to the caller.  Binding it would let a call rewrite
        // the scope it was written in.
        let m = unify(v("k"), i(5), &["n"]);
        assert_eq!(m.get("k"), None);
        assert_eq!(m.equations, vec![app("==", v("k"), i(5))]);
    }

    #[test]
    fn a_variable_bound_twice_must_be_handed_the_same_index_twice() {
        // `f {n:int} (x: int n, y: int n)` is a promise that the two
        // arguments agree, and the call site is what owes that proof.
        let mut m = Match::default();
        let names = vec!["n".to_string()];
        m.against(&v("n"), &v("a"), &names);
        m.against(&v("n"), &v("b"), &names);
        assert_eq!(m.get("n"), Some(v("a")));
        assert_eq!(m.equations, vec![app("==", v("a"), v("b"))]);
    }

    #[test]
    fn an_offset_pattern_is_inverted_rather_than_abandoned() {
        // `(x: int (n+1))` handed an `int 7` says `n` is 6.  Refusing to
        // invert here is what makes a checker useless on `cons`-shaped
        // signatures, where every index is written as an offset.
        let m = unify(app("+", v("n"), i(1)), i(7), &["n"]);
        assert_eq!(m.get("n"), Some(app("-", i(7), i(1))));
    }

    #[test]
    fn a_subtraction_inverts_on_either_side() {
        assert_eq!(unify(app("-", v("n"), i(2)), v("k"), &["n"]).get("n"), Some(app("+", v("k"), i(2))));
        assert_eq!(unify(app("-", i(10), v("n")), v("k"), &["n"]).get("n"), Some(app("-", i(10), v("k"))));
    }

    #[test]
    fn a_pattern_that_cannot_be_inverted_becomes_an_equation_to_prove() {
        // `int (m*n)` against `int 12` does not determine m or n, but the
        // call is still only correct if the product *is* 12 — so the
        // demand survives as something to prove rather than vanishing.
        let m = unify(app("*", v("m"), v("n")), i(12), &["m", "n"]);
        assert_eq!(m.get("m"), None);
        assert_eq!(m.equations, vec![app("==", app("*", v("m"), v("n")), i(12))]);
    }

    #[test]
    fn matching_descends_into_matching_shapes() {
        let m = unify(app("+", v("n"), v("m")), app("+", i(3), i(4)), &["n", "m"]);
        assert_eq!(m.get("n"), Some(i(3)));
        assert_eq!(m.get("m"), Some(i(4)));
    }

    #[test]
    fn the_substitution_is_offered_in_the_shape_sexp_wants() {
        let m = unify(v("n"), i(5), &["n"]);
        assert_eq!(v("n").substitute(&m.subst()), i(5));
    }
}
