//! # The static language
//!
//! *Literate note.*  ATS2 is two languages sharing one file.  The
//! *dynamic* language is the one that runs; the *static* language is the
//! one that reasons about what the dynamic language will do.  `int(n)`
//! is not "an int" — it is the type of the single integer whose value is
//! the static term `n`, and `{n:nat} (x: int n): int(n+1)` is a promise,
//! checked before the program runs, that the result is one more than the
//! argument.
//!
//! Everything here is erased before emission: no static term occupies
//! storage and no proof is ever evaluated.  That is *why* it needs its
//! own representation rather than being folded into `Ty` — the shapes it
//! takes (sorts, quantifiers, arithmetic over indices) have nothing to
//! do with the shapes a runtime value takes, and a checker that has to
//! recover them from an erased type is a checker that cannot be written.
//!
//! This module is data only.  Deciding whether a constraint *holds* is a
//! use case, and lives outside the domain.

use std::fmt;

/// The sort of a static variable — the static language's own "type".
///
/// `nat` and `pos` are not separate sorts in ATS: they are `int`
/// restricted by a predicate.  They are kept apart here so the
/// restriction survives to the checker, which recovers it with
/// [`Sort::refinement`]; collapsing them at parse time would throw away
/// exactly the fact that makes `nat` worth writing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sort {
    Int,
    Nat,
    Pos,
    Bool,
    Addr,
    /// `t@ype`, `type`, `viewtype`, `prop`, `view` — the sorts whose
    /// inhabitants are types rather than numbers.  A quantifier over one
    /// of these binds a *type* parameter, which is the template
    /// mechanism, not the index mechanism.
    Type,
    /// A sort this compiler does not model.  Kept by name so a
    /// diagnostic can say which one, rather than pretending it was `int`.
    Named(String),
}

impl Sort {
    /// The sort as written in a signature.
    pub fn from_name(name: &str) -> Sort {
        match name {
            "int" => Sort::Int,
            "nat" => Sort::Nat,
            "pos" => Sort::Pos,
            "bool" => Sort::Bool,
            "addr" => Sort::Addr,
            "t@ype" | "type" | "t0ype" | "vt@ype" | "vtype" | "viewtype" | "prop" | "view"
            | "tkind" => Sort::Type,
            other => Sort::Named(other.to_string()),
        }
    }

    /// Whether a variable of this sort ranges over integers, and so can
    /// appear in the arithmetic the constraint checker understands.
    pub fn is_arithmetic(&self) -> bool {
        matches!(self, Sort::Int | Sort::Nat | Sort::Pos)
    }

    /// The constraint the sort itself imposes on a variable of it.
    ///
    /// This is what makes `{n:nat}` mean more than `{n:int}`: the
    /// non-negativity is a hypothesis the body may rely on, and an
    /// obligation a caller must discharge.
    pub fn refinement(&self, var: &str) -> Option<SExp> {
        let v = SExp::Var(var.to_string());
        match self {
            Sort::Nat => Some(SExp::App(">=".into(), vec![v, SExp::IntLit(0)])),
            Sort::Pos => Some(SExp::App(">".into(), vec![v, SExp::IntLit(0)])),
            _ => None,
        }
    }
}

/// A static term: an index, or a proposition about indices.
///
/// Propositions are terms because in ATS they are — the sort `bool` is a
/// sort like any other, and `{n:int | n > 0}` is a term of it.  Keeping
/// one datatype avoids a second, near-identical one for formulas.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SExp {
    Var(String),
    IntLit(i64),
    BoolLit(bool),
    /// An operator or a static function, applied.  Arithmetic (`+`,
    /// `-`, `*`, `/`), comparison (`<`, `<=`, `>`, `>=`, `==`, `!=`),
    /// connectives (`&&`, `||`, `~`) and named static functions such as
    /// `max` all take this shape, because to the checker they differ
    /// only in which ones it knows how to interpret.
    App(String, Vec<SExp>),
}

impl SExp {
    /// Every variable the term mentions, in order of first appearance.
    pub fn vars(&self) -> Vec<String> {
        let mut out = Vec::new();
        self.collect_vars(&mut out);
        out
    }

    fn collect_vars(&self, out: &mut Vec<String>) {
        match self {
            SExp::Var(n) => {
                if !out.contains(n) {
                    out.push(n.clone());
                }
            }
            SExp::IntLit(_) | SExp::BoolLit(_) => {}
            SExp::App(_, args) => args.iter().for_each(|a| a.collect_vars(out)),
        }
    }

    /// Replace variables by terms — what a call site does when it
    /// instantiates a quantifier.
    pub fn substitute(&self, subst: &[(String, SExp)]) -> SExp {
        match self {
            SExp::Var(n) => subst
                .iter()
                .find(|(k, _)| k == n)
                .map(|(_, v)| v.clone())
                .unwrap_or_else(|| self.clone()),
            SExp::IntLit(_) | SExp::BoolLit(_) => self.clone(),
            SExp::App(f, args) => SExp::App(
                f.clone(),
                args.iter().map(|a| a.substitute(subst)).collect(),
            ),
        }
    }
}

impl fmt::Display for SExp {
    /// Static terms appear in diagnostics, and a diagnostic that prints
    /// `App(">", [Var("n"), IntLit(0)])` is a diagnostic nobody reads.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SExp::Var(n) => write!(f, "{n}"),
            SExp::IntLit(n) => write!(f, "{n}"),
            SExp::BoolLit(b) => write!(f, "{b}"),
            SExp::App(op, args)
                if args.len() == 2 && !op.chars().next().is_some_and(char::is_alphabetic) =>
            {
                write!(f, "{} {op} {}", args[0], args[1])
            }
            SExp::App(op, args)
                if args.len() == 1 && !op.chars().next().is_some_and(char::is_alphabetic) =>
            {
                write!(f, "{op}{}", args[0])
            }
            SExp::App(op, args) => {
                let parts: Vec<String> = args.iter().map(|a| a.to_string()).collect();
                write!(f, "{op}({})", parts.join(", "))
            }
        }
    }
}

/// `{n:nat | n > 0}` — variables bound, with a hypothesis about them.
///
/// A *universal* quantifier on a function's signature states what the
/// caller must establish; an *existential* on its result states what the
/// caller may then assume.  Both take this shape, which is why the
/// direction is not recorded here but at the place the quantifier is
/// attached.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Quant {
    pub vars: Vec<(String, Sort)>,
    pub guard: Option<SExp>,
}

impl Quant {
    /// Everything a body may assume, given this quantifier: the guard,
    /// plus whatever the sorts themselves promise.
    pub fn hypotheses(&self) -> Vec<SExp> {
        let mut out: Vec<SExp> = self
            .vars
            .iter()
            .filter_map(|(n, s)| s.refinement(n))
            .collect();
        out.extend(self.guard.clone());
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nat_and_pos_are_int_with_a_predicate() {
        assert_eq!(
            Sort::from_name("nat").refinement("n"),
            Some(SExp::App(
                ">=".into(),
                vec![SExp::Var("n".into()), SExp::IntLit(0)]
            ))
        );
        assert_eq!(
            Sort::from_name("pos").refinement("n"),
            Some(SExp::App(
                ">".into(),
                vec![SExp::Var("n".into()), SExp::IntLit(0)]
            ))
        );
        assert_eq!(Sort::from_name("int").refinement("n"), None);
        assert!(Sort::from_name("nat").is_arithmetic());
        assert!(!Sort::from_name("t@ype").is_arithmetic());
    }

    #[test]
    fn a_quantifier_offers_its_sorts_predicates_as_hypotheses() {
        let q = Quant {
            vars: vec![("m".into(), Sort::Nat), ("n".into(), Sort::Int)],
            guard: Some(SExp::App(
                ">".into(),
                vec![SExp::Var("m".into()), SExp::Var("n".into())],
            )),
        };
        let h = q.hypotheses();
        assert_eq!(h.len(), 2); // `m >= 0` from the sort, and the guard
        assert_eq!(h[1].to_string(), "m > n");
    }

    #[test]
    fn substitution_replaces_the_variables_a_call_site_instantiates() {
        let t = SExp::App("+".into(), vec![SExp::Var("n".into()), SExp::IntLit(1)]);
        assert_eq!(t.vars(), vec!["n".to_string()]);
        let s = t.substitute(&[("n".into(), SExp::IntLit(4))]);
        assert_eq!(s.to_string(), "4 + 1");
    }
}
