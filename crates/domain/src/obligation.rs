//! # Proof obligations — what the checker owes, as data
//!
//! *Literate note.*  A dependent type checker does not decide things as
//! it walks.  It walks once, writing down every claim the program must
//! justify, and then hands the pile to a solver.  Separating the two is
//! not tidiness: the walk knows *why* a claim exists and nothing about
//! arithmetic, the solver knows arithmetic and nothing about why, and a
//! module that knew both would be the one module nobody could change.
//!
//! So an obligation is data: what may be assumed, what must be shown,
//! and where the demand came from.  It has no opinion about whether it
//! holds — that opinion is a use case, and lives outside the domain.

use crate::statics::SExp;
use crate::tokens::Span;
use std::fmt;

/// Why a claim is being made — the half of a diagnostic that a solver
/// could never reconstruct.
///
/// Kept structured rather than as a sentence so that the wording lives
/// in exactly one place, and so a caller that wants to filter by kind
/// (report only failed calls, say) can do it without reading English.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Origin {
    /// A call must establish what the callee's universals demand.
    Call { callee: String },
    /// A body must produce what its own result type promises.
    Return { function: String },
    /// A recursive call must be smaller, by the metric written `.<n>.`.
    Metric { function: String },
    /// A subscript must lie inside the array it reaches into.
    Bound { subject: String },
    /// An annotation — `(e): int(n)` or `val x: int(n) = e` — must hold
    /// of the value annotated.
    Annotation,
    /// A `case` or `if` whose arms do not, between them, cover every
    /// index the scrutinee could take.
    Exhaustive { subject: String },
}

impl fmt::Display for Origin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Origin::Call { callee } => write!(f, "the call to `{callee}`"),
            Origin::Return { function } => write!(f, "the result of `{function}`"),
            Origin::Metric { function } => write!(f, "the recursion in `{function}`"),
            Origin::Bound { subject } => write!(f, "the subscript into `{subject}`"),
            Origin::Annotation => write!(f, "the annotation"),
            Origin::Exhaustive { subject } => write!(f, "the match on `{subject}`"),
        }
    }
}

/// One claim the program must justify: `hyps |- goal`.
///
/// The hypotheses travel *with* the goal rather than being held by the
/// checker, because a program has as many hypothesis sets as it has
/// paths, and an obligation that arrived from one path cannot be judged
/// under another's.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Obligation {
    pub hyps: Vec<SExp>,
    pub goal: SExp,
    pub origin: Origin,
    pub span: Option<Span>,
}

impl Obligation {
    pub fn new(hyps: Vec<SExp>, goal: SExp, origin: Origin) -> Self {
        Obligation { hyps, goal, origin, span: None }
    }

    /// The sentence a diagnostic prints when this obligation is not met.
    ///
    /// Written here, beside the data, so that the checker and any other
    /// reporter say the same thing about the same failure.
    pub fn describe(&self) -> String {
        format!("{} requires `{}`", self.origin, self.goal)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn goal() -> SExp {
        SExp::App(">=".into(), vec![SExp::Var("n".into()), SExp::IntLit(0)])
    }

    #[test]
    fn an_obligation_carries_the_hypotheses_it_must_be_judged_under() {
        // The same goal is provable under one path's assumptions and not
        // another's, so hypotheses belong to the obligation and not to
        // whoever is holding it at the time.
        let hyp = SExp::App(">".into(), vec![SExp::Var("n".into()), SExp::IntLit(3)]);
        let o = Obligation::new(vec![hyp.clone()], goal(), Origin::Annotation);
        assert_eq!(o.hyps, vec![hyp]);
        assert_eq!(o.goal, goal());
    }

    #[test]
    fn the_origin_says_why_rather_than_what() {
        // A solver can print the goal; only the walk knows it came from a
        // call, and a diagnostic without that is a diagnostic nobody can act on.
        let o = Obligation::new(vec![], goal(), Origin::Call { callee: "fact".into() });
        assert_eq!(o.describe(), "the call to `fact` requires `n >= 0`");
    }

    #[test]
    fn each_origin_names_itself_in_a_sentence() {
        let cases = [
            (Origin::Return { function: "f".into() }, "the result of `f`"),
            (Origin::Metric { function: "f".into() }, "the recursion in `f`"),
            (Origin::Bound { subject: "xs".into() }, "the subscript into `xs`"),
            (Origin::Annotation, "the annotation"),
            (Origin::Exhaustive { subject: "x".into() }, "the match on `x`"),
        ];
        for (origin, text) in cases {
            assert_eq!(origin.to_string(), text);
        }
    }
}
