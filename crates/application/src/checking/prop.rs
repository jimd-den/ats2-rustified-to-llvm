//! # The propositional reading of an operator
//!
//! *Literate note.*  `if x > 0 then a else b` tells the checker two
//! things, and they are the two halves of every branch it will ever see:
//! inside `a`, `x > 0` holds; inside `b`, it does not.  This module owns
//! both halves — which operators state a claim, and what the denial of a
//! claim looks like — and owns nothing else.
//!
//! It is separate from the walk because it answers a question about the
//! *language of claims*, not about programs.  The walk knows that a
//! condition's static term is a proposition; it does not need to know
//! that denying `>` yields `<=`.
//!
//! Negation is performed by flipping the relation rather than by wrapping
//! it, and that is the point of the module.  The solver's fragment is
//! conjunctions of inequalities, so a `~` it cannot see through is a
//! hypothesis it must discard — and discarding every else-branch would
//! cost the checker every program written with an early return.

use ats2_domain::ast::BinOp;
use ats2_domain::statics::SExp;

/// The relation an operator states, or `None` if it states none.
///
/// Arithmetic is deliberately absent: `x + 1` is an integer, and reading
/// it as a claim would let the checker assume what nobody asserted.
pub fn relation(op: BinOp) -> Option<&'static str> {
    Some(match op {
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::Andalso => "&&",
        BinOp::Orelse => "||",
        _ => return None,
    })
}

/// The denial of a proposition, stated in the solver's own language
/// wherever that is possible.
pub fn negate(p: &SExp) -> SExp {
    let flipped = |op: &str| -> Option<&'static str> {
        Some(match op {
            ">" => "<=",
            ">=" => "<",
            "<" => ">=",
            "<=" => ">",
            "==" => "!=",
            "!=" => "==",
            _ => return None,
        })
    };
    match p {
        SExp::BoolLit(b) => SExp::BoolLit(!b),
        // `~~P` is `P`: branches nest, and a checker that grew a `~` per
        // level would understand the outermost one only.
        SExp::App(op, args) if op == "~" && args.len() == 1 => args[0].clone(),
        SExp::App(op, args) if args.len() == 2 => match flipped(op) {
            Some(name) => SExp::App(name.into(), args.clone()),
            // `&&` and `||` deny into disjunctions, which the solver
            // cannot hold.  Left opaque, and quietly ignored there.
            None => SExp::App("~".into(), vec![p.clone()]),
        },
        _ => SExp::App("~".into(), vec![p.clone()]),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(n: &str) -> SExp { SExp::Var(n.into()) }
    fn i(n: i64) -> SExp { SExp::IntLit(n) }
    fn app(op: &str, args: Vec<SExp>) -> SExp { SExp::App(op.into(), args) }

    #[test]
    fn each_comparison_names_the_relation_it_states() {
        let cases = [
            (BinOp::Gt, ">"), (BinOp::Ge, ">="), (BinOp::Lt, "<"),
            (BinOp::Le, "<="), (BinOp::Eq, "=="), (BinOp::Ne, "!="),
        ];
        for (op, name) in cases {
            assert_eq!(relation(op), Some(name), "{name}");
        }
    }

    #[test]
    fn the_connectives_are_relations_too() {
        assert_eq!(relation(BinOp::Andalso), Some("&&"));
        assert_eq!(relation(BinOp::Orelse), Some("||"));
    }

    #[test]
    fn arithmetic_states_nothing() {
        // `x + 1` is a number, not a claim.  Anything else here would let
        // a branch assume an assertion that was never written.
        for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Mod] {
            assert_eq!(relation(op), None);
        }
    }

    #[test]
    fn negating_a_proposition_flips_the_relation_rather_than_wrapping_it() {
        assert_eq!(negate(&app(">", vec![v("x"), i(0)])), app("<=", vec![v("x"), i(0)]));
        assert_eq!(negate(&app("<=", vec![v("x"), i(0)])), app(">", vec![v("x"), i(0)]));
        assert_eq!(negate(&app("<", vec![v("x"), i(0)])), app(">=", vec![v("x"), i(0)]));
        assert_eq!(negate(&app(">=", vec![v("x"), i(0)])), app("<", vec![v("x"), i(0)]));
        assert_eq!(negate(&app("==", vec![v("x"), i(0)])), app("!=", vec![v("x"), i(0)]));
        assert_eq!(negate(&app("!=", vec![v("x"), i(0)])), app("==", vec![v("x"), i(0)]));
    }

    #[test]
    fn a_boolean_literal_denies_to_the_other_one() {
        assert_eq!(negate(&SExp::BoolLit(true)), SExp::BoolLit(false));
    }

    #[test]
    fn negating_a_conjunction_is_left_alone_rather_than_guessed_at() {
        // `~(A && B)` is a disjunction, which the solver cannot hold, so
        // it becomes an opaque `~` the solver declines — costing
        // strength, never soundness.
        let both = app("&&", vec![app(">", vec![v("x"), i(0)]), app("<", vec![v("x"), i(9)])]);
        assert_eq!(negate(&both), app("~", vec![both]));
    }

    #[test]
    fn a_double_negation_cancels() {
        let p = app(">", vec![v("x"), i(0)]);
        assert_eq!(negate(&negate(&p)), p);
    }
}
