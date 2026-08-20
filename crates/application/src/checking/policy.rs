//! # Deciding what to do about a claim that did not go through
//!
//! *Literate note.*  The walk writes down obligations and the solver
//! judges them; neither is allowed an opinion about what a failure
//! *means*.  That opinion lives here, alone, because it is the one thing
//! about a type checker that a project changes its mind on.
//!
//! There are three verdicts and two policies, and the interesting cell is
//! `Unknown`:
//!
//! * **Refuted** is an error under every policy.  The program is provably
//!   wrong and no amount of tolerance makes it right.
//! * **Proved** is never an error, obviously.
//! * **Unknown** is an error under `Strict` and not under `Permissive`.
//!   Both readings are defensible and neither is defensible alone: a
//!   checker that accepts what it cannot prove is not checking, and a
//!   checker that rejects a working corpus it merely cannot yet reason
//!   about is a checker that gets switched off.  So the choice is the
//!   caller's, and it is made in one place.
//!
//! One case is neither: hypotheses that contradict each other prove every
//! goal.  Passing silently there would hide a branch that cannot run, so
//! it is reported as what it is.

use ats2_domain::errors::{CompileError, ErrorKind};
use ats2_domain::obligation::Obligation;
use ats2_domain::statics::SExp;

use crate::constraints::{entails, is_contradictory, Verdict};

/// What to do with a claim the solver could neither prove nor refute.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Strictness {
    /// Anything unproved is an error — the honest reading of "checked".
    #[default]
    Strict,
    /// Only the provably false is an error.  What the checker cannot yet
    /// reason about compiles, so a corpus can be adopted before the
    /// solver is finished.
    Permissive,
}

/// Judge every obligation, and report the ones the policy will not
/// forgive.
pub fn discharge(obligations: &[Obligation], policy: Strictness) -> Vec<CompileError> {
    let mut out: Vec<CompileError> = Vec::new();
    for o in obligations {
        let Some(message) = verdict_message(o, policy) else { continue };
        let error = CompileError {
            kind: ErrorKind::Check,
            span: o.span,
            message: format!("{} {message}", o.describe()),
        };
        // One walk can reach the same call by two routes; the reader
        // wants the claim once.
        if !out.contains(&error) {
            out.push(error);
        }
    }
    out
}

/// The complaint this obligation earns, if any.
fn verdict_message(o: &Obligation, policy: Strictness) -> Option<String> {
    if is_contradictory(&o.hyps) {
        return Some("on a path that cannot be reached".into());
    }
    match entails(&o.hyps, &o.goal) {
        Verdict::Proved => None,
        Verdict::Refuted => Some(format!(", which {}is false", under(&o.hyps))),
        Verdict::Unknown if policy == Strictness::Strict => {
            Some(format!(", which could not be proved{}", from(&o.hyps)))
        }
        Verdict::Unknown => None,
    }
}

/// "given `h`, " — the assumptions a refutation was reached under.
fn under(hyps: &[SExp]) -> String {
    match listed(hyps) {
        Some(text) => format!("given {text}, "),
        None => String::new(),
    }
}

/// " from `h`" — the assumptions a proof was attempted from.
fn from(hyps: &[SExp]) -> String {
    match listed(hyps) {
        Some(text) => format!(" from {text}"),
        None => " from nothing at all".into(),
    }
}

fn listed(hyps: &[SExp]) -> Option<String> {
    if hyps.is_empty() {
        return None;
    }
    let parts: Vec<String> = hyps.iter().map(|h| format!("`{h}`")).collect();
    Some(parts.join(" and "))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ats2_domain::obligation::Origin;

    fn v(n: &str) -> SExp { SExp::Var(n.into()) }
    fn i(n: i64) -> SExp { SExp::IntLit(n) }
    fn app(op: &str, a: SExp, b: SExp) -> SExp { SExp::App(op.into(), vec![a, b]) }

    fn ob(hyps: Vec<SExp>, goal: SExp) -> Obligation {
        Obligation::new(hyps, goal, Origin::Call { callee: "f".into() })
    }

    #[test]
    fn a_proved_obligation_is_not_reported_under_any_policy() {
        let o = ob(vec![app(">", v("n"), i(3))], app(">=", v("n"), i(0)));
        for policy in [Strictness::Strict, Strictness::Permissive] {
            assert!(discharge(std::slice::from_ref(&o), policy).is_empty(), "{policy:?}");
        }
    }

    #[test]
    fn a_refuted_obligation_is_reported_under_every_policy() {
        // This is the one verdict no policy may forgive: the program is
        // provably wrong, and compiling it would be a lie.
        let o = ob(vec![], app(">=", i(-1), i(0)));
        for policy in [Strictness::Strict, Strictness::Permissive] {
            assert_eq!(discharge(std::slice::from_ref(&o), policy).len(), 1, "{policy:?}");
        }
    }

    #[test]
    fn an_unproved_obligation_is_an_error_only_under_the_strict_policy() {
        // A checker that accepts what it cannot prove is not checking.
        // A checker that rejects a corpus it merely cannot yet reason
        // about is one nobody can adopt.  Both are true, so both exist.
        let o = ob(vec![], app(">=", v("n"), i(0)));
        assert_eq!(discharge(std::slice::from_ref(&o), Strictness::Strict).len(), 1);
        assert!(discharge(std::slice::from_ref(&o), Strictness::Permissive).is_empty());
    }

    #[test]
    fn the_two_failures_do_not_read_the_same() {
        // "false" and "not shown" are different accusations, and a
        // diagnostic that conflates them sends the reader looking for a
        // bug that is not there.
        let refuted = discharge(&[ob(vec![], app(">=", i(-1), i(0)))], Strictness::Strict);
        let unknown = discharge(&[ob(vec![], app(">=", v("n"), i(0)))], Strictness::Strict);
        assert!(refuted[0].message.contains("is false"), "{}", refuted[0].message);
        assert!(unknown[0].message.contains("could not be proved"), "{}", unknown[0].message);
    }

    #[test]
    fn every_reported_failure_is_a_check_error_and_names_its_origin() {
        let errs = discharge(&[ob(vec![], app(">=", i(-1), i(0)))], Strictness::Strict);
        assert_eq!(errs[0].kind, ErrorKind::Check);
        assert!(errs[0].message.contains("the call to `f`"), "{}", errs[0].message);
    }

    #[test]
    fn an_unreachable_path_proves_anything_and_is_reported_as_unreachable() {
        // Hypotheses that contradict each other prove every goal, so a
        // silent pass here would hide a branch that cannot run.  Saying
        // so is more useful than the vacuous success.
        let o = ob(vec![app(">", v("n"), i(5)), app("<", v("n"), i(2))], app(">=", v("n"), i(0)));
        let errs = discharge(&[o], Strictness::Strict);
        assert_eq!(errs.len(), 1);
        assert!(errs[0].message.contains("cannot be reached"), "{}", errs[0].message);
    }

    #[test]
    fn identical_failures_from_one_walk_are_reported_once() {
        let o = ob(vec![], app(">=", i(-1), i(0)));
        assert_eq!(discharge(&[o.clone(), o], Strictness::Strict).len(), 1);
    }
}
