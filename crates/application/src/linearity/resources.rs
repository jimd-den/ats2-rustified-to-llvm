//! # The ledger — what is held, and what has been given away
//!
//! *Literate note.*  A linear value is a *resource*: it must be consumed
//! exactly once.  Used twice it is a use-after-free; never used it is a
//! leak.  Neither is a claim about arithmetic, so neither is anything
//! [`crate::constraints`] could decide — this is an accounting problem,
//! and what it needs is a ledger.
//!
//! The ledger is deliberately dumb.  It knows that a name was acquired,
//! whether it has since been given away, and in what order the names
//! arrived; it knows nothing about expressions, types, or why any of it
//! happened.  Everything interesting is in [`super::walk`], which decides
//! *where* a resource changes hands — and that is the part that has to
//! change when the language does.
//!
//! One rule is worth stating twice: a name this ledger never heard of is
//! **not a resource**.  Ordinary values are used as often as they like,
//! and a check that complained about one of them would be a check people
//! turn off on the first afternoon.

use std::collections::HashMap;

/// What happened when a resource was reached for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Use {
    /// It was there to be used.
    Given,
    /// It had already been given away — a use after the handover.
    Again,
    /// The name holds no resource, so using it means nothing here.
    NotAResource,
}

/// The resources one path is holding.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Resources {
    /// Whether each acquired name is still held.
    held: HashMap<String, bool>,
    /// The order the names arrived in, so a diagnostic reads the same
    /// way twice.
    order: Vec<String>,
}

impl Resources {
    /// Take charge of a resource under this name.
    pub fn acquire(&mut self, name: &str) {
        if self.held.insert(name.to_string(), true).is_none() {
            self.order.push(name.to_string());
        }
    }

    /// Whether the name still holds its resource.
    pub fn is_held(&self, name: &str) -> bool {
        self.held.get(name).copied().unwrap_or(false)
    }

    /// Give the resource away.
    pub fn consume(&mut self, name: &str) -> Use {
        match self.held.get_mut(name) {
            None => Use::NotAResource,
            Some(held) if *held => {
                *held = false;
                Use::Given
            }
            Some(_) => Use::Again,
        }
    }

    /// Reach for the resource without giving it away.
    ///
    /// `!xs` lends: the caller keeps it and gets it back, so it is still
    /// theirs to give away afterwards.  What a borrow *cannot* do is
    /// reach something already handed over — that is the same mistake as
    /// using it twice, and it is reported the same way.
    pub fn borrow(&mut self, name: &str) -> Use {
        match self.held.get(name) {
            None => Use::NotAResource,
            Some(true) => Use::Given,
            Some(false) => Use::Again,
        }
    }

    /// Every resource still held, in the order the names arrived.
    pub fn leaked(&self) -> Vec<String> {
        self.order
            .iter()
            .filter(|n| self.is_held(n))
            .cloned()
            .collect()
    }

    /// The first resource these two paths do not agree about.
    ///
    /// Every branch must leave the same resources held, or what is held
    /// afterwards depends on which way it went — and then nothing after
    /// the branch can be checked at all.
    pub fn disagreement(&self, other: &Resources) -> Option<String> {
        self.order
            .iter()
            .chain(other.order.iter().filter(|n| !self.held.contains_key(*n)))
            .find(|n| self.is_held(n) != other.is_held(n))
            .cloned()
    }

    /// Forget every resource, because this path does not return.
    ///
    /// `$raise` and its kind end a path rather than finishing it, so
    /// what it was holding is not the branch's to answer for.
    pub fn abandon(&mut self) {
        self.held.values_mut().for_each(|held| *held = false);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_resource_starts_out_held() {
        let mut r = Resources::default();
        r.acquire("xs");
        assert!(r.is_held("xs"));
        assert_eq!(r.leaked(), vec!["xs".to_string()]);
    }

    #[test]
    fn consuming_a_resource_gives_it_away() {
        let mut r = Resources::default();
        r.acquire("xs");
        assert_eq!(r.consume("xs"), Use::Given);
        assert!(!r.is_held("xs"));
        assert!(r.leaked().is_empty(), "what was given away cannot leak");
    }

    #[test]
    fn consuming_a_resource_twice_is_the_error_the_whole_thing_exists_for() {
        let mut r = Resources::default();
        r.acquire("xs");
        r.consume("xs");
        assert_eq!(r.consume("xs"), Use::Again);
    }

    #[test]
    fn a_name_that_never_held_anything_is_not_a_resource() {
        // Ordinary values are used as often as they like, and saying so
        // about one of them would make the check unusable.
        let mut r = Resources::default();
        assert_eq!(r.consume("n"), Use::NotAResource);
        assert_eq!(r.consume("n"), Use::NotAResource);
    }

    #[test]
    fn borrowing_leaves_the_resource_where_it_was() {
        // `!xs` is lent: the caller keeps it and gets it back, so it is
        // still theirs to give away afterwards.
        let mut r = Resources::default();
        r.acquire("xs");
        assert_eq!(r.borrow("xs"), Use::Given);
        assert!(r.is_held("xs"));
        assert_eq!(r.consume("xs"), Use::Given);
    }

    #[test]
    fn borrowing_what_was_already_given_away_is_still_wrong() {
        let mut r = Resources::default();
        r.acquire("xs");
        r.consume("xs");
        assert_eq!(r.borrow("xs"), Use::Again);
    }

    #[test]
    fn two_paths_that_agree_agree() {
        // Every branch must leave the same resources held, or what is
        // held after the branch depends on which way it went — and then
        // nothing after it can be checked at all.
        let mut base = Resources::default();
        base.acquire("xs");
        let mut taken = base.clone();
        taken.consume("xs");
        let mut untaken = base.clone();
        untaken.consume("xs");
        assert_eq!(taken.disagreement(&untaken), None);
    }

    #[test]
    fn two_paths_that_disagree_name_what_they_disagree_about() {
        let mut base = Resources::default();
        base.acquire("xs");
        let mut taken = base.clone();
        taken.consume("xs");
        assert_eq!(base.disagreement(&taken), Some("xs".to_string()));
    }

    #[test]
    fn what_a_body_leaked_is_reported_in_the_order_it_was_acquired() {
        // A diagnostic that names resources in a shuffled order is a
        // diagnostic that reads differently on every run.
        let mut r = Resources::default();
        for name in ["a", "b", "c"] {
            r.acquire(name);
        }
        r.consume("b");
        assert_eq!(r.leaked(), vec!["a".to_string(), "c".to_string()]);
    }
}
