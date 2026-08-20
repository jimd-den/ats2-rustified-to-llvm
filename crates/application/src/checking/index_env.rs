//! # The index environment — what is known, and where
//!
//! *Literate note.*  Dependent checking is bookkeeping before it is
//! arithmetic.  Two things travel with the walk: what static term each
//! dynamic name is known to equal, and what may be assumed about those
//! terms on *this* path.  Both are scoped, and both are wrong the moment
//! they outlive their scope, so this module owns them and nothing else.
//!
//! It is a persistent structure rather than a mutable one with a stack of
//! undo records.  A branch takes a copy, learns what its guard tells it,
//! and is thrown away; the sibling branch never sees it.  Copying is what
//! makes that impossible to get wrong, and the environments are small.

use std::collections::HashMap;
use std::rc::Rc;

use ats2_domain::ast::Ty;
use ats2_domain::statics::{SExp, Sort};

/// A supply of names no source file can collide with.
///
/// Shared rather than copied, because two branches that each invent a
/// "first" fresh variable would be talking about different values under
/// the same name — the one bookkeeping error that produces unsound
/// proofs rather than merely weak ones.
#[derive(Debug, Clone, Default)]
pub struct Fresh {
    next: Rc<std::cell::Cell<u32>>,
}

impl Fresh {
    /// A new variable, hinted by `stem` so diagnostics stay readable.
    ///
    /// `%` is in the name because ATS cannot spell it: a skolem constant
    /// can then never be captured by a variable the programmer wrote.
    pub fn var(&self, stem: &str) -> SExp {
        let n = self.next.get();
        self.next.set(n + 1);
        SExp::Var(format!("{stem}%{n}"))
    }
}

/// What is known here: the index of every name in scope, and the
/// propositions this path has established.
#[derive(Debug, Clone, Default)]
pub struct IndexEnv {
    indices: HashMap<String, Vec<SExp>>,
    sizes: HashMap<String, SExp>,
    types: HashMap<String, Ty>,
    hyps: Vec<SExp>,
    fresh: Fresh,
}

impl IndexEnv {
    pub fn new() -> Self {
        IndexEnv::default()
    }

    /// The supply itself, for a collaborator that must invent names in
    /// the same sequence — a signature skolemising its existentials, say.
    ///
    /// Shared rather than handed out by value, because two collaborators
    /// each inventing a "first" fresh variable would be talking about
    /// different values under one name.
    pub fn fresh_supply(&self) -> Fresh {
        self.fresh.clone()
    }

    /// A fresh static variable, sharing this environment's supply.
    pub fn fresh(&mut self, stem: &str) -> SExp {
        self.fresh.var(stem)
    }

    /// Name a dynamic variable's index.
    pub fn bind(&mut self, name: &str, index: SExp) {
        self.bind_all(name, vec![index]);
    }

    /// Name every index a variable's type gave it.
    ///
    /// One is the common case — `int n` — but `array(a, n)` and
    /// `matrix(a, m, n)` carry more, and a subscript check that could
    /// only see the first would be a subscript check for vectors only.
    pub fn bind_all(&mut self, name: &str, indices: Vec<SExp>) {
        self.indices.insert(name.to_string(), indices);
    }

    /// The static term a name is known to equal.
    pub fn index_of(&self, name: &str) -> Option<SExp> {
        self.indices_of(name).first().cloned()
    }

    /// Every index the name carries, in the order its type wrote them.
    pub fn indices_of(&self, name: &str) -> Vec<SExp> {
        self.indices.get(name).cloned().unwrap_or_default()
    }

    /// Record how long a name is — the `n` of `array(a, n)`.
    ///
    /// Kept apart from the value's own index on purpose.  `int(n)` says
    /// the value *is* `n`; `array(a, n)` says the value has `n` of
    /// something.  Confusing the two lets an unindexed variable acquire a
    /// length nobody gave it, and then a subscript is checked against a
    /// bound that does not exist.
    pub fn bind_size(&mut self, name: &str, size: SExp) {
        self.sizes.insert(name.to_string(), size);
    }

    /// How long a name is, when its type said.
    pub fn size_of(&self, name: &str) -> Option<SExp> {
        self.sizes.get(name).cloned()
    }

    /// Record the type a name was declared with.
    ///
    /// A type carries indices at every depth — `list0(list(int, n))`
    /// buries one inside its element — and only the whole type can be
    /// matched against a parameter's whole type.  A single "size" is the
    /// shallowest case of that, and was never the general one.
    pub fn bind_type(&mut self, name: &str, ty: Ty) {
        self.types.insert(name.to_string(), ty);
    }

    /// The type a name was declared with, if the source said.
    pub fn type_of(&self, name: &str) -> Option<Ty> {
        self.types.get(name).cloned()
    }

    /// Bring a static variable into scope at a sort, assuming whatever
    /// the sort itself promises.
    ///
    /// This is what makes `{n:nat}` stronger than `{n:int}` without the
    /// rest of the checker having to know which sorts are refined.
    pub fn declare(&mut self, name: &str, sort: &Sort) {
        if let Some(r) = sort.refinement(name) {
            self.assume(r);
        }
    }

    /// Add a hypothesis to this path.
    pub fn assume(&mut self, prop: SExp) {
        if !self.hyps.contains(&prop) {
            self.hyps.push(prop);
        }
    }

    pub fn assume_all(&mut self, props: impl IntoIterator<Item = SExp>) {
        props.into_iter().for_each(|p| self.assume(p));
    }

    /// Everything this path may rely on.
    pub fn hyps(&self) -> &[SExp] {
        &self.hyps
    }

    /// Forget what was known of a name, because it was written to.
    ///
    /// The name keeps an index — it still denotes *some* integer, and
    /// saying so lets later reasoning relate it to itself — but the new
    /// index is unconstrained, so nothing survives the write.
    pub fn forget(&mut self, name: &str) {
        let v = self.fresh(name);
        self.bind(name, v);
    }

    /// Forget every name in `names`: what a loop body does to the cells
    /// it assigns, seen from outside the loop.
    pub fn forget_all(&mut self, names: impl IntoIterator<Item = String>) {
        names.into_iter().for_each(|n| self.forget(&n));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ats2_domain::ast::Ty;
    use ats2_domain::statics::{SExp, Sort};

    #[test]
    fn a_parameter_is_known_by_the_static_term_that_indexes_it() {
        let mut env = IndexEnv::new();
        env.bind("x", SExp::Var("n".into()));
        assert_eq!(env.index_of("x"), Some(SExp::Var("n".into())));
    }

    #[test]
    fn a_value_with_no_index_gets_one_of_its_own() {
        // A checker that gave up on unindexed values could not relate
        // `val y = f(x)` to anything later.  Naming the unknown is what
        // lets `y = y` be a fact even when nobody knows what y is.
        let mut env = IndexEnv::new();
        let a = env.fresh("y");
        let b = env.fresh("y");
        assert_ne!(a, b, "two unknowns must not be confused for one");
    }

    #[test]
    fn a_sort_contributes_its_own_refinement_when_a_variable_is_declared() {
        // `{n:nat}` says more than `{n:int}`, and the difference is a
        // hypothesis: declaring the variable is what puts it in scope.
        let mut env = IndexEnv::new();
        env.declare("n", &Sort::Nat);
        assert!(env.hyps().contains(&SExp::App(
            ">=".into(),
            vec![SExp::Var("n".into()), SExp::IntLit(0)]
        )));
    }

    #[test]
    fn a_branch_assumes_without_disturbing_its_sibling() {
        // Path sensitivity is the whole point: what the then-branch knows
        // must not leak into the else-branch.
        let env = IndexEnv::new();
        let mut then = env.clone();
        then.assume(SExp::BoolLit(true));
        assert_eq!(then.hyps().len(), 1);
        assert_eq!(env.hyps().len(), 0);
    }

    #[test]
    fn a_name_keeps_every_index_its_type_gave_it() {
        // `array(a, n)` is indexed by its size, and `xs[i]` cannot be
        // checked without it.  A name is not limited to one index because
        // a type is not.
        let mut env = IndexEnv::new();
        env.bind_all("xs", vec![SExp::Var("n".into())]);
        assert_eq!(env.indices_of("xs"), vec![SExp::Var("n".into())]);
        assert_eq!(env.index_of("xs"), Some(SExp::Var("n".into())));
    }

    #[test]
    fn a_name_remembers_the_type_it_was_declared_with() {
        // Indices live at every depth of a type, and only the whole type
        // can be matched against a parameter's whole type.
        let mut env = IndexEnv::new();
        let ty = Ty::App("list0".into(), vec![Ty::Name("int".into())]);
        env.bind_type("xs", ty.clone());
        assert_eq!(env.type_of("xs"), Some(ty));
        assert_eq!(env.type_of("nothing"), None);
    }

    #[test]
    fn a_length_is_not_the_same_fact_as_a_value() {
        // `int(n)` says the value *is* n; `array(a, n)` says it holds n
        // things.  A checker that stored them in one place would let an
        // ordinary integer be subscripted against its own value.
        let mut env = IndexEnv::new();
        env.bind("x", SExp::IntLit(3));
        assert_eq!(env.size_of("x"), None);
        env.bind_size("xs", SExp::Var("n".into()));
        assert_eq!(env.size_of("xs"), Some(SExp::Var("n".into())));
    }

    #[test]
    fn a_name_with_no_indices_at_all_reports_none_rather_than_an_empty_answer() {
        let env = IndexEnv::new();
        assert!(env.indices_of("nothing").is_empty());
        assert_eq!(env.index_of("nothing"), None);
    }

    #[test]
    fn writing_to_a_cell_forgets_what_was_known_of_it() {
        // `x := f()` makes every earlier fact about `x` false.  Keeping
        // them would let the checker prove things that are not true, which
        // is the one failure a checker may never have.
        let mut env = IndexEnv::new();
        env.bind("x", SExp::IntLit(3));
        env.forget("x");
        let after = env.index_of("x");
        assert_ne!(after, Some(SExp::IntLit(3)));
        assert!(
            after.is_some(),
            "the cell still has *some* value, just an unknown one"
        );
    }

    #[test]
    fn fresh_names_cannot_collide_with_names_the_source_wrote() {
        let mut env = IndexEnv::new();
        let SExp::Var(name) = env.fresh("n") else {
            panic!("a variable")
        };
        assert!(
            name.contains('%'),
            "fresh names must be unspellable in ATS: {name}"
        );
    }
}
