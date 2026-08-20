//! # The abstract syntax tree — the program as pure shape
//!
//! *Literate note.*  Where tokens are the *surface* of a program, the AST
//! is its *skeleton*: every construct the compiler understands, stripped of
//! whitespace, comments and concrete syntax, and arranged into a tree.
//! The AST is the contract between the parser (which builds it) and the
//! emitter (which consumes it).  Both of those live in other layers; this
//! module only declares the shape, so the two sides can evolve
//! independently as long as they both speak this shape.
//!
//! The subset deliberately mirrors real ATS2: datatype declarations with
//! constructor lists, recursive `fun` definitions, `implement` clauses for
//! the `main0` entry point, `if/then/else` expressions, `let/in/end`
//! bindings, `lam` lambdas, and `println!` macro calls.  A few constructs
//! real ATS has — dependent types, template parameters, termination
//! metrics — are intentionally absent; they arrive in later iterations
//! without disturbing this shape.

use crate::statics::{Quant, SExp, Sort};

/// A whole compiled unit: an ordered list of top-level definitions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub defs: Vec<Def>,
}

impl Program {
    pub fn new(defs: Vec<Def>) -> Self {
        Self { defs }
    }

    /// The definitions, in source order.
    pub fn defs(&self) -> &[Def] {
        &self.defs
    }
}

/// A top-level definition: a datatype, a function, or an implementation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Def {
    Datatype(DatatypeDef),
    Fun(FunDef),
    Implement(ImplementDef),
    /// `extern fun f (x: t): u` — a signature with no body here.
    ///
    /// It is what lets a definition be written separately from its
    /// declaration, which is how ATS states a *template*: the `extern`
    /// gives the shape, and one or more `implement`s fill it in.
    Extern(FunDecl),
    /// `val name = expr` at the top level — a value the whole program
    /// shares, worked out once before `main` runs.
    Val(ValDef),
    /// `overload * with f` — the function to try when an operator's
    /// operands do not fit it natively.
    Overload { op: String, func: String },
    /// `#define NAME value` — a compile-time constant.  It is not a
    /// function and occupies no storage: every mention of `NAME` is
    /// replaced by `value` at emission time.
    Const(ConstDef),
    /// `%{ ... %}` — a block of C the program brought with it.
    ///
    /// It is not this compiler's language, and nothing here reads it: it
    /// is carried through untouched and handed to the toolchain, which
    /// speaks C. It is a *definition* because that is what it is — the
    /// body of some `extern fun` declared elsewhere in the file — and a
    /// program that lost it would compile and then fail to link.
    InlineC(String),
}

/// `datatype name(a, b) = ctor1(...) | ctor2 | ...`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DatatypeDef {
    pub name: String,
    pub ty_params: Vec<String>,
    pub ctors: Vec<Ctor>,
    /// `datavtype` / `dataview` — whether its values are *resources*.
    ///
    /// A linear value must be consumed exactly once: used twice it is a
    /// use-after-free, never used it is a leak.  Nothing about the bits
    /// says which kind a value is — the declaration does, and it is the
    /// only place that does.
    pub linear: bool,
}

/// One constructor of a datatype, e.g. `cons(a, list(a))`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ctor {
    pub name: String,
    pub fields: Vec<Ty>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub ty: Ty,
    /// `!t` or `&t` — whether the parameter is *lent* rather than given.
    ///
    /// The caller keeps a borrowed value and gets it back; the callee
    /// may read it, may write through it, and may not consume it.
    /// Dropping the mark makes every borrow look like a handover, and
    /// then a program that lends the same list twice reads as one that
    /// frees it twice.
    pub borrowed: bool,
}

/// `fun name(x: int, y: int): int = body` — recursive by default, exactly
/// as in ATS2.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunDef {
    /// The type parameters this definition abstracts over, if it is a
    /// template.  Empty for an ordinary function.
    pub ty_params: Vec<String>,
    /// The `{n:nat | n > 0}` quantifiers written before the parameter
    /// list: what the caller must establish, and what the body may
    /// therefore assume.  Empty for a function that says nothing about
    /// its arguments beyond their types.
    pub universals: Vec<Quant>,
    /// The `[r:int]` quantifier written on the result: what the caller
    /// may assume about the value it gets back.
    pub existentials: Vec<Quant>,
    /// `.<n>.` — the term that must decrease on every recursive call.
    ///
    /// It is what makes a *total* function total: without it a
    /// definition may promise anything at all and satisfy the promise by
    /// never returning.  Several terms are a lexicographic metric, in the
    /// order written.  Empty means the source made no claim, and none is
    /// checked — ATS's `.<>.` says exactly that.
    pub metric: Vec<SExp>,
    pub name: String,
    pub params: Vec<Param>,
    pub ret: Ty,
    pub body: Expr,
}

/// `implement main0() = body` (in this foundation: the program entry).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplementDef {
    /// The type parameters bound by `implement{a}`.
    pub ty_params: Vec<String>,
    /// The instance this fills in: the `<list0(int)>` of
    /// `implement fprint_val<list0(int)> (out, xs) = ...`.
    ///
    /// Empty when the implementation is generic and answers for every
    /// instance.  ATS's printing protocol turns on the difference: a
    /// program supplies `fprint_val` for its *own* types, and the ones
    /// the compiler already knows must not be shadowed by it.
    pub instance: Vec<Ty>,
    pub name: String,
    pub params: Vec<Param>,
    pub ret: Option<Ty>,
    pub body: Expr,
}

/// A type.  Three shapes exist in the subset: named types (`int`, `bool`,
/// `string`, user datatypes), type application (`list(a)`), and function
/// types `(a, b) -> c`.
/// `val name = expr` at the top level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValDef {
    pub name: String,
    pub ty: Option<Ty>,
    pub value: Expr,
}

/// A function's signature without its body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunDecl {
    pub name: String,
    /// Whether what this builds or returns is a resource.
    ///
    /// A `dataview`'s constructors build linear proofs: permission to
    /// touch something, which could not be permission at all if it could
    /// be used twice.
    pub linear: bool,
    /// Whether this declares a *proof* rather than a function.
    ///
    /// `praxi`, `prfun` and each constructor of a `dataprop` declare
    /// something that exists only in the static language: no body, no
    /// symbol, no bits.  The checker must see them — they are where every
    /// claim in a proof comes from — and the emitter must not, because
    /// there is nothing there to emit and `FACT(n, r)` is not a type any
    /// machine has.
    pub proof: bool,
    /// The type parameters a template abstracts over: the `a` of
    /// `fun{a:t@ype}`.  Empty for an ordinary function.
    pub ty_params: Vec<String>,
    /// `{n:nat | n > 0}` — the same promise a definition's quantifiers
    /// make.  A declaration is a promise with the body left elsewhere,
    /// and a call site cannot tell the two apart, so it must not have to.
    pub universals: Vec<Quant>,
    /// `[r:int]` on the result — what the caller may assume it got.
    pub existentials: Vec<Quant>,
    pub params: Vec<Param>,
    pub ret: Ty,
}

/// `#define NAME value` — a named compile-time constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstDef {
    pub name: String,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    Name(String),
    /// `list(a)` — a type name applied to type arguments.
    App(String, Vec<Ty>),
    Fun(Vec<Ty>, Box<Ty>),
    /// `(t, u)` or `@(t, u)` — a tuple.  ATS distinguishes boxed from
    /// unboxed tuples; the difference is one of representation, which
    /// only matters once tuples are actually lowered.
    Tuple(Vec<Ty>),
    /// `int(n)`, `string(n1)`, `array(a, n)` — a type refined by static
    /// index terms.
    ///
    /// The indices carry no runtime content: `int(n)` and `int` are the
    /// same machine word.  They are kept because they are the whole
    /// point of a dependent type — the difference between "an integer"
    /// and "the integer `n`" is what the constraint checker reads, and
    /// erasing them here would leave nothing to check.
    Index(Box<Ty>, Vec<SExp>),
    /// `'{ cmp= (a, a) -> int }` — a record: a tuple whose slots have
    /// names.
    ///
    /// The names are part of the type, not decoration on it: they are how
    /// a field is reached, and two records that differ only in them are
    /// different types.  The order is the order written, which is what
    /// fixes each name to a slot.
    Record(Vec<(String, Ty)>),
    /// `(FACT(n, r) | int(r))` — a value carrying a proof about itself.
    ///
    /// The proof half is erased before anything runs, so the value's
    /// representation is the second half alone.  It is kept because it
    /// is where the *interesting* index usually lives: a function
    /// returning `[r:int] (FACT(n,r) | int(r*r0))` pins `r` down through
    /// the proposition, not through the arithmetic — and the arithmetic
    /// on its own is nonlinear and out of any linear solver's reach.
    Proof(Box<Ty>, Box<Ty>),
}

impl Ty {
    /// The type with every static index dropped — what the value looks
    /// like once it is running.
    ///
    /// Emission works on this: an index is a fact about a value, never a
    /// part of it.
    pub fn erased(&self) -> Ty {
        match self {
            Ty::Index(base, _) => base.erased(),
            // A proof occupies no storage: what a `(pf | v)` *is*, is v.
            Ty::Proof(_, value) => value.erased(),
            Ty::Name(_) => self.clone(),
            Ty::App(n, args) => Ty::App(n.clone(), args.iter().map(Ty::erased).collect()),
            Ty::Fun(args, ret) => {
                Ty::Fun(args.iter().map(Ty::erased).collect(), Box::new(ret.erased()))
            }
            Ty::Tuple(items) => Ty::Tuple(items.iter().map(Ty::erased).collect()),
            Ty::Record(fields) => {
                Ty::Record(fields.iter().map(|(n, t)| (n.clone(), t.erased())).collect())
            }
        }
    }

    /// The index terms this type is refined by, if any.
    pub fn indices(&self) -> &[SExp] {
        match self {
            Ty::Index(_, idx) => idx,
            // The indices of a `(pf | v)` are the value's: they are what
            // describes the thing that exists at run time.
            Ty::Proof(_, value) => value.indices(),
            _ => &[],
        }
    }

    /// The proposition a value carries a proof of, if it carries one.
    pub fn proof(&self) -> Option<&Ty> {
        match self {
            Ty::Proof(proof, _) => Some(proof),
            _ => None,
        }
    }
}

/// Binary operators of the subset, split into three families: arithmetic,
/// comparison, and boolean connectives.  The distinction matters to the
/// emitter, which must pick a different LLVM instruction per family.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    // boolean connectives (short-circuit in ATS semantics)
    Andalso,
    Orelse,
}

impl BinOp {
    /// Whether this operator yields a `bool` rather than an `int`.
    pub fn is_comparison(self) -> bool {
        matches!(self, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Andalso | BinOp::Orelse)
    }
}

/// An expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// `_` — a value the source declines to name.  ATS uses it where a
    /// value is determined by the context (an inferred argument, a
    /// don't-care position in a pattern).  Nothing can be emitted for it,
    /// so it exists to let the parser record what was written.
    Wildcard,
    /// The value an uninitialized `var` holds before its first write.
    ///
    /// `var res: res` declares a cell without saying what is in it, and
    /// ATS's type system is what guarantees nothing reads it before a
    /// write.  There is no *expression* in the source for this, so it
    /// cannot be desugared into one: what belongs in the cell depends on
    /// the annotated type, which only the emitter knows.  Hence a node
    /// that means "whatever a cell of this type starts as".
    Uninit,
    /// `()` — the unit value, the sole inhabitant of type `void`.
    /// It is what an empty `let ... in end` body evaluates to, and what
    /// every effectful statement (`println!`, `assertloc`) returns.
    Unit,
    /// `42`
    IntLit(i64),
    /// `'a'` — a character literal, already decoded to its byte.
    CharLit(u8),
    /// `1.5` — a floating-point literal.
    FloatLit(crate::tokens::FloatBits),
    /// `true` / `false`
    BoolLit(bool),
    /// a decoded string constant, e.g. `"hello"`
    StrLit(String),
    /// a variable reference: `x`
    Var(String),
    /// unary negation: `~x` or `-x`
    UnaryNeg(Box<Expr>),
    /// `a + b`, `a = b`, `a andalso b`, …
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    /// `(a, b)` — a tuple value.
    TupleLit(Vec<Expr>),
    /// `'{ x= 1, y= 2 }` — a record value.
    ///
    /// A record is a tuple whose slots have names.  The names are what
    /// distinguishes it: two records with the same field types but
    /// different names are different types, and a field is reached by
    /// name rather than by position.  Order is kept as written, because
    /// that is what fixes the slots.
    RecordLit(Vec<(String, Expr)>),
    /// `r.cmp` — one field of a record, by name.
    ///
    /// Distinct from `Proj`, which reaches a tuple slot by position:
    /// which slot a name means depends on the record's type, and only
    /// the emitter knows that.
    Field(Box<Expr>, String),
    /// `e : t` — an ascription.
    ///
    /// It says what `e` should be, which is a *claim* and therefore the
    /// checker's business: `(if n >= 0 then n else 0): intGte(0)` is how
    /// a program turns an integer nobody can bound into one that is
    /// bounded, and it is the only line that says so.  Nothing about the
    /// value changes, so every later stage looks through it.
    Ascribe(Box<Expr>, Ty),
    /// `(pf | v)` — a value returned together with a proof about it.
    ///
    /// The proof is erased before anything runs, so `v` is the whole of
    /// what this evaluates to.  It survives to the checker because the
    /// proof is what determines the existential the function promised:
    /// `(pf0 | res)` against `[r:int] (FACT(n,r) | int(r*r0))` fixes `r`
    /// through the proposition, which the arithmetic alone cannot do.
    ProofPair(Box<Expr>, Box<Expr>),
    /// `f<int>` — a template named together with the types it is being
    /// instantiated at.  It is not yet a function: monomorphisation turns
    /// each distinct instantiation into one.
    Inst(String, Vec<Ty>),
    /// `fact_ind{n}{r}` — an expression named together with the *static*
    /// terms it is instantiated at.
    ///
    /// Distinct from [`Expr::Inst`] because the two instantiate different
    /// languages: type arguments choose which function is emitted, index
    /// arguments choose what it *proves*.  Nothing here survives to run
    /// time — the emitter looks straight through it — but the checker
    /// cannot: `fact_ind{n}()` and `fact_ind{m}()` are the same code and
    /// different claims, and an axiom applied at the wrong index is the
    /// one mistake a proof language exists to catch.
    StaticInst(Box<Expr>, Vec<SExp>),
    /// `f(a, b)`
    Call(Box<Expr>, Vec<Expr>),
    /// `xs[i]` — indexing into an array or, in `main`, into `argv`.
    Index(Box<Expr>, Box<Expr>),
    /// `xs.0 := e` — a store into a *place* rather than a name.
    ///
    /// `Assign` covers the one place a name can denote: its own cell.
    /// Everything else — a tuple slot, later an array element or the
    /// target of a reference — is an address computed from the left-hand
    /// expression, so the left-hand side is kept as an expression.
    Store(Box<Expr>, Box<Expr>),
    /// `!p` — read through a pointer.
    ///
    /// In ATS this is how a `ref` and a by-reference parameter are read.
    /// What it costs at run time depends on what is behind the pointer,
    /// which is why it survives to the emitter rather than being
    /// desugared here.
    Deref(Box<Expr>),
    /// `xs.0` — projecting one component out of a tuple.
    ///
    /// Distinct from `Index` because a tuple's slots may hold different
    /// types, so the component's type comes from the slot rather than
    /// from the aggregate.
    Proj(Box<Expr>, usize),
    /// `if c then t else e` (the `else` is mandatory — everything is an
    /// expression in ATS)
    IfThenElse(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `let b1; b2 in body end` (also the desugared form of `{ ... }`
    /// blocks)
    Let(Vec<LetBind>, Box<Expr>),
    /// `lam (x: int): int => x + 1` — an anonymous function.
    ///
    /// The return type is kept when the source gave one: a lambda may be
    /// recursive through the function that builds it, and then its
    /// annotation is the only thing that says what that function returns.
    Lam(Vec<Param>, Option<Ty>, Box<Expr>),
    /// Functions defined *inside* a body — by a nested `fun` in a `let`,
    /// or by a `where { ... }` clause.  They are scoped to the body they
    /// wrap and may read the enclosing function's bindings, which is what
    /// distinguishes them from top-level functions and why a later pass
    /// has to lift them out before emission.
    LetFun(Vec<FunDef>, Box<Expr>),
    /// `x := e` — assignment to a `var` cell.  It is an expression of
    /// type void, not a statement, because everything in ATS is an
    /// expression.
    Assign(String, Box<Expr>),
    /// `while (cond) body` — the condition is re-evaluated each turn, so
    /// it must read a mutable cell to ever terminate.
    While(Box<Expr>, Box<Expr>),
    /// `for (init; cond; step) body` — the C-shaped loop.  It is *not*
    /// desugared to a `while` in the AST: keeping the three clauses
    /// separate lets the emitter place `step` in its own block, which is
    /// what makes the loop's shape obvious in the IR.
    For(Box<Expr>, Box<Expr>, Box<Expr>, Box<Expr>),
    /// `case e of | p1 => e1 | p2 => e2` — pattern matching, and the
    /// only way to take a datatype apart.
    Case(Box<Expr>, Vec<(Pattern, Expr)>),
    /// `println!(...)` — a macro invocation.
    MacroCall(String, Vec<Expr>),
}

impl Expr {
    /// Apply `f` to every immediate subexpression.
    ///
    /// Written once, here, so that every pass which walks an expression
    /// states only what it is looking for and not how many shapes an
    /// expression can take — and so that adding a shape breaks the one
    /// place that must know about it.
    pub fn each_subexpr(&self, f: &mut impl FnMut(&Expr)) {
        match self {
            Expr::Unit
            | Expr::Uninit
            | Expr::Wildcard
            | Expr::IntLit(_)
            | Expr::CharLit(_)
            | Expr::FloatLit(_)
            | Expr::BoolLit(_)
            | Expr::StrLit(_)
            | Expr::Var(_)
            | Expr::Inst(..) => {}
            Expr::StaticInst(inner, _) => f(inner),
            Expr::ProofPair(proof, value) => {
                f(proof);
                f(value);
            }
            Expr::Ascribe(inner, _) => f(inner),
            Expr::UnaryNeg(a) | Expr::Proj(a, _) | Expr::Deref(a) | Expr::Field(a, _) => f(a),
            Expr::RecordLit(fields) => fields.iter().for_each(|(_, v)| f(v)),
            Expr::BinOp(_, a, b) | Expr::Index(a, b) | Expr::Store(a, b) | Expr::While(a, b) => {
                f(a);
                f(b);
            }
            Expr::Assign(_, a) => f(a),
            Expr::IfThenElse(a, b, c) => {
                f(a);
                f(b);
                f(c);
            }
            Expr::For(a, b, c, d) => {
                f(a);
                f(b);
                f(c);
                f(d);
            }
            Expr::Call(c, args) => {
                f(c);
                args.iter().for_each(&mut *f);
            }
            Expr::MacroCall(_, args) | Expr::TupleLit(args) => args.iter().for_each(&mut *f),
            Expr::Let(binds, body) => {
                binds.iter().for_each(|b| f(&b.value));
                f(body);
            }
            Expr::Lam(_, _, body) => f(body),
            Expr::LetFun(funs, body) => {
                funs.iter().for_each(|fun| f(&fun.body));
                f(body);
            }
            Expr::Case(scrutinee, arms) => {
                f(scrutinee);
                arms.iter().for_each(|(_, body)| f(body));
            }
        }
    }

}

/// A pattern: the left-hand side of a `case` arm.
///
/// Patterns both *test* a value and *bind* parts of it, and the two jobs
/// are done by the same syntax: `cons(x, xs)` succeeds only when the
/// value was built by `cons`, and when it does, names the two fields.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    /// `_` — matches anything, binds nothing.
    Wildcard,
    /// `x` — matches anything and binds it.
    Var(String),
    /// `0`, `'a'`, `true`, `"s"` — matches one value exactly.
    Int(i64),
    Char(u8),
    Bool(bool),
    Str(String),
    /// `nil()`, `cons(x, xs)` — matches a constructor and its fields.
    Ctor(String, Vec<Pattern>),
    /// `(x, y)` — matches a tuple componentwise.
    Tuple(Vec<Pattern>),
    /// `@cons(x, xs)` — matches *in place*.
    ///
    /// An ordinary pattern copies what it names out of the value; this
    /// one names the value's own cells, so writing to a name it bound
    /// writes into the value.  ATS uses it to build a list by filling in
    /// its own tail, which is the one thing an immutable match cannot
    /// express.
    InPlace(Box<Pattern>),
}

impl Pattern {
    /// Every name this pattern binds, in the order they appear.
    ///
    /// The order matters: it is the order the emitter will bind them in,
    /// and a reader should be able to predict it from the source.
    pub fn bound_names(&self) -> Vec<String> {
        let mut out = Vec::new();
        self.collect_names(&mut out);
        out
    }

    fn collect_names(&self, out: &mut Vec<String>) {
        match self {
            Pattern::Wildcard | Pattern::Int(_) | Pattern::Char(_) | Pattern::Bool(_) | Pattern::Str(_) => {}
            Pattern::Var(n) => out.push(n.clone()),
            Pattern::Ctor(_, fields) => {
                for f in fields {
                    f.collect_names(out);
                }
            }
            Pattern::Tuple(items) => {
                for i in items {
                    i.collect_names(out);
                }
            }
            Pattern::InPlace(inner) => inner.collect_names(out),
        }
    }
}

/// One binding inside a `let`/block: `val x: ty = value`, or `val () = value`
/// when `name` is `None` (a discard binding).
///
/// `mutable` distinguishes ATS's two binding keywords.  `val` names a
/// *value*, which never changes and needs no storage.  `var` names a
/// *cell*: it is allocated on the stack, it can be the target of `:=`,
/// and reading it is a load rather than a reference to an SSA register.
///
/// A `var` may be declared without an initializer (`var i: int`).  ATS's
/// type system tracks initialization and forbids reading such a cell
/// before it is written, so this compiler materializes a zero of the
/// annotated type rather than carrying an `Option` through every stage:
/// for programs ATS itself accepts, the two are indistinguishable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetBind {
    pub name: Option<String>,
    pub ty: Option<Ty>,
    pub value: Expr,
    pub mutable: bool,
    /// `val [r1:int] (pf | x) = f(...)` — the static variables this
    /// binding *opens*.
    ///
    /// A function that returns `[r:int] int(r)` promises a witness
    /// exists and refuses to say which.  The caller may give that
    /// witness a name, and from then on reason about it — which is the
    /// only way an existential result is ever useful.  Without the name,
    /// every fact about the returned value is about a variable nobody
    /// can mention twice.
    pub opened: Vec<(String, Sort)>,
    /// `prval pf = ...` — a *proof* binding.
    ///
    /// It is a binding the checker must see and the emitter must not.
    /// What it names is a proof, which occupies no storage and cannot be
    /// called at run time: emitting it would be a call to a function
    /// that was never built. But erasing it at the parser would throw
    /// away the only line in the file that establishes the claim the
    /// body goes on to rely on, so it is *marked* rather than dropped,
    /// and each stage does with it what its own job requires.
    pub proof: bool,
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- small builder helpers (test-only, keeps assertions readable) --

    fn ty(name: &str) -> Ty {
        Ty::Name(name.to_string())
    }

    fn param(name: &str, t: &str) -> Param {
        Param { name: name.to_string(), ty: ty(t), borrowed: false }
    }

    fn int(n: i64) -> Expr {
        Expr::IntLit(n)
    }

    fn var(name: &str) -> Expr {
        Expr::Var(name.to_string())
    }

    // --- Program ---------------------------------------------------

    #[test]
    fn program_holds_defs_in_order() {
        let p = Program::new(vec![
            Def::Fun(FunDef {
                universals: vec![],
                existentials: vec![],
            metric: vec![],
            ty_params: vec![],
                name: "f".into(),
                params: vec![],
                ret: ty("int"),
                body: int(1),
            }),
            Def::Implement(ImplementDef {
            ty_params: vec![],
            instance: vec![],
                name: "main0".into(),
                params: vec![],
                ret: None,
                body: int(1),
            }),
        ]);
        assert_eq!(p.defs().len(), 2);
        assert!(matches!(&p.defs()[0], Def::Fun(f) if f.name == "f"));
        assert!(matches!(&p.defs()[1], Def::Implement(i) if i.name == "main0"));
    }

    // --- Datatypes ------------------------------------------------

    #[test]
    fn datatype_def_carries_params_and_constructors() {
        let d = DatatypeDef {
            linear: false,
            name: "list".into(),
            ty_params: vec!["a".into()],
            ctors: vec![
                Ctor { name: "nil".into(), fields: vec![] },
                Ctor { name: "cons".into(), fields: vec![ty("a"), ty("list")] },
            ],
        };
        assert_eq!(d.name, "list");
        assert_eq!(d.ty_params, vec!["a"]);
        assert_eq!(d.ctors.len(), 2);
        assert_eq!(d.ctors[1].name, "cons");
        assert_eq!(d.ctors[1].fields, vec![ty("a"), ty("list")]);
    }

    // --- Functions ------------------------------------------------

    #[test]
    fn fun_def_carries_params_return_type_and_body() {
        let f = FunDef {
            universals: vec![],
            existentials: vec![],
            metric: vec![],
            ty_params: vec![],
            name: "add".into(),
            params: vec![param("x", "int"), param("y", "int")],
            ret: ty("int"),
            body: Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(var("y"))),
        };
        assert_eq!(f.params.len(), 2);
        assert_eq!(f.params[1].name, "y");
        assert_eq!(f.ret, ty("int"));
        assert!(matches!(
            f.body,
            Expr::BinOp(BinOp::Add, _, _)
        ));
    }

    #[test]
    fn implement_def_ret_is_optional() {
        let with_ret = ImplementDef {
            ty_params: vec![],
            instance: vec![],
            name: "f".into(),
            params: vec![],
            ret: Some(ty("int")),
            body: int(3),
        };
        let without_ret = ImplementDef {
            ty_params: vec![],
            instance: vec![],
            name: "main0".into(),
            params: vec![],
            ret: None,
            body: int(3),
        };
        assert_eq!(with_ret.ret, Some(ty("int")));
        assert_eq!(without_ret.ret, None);
    }

    // --- Types ----------------------------------------------------

    #[test]
    fn type_application_carries_a_name_and_arguments() {
        let applied = Ty::App("list".into(), vec![ty("a")]);
        assert_eq!(applied, Ty::App("list".into(), vec![Ty::Name("a".into())]));
        let nested = Ty::App("list".into(), vec![Ty::App("pair".into(), vec![ty("a"), ty("b")])]);
        assert!(matches!(nested, Ty::App(_, args) if args.len() == 1));
    }

    #[test]
    fn type_application_is_distinct_from_a_plain_name() {
        assert_ne!(Ty::App("list".into(), vec![]), ty("list"));
    }

    #[test]
    fn types_are_names_or_function_types() {
        let named = Ty::Name("bool".into());
        let fun_ty = Ty::Fun(vec![ty("int"), ty("int")], Box::new(ty("int")));
        assert_eq!(named, ty("bool"));
        assert!(matches!(fun_ty, Ty::Fun(args, ret) if args.len() == 2 && *ret == ty("int")));
    }

    // --- Expressions ----------------------------------------------

    #[test]
    fn every_expression_variant_is_constructible() {
        let exprs = vec![
            Expr::IntLit(1),
            Expr::BoolLit(true),
            Expr::StrLit("hi".into()),
            Expr::Var("x".into()),
            Expr::UnaryNeg(Box::new(int(1))),
            Expr::BinOp(BinOp::Add, Box::new(int(1)), Box::new(int(2))),
            Expr::Call(Box::new(var("f")), vec![int(1)]),
            Expr::IfThenElse(Box::new(Expr::BoolLit(true)), Box::new(int(1)), Box::new(int(2))),
            Expr::Let(vec![], Box::new(int(1))),
            Expr::Lam(vec![param("x", "int")], None, Box::new(var("x"))),
            Expr::MacroCall("println!".into(), vec![Expr::StrLit("hi".into())]),
            Expr::Uninit,
            Expr::RecordLit(vec![("x".into(), int(1))]),
            Expr::Field(Box::new(var("r")), "x".into()),
        ];
        assert_eq!(exprs.len(), 14);
        assert!(matches!(exprs[2], Expr::StrLit(ref s) if s == "hi"));
    }

    #[test]
    fn every_binop_variant_is_constructible() {
        let ops: Vec<BinOp> = vec![
            BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Mod,
            BinOp::Eq, BinOp::Ne, BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge,
            BinOp::Andalso, BinOp::Orelse,
        ];
        assert_eq!(ops.len(), 13);
        assert!(ops.iter().all(|o| *o != BinOp::Add || o == &BinOp::Add));
    }

    // --- patterns and case -----------------------------------------

    #[test]
    fn a_wildcard_pattern_binds_nothing() {
        assert!(Pattern::Wildcard.bound_names().is_empty());
    }

    #[test]
    fn a_variable_pattern_binds_its_name() {
        assert_eq!(Pattern::Var("x".into()).bound_names(), vec!["x".to_string()]);
    }

    #[test]
    fn a_constructor_pattern_binds_its_fields_in_order() {
        let p = Pattern::Ctor(
            "cons".into(),
            vec![Pattern::Var("x".into()), Pattern::Var("xs".into())],
        );
        assert_eq!(p.bound_names(), vec!["x".to_string(), "xs".to_string()]);
    }

    #[test]
    fn a_nested_pattern_binds_everything_it_reaches() {
        let p = Pattern::Ctor(
            "cons".into(),
            vec![
                Pattern::Ctor("some".into(), vec![Pattern::Var("v".into())]),
                Pattern::Wildcard,
            ],
        );
        assert_eq!(p.bound_names(), vec!["v".to_string()]);
    }

    #[test]
    fn a_case_expression_holds_a_scrutinee_and_its_arms() {
        let c = Expr::Case(
            Box::new(Expr::Var("xs".into())),
            vec![
                (Pattern::Ctor("nil".into(), vec![]), Expr::IntLit(0)),
                (Pattern::Var("other".into()), Expr::IntLit(1)),
            ],
        );
        let Expr::Case(scrutinee, arms) = &c else { panic!("expected a case") };
        assert_eq!(**scrutinee, Expr::Var("xs".into()));
        assert_eq!(arms.len(), 2);
    }

    // --- mutable state: `var`, `:=`, and the loop forms ------------

    #[test]
    fn a_let_bind_is_immutable_by_default() {
        // `val x = 1` binds a value; `var x = 1` binds a *cell*.
        let bind = LetBind { opened: Vec::new(), proof: false, name: Some("x".into()), ty: None, value: Expr::IntLit(1), mutable: false };
        assert!(!bind.mutable);
    }

    #[test]
    fn a_var_binding_is_marked_mutable() {
        let bind = LetBind { opened: Vec::new(), proof: false, name: Some("x".into()), ty: Some(ty("int")), value: Expr::IntLit(0), mutable: true };
        assert!(bind.mutable);
        assert_eq!(bind.name.as_deref(), Some("x"));
    }

    #[test]
    fn assignment_names_its_target_and_its_value() {
        let a = Expr::Assign("count".into(), Box::new(Expr::IntLit(7)));
        let Expr::Assign(name, value) = &a else { panic!("expected an assignment") };
        assert_eq!(name, "count");
        assert_eq!(**value, Expr::IntLit(7));
    }

    #[test]
    fn a_while_loop_holds_a_condition_and_a_body() {
        let w = Expr::While(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::MacroCall("println!".into(), vec![])),
        );
        let Expr::While(cond, body) = &w else { panic!("expected a while loop") };
        assert_eq!(**cond, Expr::BoolLit(true));
        assert_eq!(**body, Expr::MacroCall("println!".into(), vec![]));
    }

    #[test]
    fn a_for_loop_holds_its_three_clauses_and_a_body() {
        // `for (i := 0; i < 3; i := i + 1) body`
        let f = Expr::For(
            Box::new(Expr::Assign("i".into(), Box::new(Expr::IntLit(0)))),
            Box::new(Expr::BinOp(BinOp::Lt, Box::new(Expr::Var("i".into())), Box::new(Expr::IntLit(3)))),
            Box::new(Expr::Assign("i".into(), Box::new(Expr::IntLit(1)))),
            Box::new(Expr::Unit),
        );
        let Expr::For(init, cond, step, body) = &f else { panic!("expected a for loop") };
        assert_eq!(**init, Expr::Assign("i".into(), Box::new(Expr::IntLit(0))));
        assert!(matches!(**cond, Expr::BinOp(BinOp::Lt, _, _)));
        assert_eq!(**step, Expr::Assign("i".into(), Box::new(Expr::IntLit(1))));
        assert_eq!(**body, Expr::Unit);
    }

    #[test]
    fn let_bind_can_be_a_discard() {
        // `val () = println!(...)` — a binding with no name.
        let bind = LetBind {
            opened: Vec::new(),
            proof: false,
            name: None,
            ty: None,
            value: Expr::MacroCall("println!".into(), vec![]),
            mutable: false,
        };
        assert_eq!(bind.name, None);
    }

    #[test]
    fn ast_is_cloneable_and_comparable() {
        let a = Program::new(vec![Def::Fun(FunDef {
            universals: vec![],
            existentials: vec![],
            metric: vec![],
            ty_params: vec![],
            name: "f".into(),
            params: vec![],
            ret: ty("int"),
            body: int(1),
        })]);
        let b = a.clone();
        assert_eq!(a, b);
        assert_eq!(a.defs(), b.defs());
    }

    // --- A realistic mini-program ---------------------------------

    #[test]
    fn builds_the_factorial_program() {
        let program = Program::new(vec![
            Def::Fun(FunDef {
                universals: vec![],
                existentials: vec![],
            metric: vec![],
            ty_params: vec![],
                name: "fact".into(),
                params: vec![param("n", "int")],
                ret: ty("int"),
                body: Expr::IfThenElse(
                    Box::new(Expr::BinOp(BinOp::Eq, Box::new(var("n")), Box::new(int(0)))),
                    Box::new(int(1)),
                    Box::new(Expr::BinOp(
                        BinOp::Mul,
                        Box::new(var("n")),
                        Box::new(Expr::Call(Box::new(var("fact")), vec![
                            Expr::BinOp(BinOp::Sub, Box::new(var("n")), Box::new(int(1))),
                        ])),
                    )),
                ),
            }),
            Def::Implement(ImplementDef {
            ty_params: vec![],
            instance: vec![],
                name: "main0".into(),
                params: vec![],
                ret: None,
                body: Expr::MacroCall(
                    "println!".into(),
                    vec![Expr::StrLit("fact(5) = ".into()), Expr::Call(Box::new(var("fact")), vec![int(5)])],
                ),
            }),
        ]);
        assert_eq!(program.defs().len(), 2);
        let Def::Fun(fact) = &program.defs()[0] else { panic!("expected fun") };
        assert_eq!(fact.name, "fact");
        assert_eq!(fact.params[0].name, "n");
    }
}
