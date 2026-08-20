//! # ats2-domain — the imputrescible core
//!
//! *Literate note.*  This crate is the innermost ring of the clean
//! architecture.  It contains the three pure data families the whole
//! compiler reasons about — **tokens**, the **abstract syntax tree**, and
//! **compile errors** — and nothing else.  There is deliberately no I/O
//! here, no CLI vocabulary, no mention of LLVM or any compilation target,
//! and (in `Cargo.toml`) not a single dependency.  The domain cannot rot
//! because it has nothing to depend on, and it cannot be coerced into
//! knowing about the outside world because the dependency rule forbids the
//! outer crates it would need to import.
//!
//! The compilation *process* lives in the application layer; the domain
//! only describes the *data* that process consumes and produces.

pub mod tokens;
pub mod errors;
pub mod ast;
pub mod statics;
pub mod obligation;
