//! # ats2-infrastructure — every concrete mechanism
//!
//! *Literate note.*  Here live the real lexer, parser and LLVM IR emitter
//! together with the adapters that satisfy the application-layer ports and
//! the CLI controller.  This is the only crate allowed to touch `std::fs`,
//! `std::io`, `std::process` and platform tools.  Domain data flows in and
//! out; no domain file ever learns where it came from.

pub mod adapters;
pub mod cli;
pub mod diagnostics;
pub mod infer;
pub mod io;
pub mod lexer;
pub mod lift;
pub mod llvm_ir;
pub mod mono;
pub mod parser;
pub mod prelude;
pub mod toolchain;
