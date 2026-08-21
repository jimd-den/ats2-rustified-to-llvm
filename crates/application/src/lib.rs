//! # ats2-application — the use cases and their ports
//!
//! *Literate note.*  This crate is the *screaming* part of the screaming
//! architecture: read its module list and you learn what the software
//! *does* (parse ATS2, compile to LLVM IR, link an executable) rather than
//! what framework it uses.  The use cases orchestrate; every external
//! effect — reading a file, running clang, printing diagnostics — is
//! reached exclusively through abstract **port** traits defined here, so
//! the application layer can be tested with tiny in-memory fakes.

pub mod checking;
pub mod constraints;
pub mod elaboration;
pub mod linearity;
pub mod modules;
pub mod ports;
pub mod use_cases;
