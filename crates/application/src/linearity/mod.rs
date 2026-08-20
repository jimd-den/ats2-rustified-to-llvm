//! # The linear language — whose a value is, and for how long
//!
//! *Literate note.*  ATS is two disciplines.  [`crate::checking`] reads
//! the first: what a value *is*, said in indices and decided by
//! arithmetic.  This one reads the second: a `datavtype` value is a
//! *resource*, and must be consumed exactly once.  Used twice it is a
//! use-after-free; never used it is a leak.
//!
//! They are separate modules because they are separate questions, and
//! nothing either one knows helps the other: no amount of arithmetic
//! says whether a list was freed twice, and no ledger says whether an
//! index is in range.  Keeping them apart is what lets the resource
//! check be a hundred lines of accounting rather than a second solver.
//!
//! The shape is the same as its neighbour's, because the shape was right:
//! [`walk`] finds faults and knows nothing about diagnostics,
//! [`resources`] keeps the ledger and knows nothing about programs, and
//! this module turns what they found into what a reader sees.

pub mod resources;
pub mod walk;

use ats2_domain::ast::Program;
use ats2_domain::errors::{CompileError, ErrorKind};

/// Check a program's resource discipline, and report what it broke.
///
/// `ambient` supplies the declarations the program did not write — which
/// types are linear, and which parameters are lent rather than given.
pub fn check_linearity(program: &Program, ambient: &Program) -> Vec<CompileError> {
    let mut out: Vec<CompileError> = Vec::new();
    for fault in walk::faults(program, ambient) {
        let error = CompileError {
            kind: ErrorKind::Linear,
            span: None,
            message: fault.describe(),
        };
        // One walk can reach the same mistake by two routes; the reader
        // wants it once.
        if !out.contains(&error) {
            out.push(error);
        }
    }
    out
}
