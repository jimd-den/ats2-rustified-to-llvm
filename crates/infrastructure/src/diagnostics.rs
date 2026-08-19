//! # Diagnostics adapter — errors reach a human
//!
//! *Literate note.*  The domain formats errors; this adapter *presents*
//! them.  It owns nothing but a `std::io::Stderr` handle, so swapping it
//! for a logger or an IDE channel never disturbs the application layer.

use ats2_domain::errors::CompileError;

use ats2_application::ports::DiagnosticsPort;

/// Prints errors and info lines to standard error.
pub struct StderrDiagnostics;

impl StderrDiagnostics {
    pub fn new() -> Self {
        Self
    }
}

impl DiagnosticsPort for StderrDiagnostics {
    fn report_errors(&self, errors: &[CompileError]) {
        for error in errors {
            eprintln!("{error}");
        }
    }

    fn info(&self, message: &str) {
        eprintln!("{message}");
    }
}
