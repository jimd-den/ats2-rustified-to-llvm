//! # ats2-infrastructure::prelude — ambient standard library
//!
//! *Literate note.*  Provides ambient static props, runtime functions, and
//! canonical type mappings that form the standard ATS2 prelude environment.

pub mod runtime;
pub mod statics;
pub mod types;

pub use runtime::PRELUDE_SOURCE;
pub use statics::PRELUDE_STATIC_SOURCE;
pub use types::*;
