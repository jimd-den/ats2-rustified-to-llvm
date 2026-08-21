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

pub mod ast;
pub mod errors;
pub mod obligation;
pub mod statics;
pub mod tokens;

/// The C that realises the exception runtime, linked beside the IR.
///
/// A `try`/`$raise` in ATS lowers to a setjmp/longjmp pair across
/// function calls, which only real C implements reliably (LLVM's own IR
/// does not lower a plain `setjmp`/`longjmp` call the way throwing
/// across frames needs).  So this text is written to the `.c` that sits
/// beside the module, and the IR calls into it.  It is pure data here;
/// nothing in the domain depends on what it says.
pub fn exception_runtime_c() -> &'static str {
    r#"#include <setjmp.h>
typedef struct ats2_exf { jmp_buf jb; void *parent; void *exn; } ats2_exf;
static ats2_exf *ats2_excur = 0;
static void *ats2_exval = 0;
int ats2_try_begin(ats2_exf *f) { f->parent = ats2_excur; f->exn = 0; ats2_excur = f; return setjmp(f->jb); }
void ats2_try_end(ats2_exf *f) { ats2_excur = f->parent; }
void ats2_throw(void *e) { ats2_exval = e; if (ats2_excur) longjmp(ats2_excur->jb, 1); }
void *ats2_caught(void) { return ats2_exval; }
"#
}

