//! # Compile errors — the third family of imputrescible data
//!
//! *Literate note.*  Errors in this design are **data**, not behavior: a
//! compile error is a kind, an optional source span, and a message.  It
//! knows where something went wrong and what went wrong, but it has no idea
//! how to *report* itself — printing is a presentation concern owned by the
//! outer layers.  This is what lets the application layer test whole error
//! paths with in-memory fakes: errors are just values flowing through the
//! pipeline.
//!
//! Four kinds cover every stage of the pipeline:
//!
//! * `Lex`   — the lexer could not carve the source into tokens;
//! * `Parse` — the tokens do not form a valid program;
//! * `Emit`  — the AST could not be lowered to LLVM IR (unsupported
//!   construct, ill-typed shape, …);
//! * `Target`— an external target failed (the toolchain, a file write, …).
//!
//! The last kind is the only one that hints at the outside world, and even
//! it stays abstract: the domain records that *some* target failed and why,
//! never which one or how.

use crate::tokens::Span;

/// The pipeline stage an error belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorKind {
    Lex,
    Parse,
    Emit,
    /// A promise the static language made and the program broke: a call
    /// whose arguments the callee's quantifiers exclude.  Distinct from
    /// `Emit` because nothing is wrong with the *shape* of the program —
    /// it would lower perfectly well, and be wrong.
    Check,
    /// A resource discipline the program did not keep: a linear value
    /// given away twice, or never given away at all.
    ///
    /// Distinct from `Check` because it is a different accusation.  A
    /// `Check` error says the program computes something it promised not
    /// to; this one says the program is wrong about *ownership*, which
    /// no amount of arithmetic would ever have revealed.
    Linear,
    Target,
}

/// A located or location-less compile error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompileError {
    pub kind: ErrorKind,
    pub span: Option<Span>,
    pub message: String,
}

impl CompileError {
    /// A lexing failure at the given span.
    pub fn lex(span: Span, message: impl Into<String>) -> Self {
        Self {
            kind: ErrorKind::Lex,
            span: Some(span),
            message: message.into(),
        }
    }

    /// A parsing failure at the given span.
    pub fn parse(span: Span, message: impl Into<String>) -> Self {
        Self {
            kind: ErrorKind::Parse,
            span: Some(span),
            message: message.into(),
        }
    }

    /// A lowering failure.  Emission errors usually have no useful span
    /// (the problem is a shape of the whole AST), so they carry none.
    pub fn emit(message: impl Into<String>) -> Self {
        Self {
            kind: ErrorKind::Emit,
            span: None,
            message: message.into(),
        }
    }

    /// A constraint the program does not satisfy.
    pub fn check(message: impl Into<String>) -> Self {
        Self {
            kind: ErrorKind::Check,
            span: None,
            message: message.into(),
        }
    }

    /// A resource the program did not account for.
    pub fn linear(message: impl Into<String>) -> Self {
        Self {
            kind: ErrorKind::Linear,
            span: None,
            message: message.into(),
        }
    }

    /// A failure reported by an external target.
    pub fn target(message: impl Into<String>) -> Self {
        Self {
            kind: ErrorKind::Target,
            span: None,
            message: message.into(),
        }
    }

    /// The stage this error belongs to.
    pub fn kind(&self) -> ErrorKind {
        self.kind
    }

    /// The source span this error points at, if any.
    pub fn span(&self) -> Option<Span> {
        self.span
    }

    /// The human-readable explanation.
    pub fn message(&self) -> &str {
        &self.message
    }
}

/// Errors render themselves as `"<kind> error at <line>:<column>: <message>"`.
/// Rendering here is pure string formatting — presentation infrastructure
/// (stderr, colors, exit codes) still belongs to the outer layers.
impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let stage = match self.kind {
            ErrorKind::Lex => "lex error",
            ErrorKind::Parse => "parse error",
            ErrorKind::Emit => "emit error",
            ErrorKind::Check => "constraint error",
            ErrorKind::Linear => "resource error",
            ErrorKind::Target => "target error",
        };
        match self.span {
            Some(s) => write!(
                f,
                "{stage} at {}:{}: {}",
                s.start.line, s.start.column, self.message
            ),
            None => write!(f, "{stage}: {}", self.message),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tokens::{Pos, Span};

    fn span() -> Span {
        Span::new(Pos::new(3, 7, 20), Pos::new(3, 11, 24))
    }

    #[test]
    fn lex_errors_carry_kind_span_and_message() {
        let e = CompileError::lex(span(), "unterminated string literal");
        assert_eq!(e.kind(), ErrorKind::Lex);
        assert_eq!(e.span(), Some(span()));
        assert_eq!(e.message(), "unterminated string literal");
    }

    #[test]
    fn parse_errors_carry_kind_span_and_message() {
        let e = CompileError::parse(span(), "expected `then`");
        assert_eq!(e.kind(), ErrorKind::Parse);
        assert_eq!(e.span().unwrap().start.offset, 20);
        assert_eq!(e.message(), "expected `then`");
    }

    #[test]
    fn emit_errors_carry_no_span() {
        let e = CompileError::emit("unsupported type `list`");
        assert_eq!(e.kind(), ErrorKind::Emit);
        assert_eq!(e.span(), None);
        assert_eq!(e.message(), "unsupported type `list`");
    }

    #[test]
    fn target_errors_carry_no_span() {
        let e = CompileError::target("clang exited with status 1");
        assert_eq!(e.kind(), ErrorKind::Target);
        assert_eq!(e.span(), None);
    }

    #[test]
    fn messages_accept_owned_as_well_as_borrowed_strings() {
        let owned = CompileError::parse(span(), String::from("msg"));
        let borrowed = CompileError::parse(span(), "msg");
        assert_eq!(owned, borrowed);
    }

    #[test]
    fn display_includes_kind_and_location() {
        let e = CompileError::lex(span(), "bad character `@`");
        let text = format!("{e}");
        assert!(text.contains("lex error"), "got: {text}");
        assert!(text.contains("3:7"), "got: {text}");
        // The message text itself is preserved verbatim.
        assert!(text.contains("bad character `@`"), "got: {text}");
    }

    #[test]
    fn display_without_span_omits_the_location() {
        let e = CompileError::emit("unsupported type `list`");
        let text = format!("{e}");
        assert_eq!(text, "emit error: unsupported type `list`");
    }

    #[test]
    fn errors_are_cloneable_and_comparable() {
        let a = CompileError::parse(span(), "expected `then`");
        let b = CompileError::parse(span(), "expected `then`");
        let c = CompileError::parse(span(), "expected `else`");
        assert_eq!(a.clone(), b);
        assert_ne!(a, c);
    }
}
