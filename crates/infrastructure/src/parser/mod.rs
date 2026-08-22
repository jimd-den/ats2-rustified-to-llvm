use ats2_domain::ast::Program;
use ats2_domain::errors::CompileError;
use ats2_domain::tokens::{Pos, Span, Token, TokenKind};

use crate::lexer::Lexer;

pub mod context;
pub mod decode;
pub mod expr;
pub mod patterns;
pub mod toplevel;
pub mod types;

#[cfg(test)]
mod tests;

pub use context::TOPLEVEL_STATEMENT;
use context::ParseCtx;

/// A stateless parser: `parse` turns source text straight into a program.
pub struct Parser;

impl Parser {
    /// Lex and parse `source`.  Returns the program or the first error
    /// encountered (fail-fast; collecting *all* parse errors is a later
    /// iteration).
    pub fn parse(source: &str) -> Result<Program, Vec<CompileError>> {
        let tokens = Lexer::lex(source)?;
        Self::parse_tokens(&tokens)
    }

    /// Parse a dependency while retaining complete declarations before the
    /// first unsupported top-level form.  Lexing remains strict because no
    /// trustworthy token prefix exists when tokenization itself fails.
    pub fn parse_dependency(source: &str) -> Result<Program, Vec<CompileError>> {
        let tokens = Lexer::lex(source)?;
        Self::parse_dependency_tokens(&tokens)
    }

    /// Parse a token stream (e.g. one produced by the lexer in tests).
    pub fn parse_tokens(tokens: &[Token]) -> Result<Program, Vec<CompileError>> {
        if tokens.is_empty() {
            let span = Span::new(Pos::new(1, 1, 0), Pos::new(1, 1, 0));
            return Err(vec![CompileError::parse(
                span,
                "empty token stream (missing EOF)",
            )]);
        }
        let mut ctx = ParseCtx::new(tokens);
        ctx.parse_program()
    }

    fn parse_dependency_tokens(tokens: &[Token]) -> Result<Program, Vec<CompileError>> {
        if tokens.is_empty() {
            let span = Span::new(Pos::new(1, 1, 0), Pos::new(1, 1, 0));
            return Err(vec![CompileError::parse(
                span,
                "empty token stream (missing EOF)",
            )]);
        }
        Ok(ParseCtx::new(tokens).parse_available_program())
    }
}
