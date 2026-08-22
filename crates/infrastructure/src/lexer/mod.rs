use ats2_domain::errors::CompileError;
use ats2_domain::tokens::Token;

pub mod keywords;
pub mod numbers;
pub mod scanner;
pub mod strings;

#[cfg(test)]
mod tests;

pub use numbers::float_bits;
pub use scanner::Scanner;

/// A stateless lexer. `lex` is a pure function of the source text.
pub struct Lexer;

impl Lexer {
    /// Carve `source` into a token stream (terminated by exactly one
    /// `Eof`), or report every lexing error that was found.
    pub fn lex(source: &str) -> Result<Vec<Token>, Vec<CompileError>> {
        let mut scanner = Scanner::new(source);
        scanner.scan_all();
        if scanner.errors.is_empty() {
            Ok(scanner.tokens)
        } else {
            Err(scanner.errors)
        }
    }
}
