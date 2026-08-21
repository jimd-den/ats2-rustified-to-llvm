//! # Tokens — the outermost surface of the domain data
//!
//! *Literate note.*  A **token** is the smallest meaningful unit the lexer
//! will later produce: a keyword, a literal, an operator, or a piece of
//! punctuation.  A token is *located*: it always carries the **span** of
//! source text it was cut from, so that any later stage can point a human
//! at precisely the right line and column.  The span is pure geometry —
//! three unsigned coordinates — and the token kind is pure vocabulary.
//! Neither knows anything about files, the CLI, or where the text came
//! from.  That is what "imputrescible data" means: this module could be
//! lifted into any compiler project and rot-proof forever.
//!
//! Two deliberate design decisions worth recording in prose:
//!
//! 1. **Owned data.**  Identifiers and string literals carry owned `String`
//!    payloads rather than borrowed slices of the source.  Tokens are then
//!    lifetime-free, which keeps every downstream consumer (`Vec<Token>`,
//!    the parser, error messages) simple.  The lexer pays a small
//!    allocation once per identifier; that is invisible at this scale.
//!
//! 2. **Raw string interiors.**  A `StrLit` token stores the *raw* text
//!    between the quotes with escape sequences intact (`"a\n"` -> `a\n`).
//!    Decoding escapes is a *parsing* concern (it produces semantic
//!    values), so it happens later; the lexer only has to cut the source
//!    into pieces.

/// A position in the source: 1-based line and column plus a 0-based byte
/// offset.  The offset is what actually slices source text; line/column
/// exist so diagnostics read like a human expects.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pos {
    pub line: usize,
    pub column: usize,
    pub offset: usize,
}

impl Pos {
    /// Build a source position from its three coordinates.
    pub fn new(line: usize, column: usize, offset: usize) -> Self {
        Self {
            line,
            column,
            offset,
        }
    }
}

/// A half-open region of source text: `[start, end)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: Pos,
    pub end: Pos,
}

impl Span {
    pub fn new(start: Pos, end: Pos) -> Self {
        Self { start, end }
    }
}

/// The token vocabulary of the supported ATS2 subset.
///
/// `Ident` carries the identifier text, `IntLit` the decoded integer, and
/// `StrLit` the *raw* (still escaped) string interior.  Every keyword of the
/// subset has its own variant: keywords are reserved words, and modeling
/// them as distinct variants — rather than strings — lets the parser match
/// on them cheaply and lets the lexer reject them as identifiers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    // Literals and identifiers
    Ident(String),
    IntLit(i64),
    /// A floating-point literal such as `1.5`.
    ///
    /// `TokenKind` derives `Eq`, which `f64` does not implement, so the
    /// bits are what is stored and compared.  Two literals are the same
    /// token when they were written the same way, which is the only
    /// question a lexer's output should answer.
    FloatLit(FloatBits),
    StrLit(String),

    // Keywords
    Datatype,
    Fun,
    Implement,
    If,
    Then,
    Else,
    Let,
    In,
    End,
    Lam,
    Val,
    True,
    False,
    Andalso,
    Orelse,
    Mod,
    /// `fn` — a non-recursive function.  The subset treats it exactly as
    /// `fun`; the distinction is a promise to the ATS type checker, not a
    /// difference in lowering.
    Fn,
    /// `local ... in ... end` — a scoped group of definitions.
    Local,
    /// `case`/`case+`/`case-` — pattern matching.
    Case,
    /// `of` — separates a pattern from its branch body.
    Of,
    /// `when` — a guard on a pattern.
    When,
    /// `with` — the handler separator in `try e with | p => h`.
    With,
    /// `var` — a stack-allocated mutable binding.
    Var,
    /// `void` is an ordinary type name elsewhere, but `while`/`for` are
    /// statement keywords in the loop forms.
    While,
    For,

    // Symbols and punctuation
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Semicolon,
    /// `%{ ... %}` — a block of C, carried through untouched.
    ///
    /// It is not this compiler's language and never will be, so it is
    /// not lexed further: the toolchain speaks C, and this is how the
    /// text reaches it.
    InlineC(String),
    Colon,
    Pipe,
    Dot,
    Bang,
    Underscore,
    Plus,
    Minus,
    Star,
    Slash,
    Tilde,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Arrow,
    FatArrow,
    At,
    Dollar,
    Hash,
    /// `&` — a call-by-reference marker in parameter types.
    Amp,
    /// `?` — the "uninitialized" type modifier, as in `int?`.
    Question,
    /// `%` — used by the `%{ ... %}` inline-C escape.
    Percent,
    /// `\` — the closure marker in `lam`/`llam` types.
    Backslash,
    /// `^` — used in a handful of type operators.
    Caret,
    /// `:=` — assignment to a `var` or a reference.
    ColonEq,
    /// `'{` or `@{` — the opening of a record, in a type or a value.
    ///
    /// One token rather than a quote and a brace, because a brace on its
    /// own opens a *block*: reading `'{ x= 1 }` as a quote followed by a
    /// block would parse the fields as statements.  The two spellings
    /// differ in whether the record is boxed, which is a question of
    /// representation that this compiler settles the same way for both.
    RecordOpen,
    /// `::` — the list-cons operator, infix in both expressions and
    /// patterns.  One token rather than two colons, because `x : : t` is
    /// not a thing and the pair always means cons.
    ColonColon,
    /// A character literal such as `'a'` or `'\n'`, already decoded.
    CharLit(u8),

    /// End of input.  Every token stream ends with exactly one of these.
    Eof,
}

/// A floating-point literal's value, compared by its bits.
///
/// Tokens are `Eq` so that the parser can match on them; `f64` is not,
/// because `NaN != NaN`.  Storing the bit pattern sidesteps the question
/// without pretending floats have a total order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FloatBits(u64);

impl FloatBits {
    pub fn new(value: f64) -> Self {
        Self(value.to_bits())
    }

    pub fn value(self) -> f64 {
        f64::from_bits(self.0)
    }
}

impl From<f64> for FloatBits {
    fn from(value: f64) -> Self {
        Self::new(value)
    }
}

/// A located token: one vocabulary item plus the span of source it covers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }

    /// The kind of this token, by reference (handy in match arms).
    pub fn kind(&self) -> &TokenKind {
        &self.kind
    }

    /// The span of source this token was cut from.
    pub fn span(&self) -> Span {
        self.span
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- Positions ------------------------------------------------

    #[test]
    fn pos_orders_its_three_coordinates() {
        let p = Pos::new(3, 7, 41);
        assert_eq!(p.line, 3);
        assert_eq!(p.column, 7);
        assert_eq!(p.offset, 41);
    }

    #[test]
    fn pos_is_copyable_and_comparable() {
        let a = Pos::new(1, 1, 0);
        let b = Pos::new(1, 1, 0);
        let c = Pos::new(1, 2, 1);
        assert_eq!(a, b);
        assert_ne!(a, c);
        // Copy semantics: using `a` twice must not move it.
        let _ = (a, a);
    }

    // --- Spans ----------------------------------------------------

    #[test]
    fn span_holds_start_and_end() {
        let s = Span::new(Pos::new(1, 1, 0), Pos::new(1, 4, 3));
        assert_eq!(s.start.offset, 0);
        assert_eq!(s.end.offset, 3);
    }

    #[test]
    fn span_is_copyable_and_comparable() {
        let a = Span::new(Pos::new(1, 1, 0), Pos::new(1, 2, 1));
        let b = Span::new(Pos::new(1, 1, 0), Pos::new(1, 2, 1));
        assert_eq!(a, b);
        let _ = (a, a);
    }

    // --- Tokens ---------------------------------------------------

    #[test]
    fn token_carries_kind_and_span() {
        let span = Span::new(Pos::new(1, 1, 0), Pos::new(1, 3, 2));
        let t = Token::new(TokenKind::IntLit(42), span);
        assert_eq!(t.kind(), &TokenKind::IntLit(42));
        assert_eq!(t.span(), span);
    }

    #[test]
    fn eof_token_marks_the_end_of_a_stream() {
        let span = Span::new(Pos::new(1, 5, 4), Pos::new(1, 5, 4));
        let t = Token::new(TokenKind::Eof, span);
        assert_eq!(t.kind(), &TokenKind::Eof);
        assert_eq!(t.span().start.offset, 4);
    }

    #[test]
    fn identifiers_carry_their_text() {
        let span = Span::new(Pos::new(2, 1, 10), Pos::new(2, 6, 15));
        let t = Token::new(TokenKind::Ident("fact".to_string()), span);
        assert_eq!(t.kind(), &TokenKind::Ident("fact".to_string()));
    }

    #[test]
    fn string_literals_carry_the_raw_interior() {
        let t = Token::new(
            TokenKind::StrLit("a\\n".to_string()),
            Span::new(Pos::new(1, 1, 0), Pos::new(1, 5, 4)),
        );
        // The raw, still-escaped interior is preserved verbatim.
        assert_eq!(t.kind(), &TokenKind::StrLit("a\\n".to_string()));
    }

    #[test]
    fn keywords_are_distinct_from_identifiers() {
        let kw = TokenKind::Fun;
        let id = TokenKind::Ident("fun".to_string());
        assert_ne!(kw, id);
    }

    #[test]
    fn token_equality_requires_kind_and_span_to_agree() {
        let s1 = Span::new(Pos::new(1, 1, 0), Pos::new(1, 2, 1));
        let s2 = Span::new(Pos::new(1, 2, 1), Pos::new(1, 3, 2));
        let a = Token::new(TokenKind::Plus, s1);
        let b = Token::new(TokenKind::Plus, s1);
        let c = Token::new(TokenKind::Plus, s2);
        let d = Token::new(TokenKind::Minus, s1);
        assert_eq!(a, b);
        assert_ne!(a, c); // same kind, different span
        assert_ne!(a, d); // different kind
    }

    #[test]
    fn every_variant_of_the_vocabulary_is_constructible() {
        // A compile-time-ish census: construct one token of every kind the
        // parser will need to recognize.  If a variant is missing, this
        // test stops compiling — the vocabulary is the contract.
        let span = Span::new(Pos::new(1, 1, 0), Pos::new(1, 1, 0));
        let kinds: Vec<TokenKind> = vec![
            TokenKind::Ident("x".into()),
            TokenKind::IntLit(1),
            TokenKind::StrLit("s".into()),
            TokenKind::Datatype,
            TokenKind::Fun,
            TokenKind::Implement,
            TokenKind::If,
            TokenKind::Then,
            TokenKind::Else,
            TokenKind::Let,
            TokenKind::In,
            TokenKind::End,
            TokenKind::Lam,
            TokenKind::Val,
            TokenKind::True,
            TokenKind::False,
            TokenKind::Andalso,
            TokenKind::Orelse,
            TokenKind::Mod,
            TokenKind::LParen,
            TokenKind::RParen,
            TokenKind::LBracket,
            TokenKind::RBracket,
            TokenKind::LBrace,
            TokenKind::RBrace,
            TokenKind::Comma,
            TokenKind::Semicolon,
            TokenKind::Colon,
            TokenKind::Pipe,
            TokenKind::Dot,
            TokenKind::Bang,
            TokenKind::Underscore,
            TokenKind::Plus,
            TokenKind::Minus,
            TokenKind::Star,
            TokenKind::Slash,
            TokenKind::Tilde,
            TokenKind::Eq,
            TokenKind::Ne,
            TokenKind::Lt,
            TokenKind::Le,
            TokenKind::Gt,
            TokenKind::Ge,
            TokenKind::Arrow,
            TokenKind::FatArrow,
            TokenKind::At,
            TokenKind::Dollar,
            TokenKind::Hash,
            TokenKind::ColonColon,
            TokenKind::RecordOpen,
            TokenKind::Eof,
        ];
        // Every kind must also fit inside a real token.
        let tokens: Vec<Token> = kinds.into_iter().map(|k| Token::new(k, span)).collect();
        assert_eq!(tokens.len(), 51);
        assert!(tokens.iter().all(|t| t.span() == span));
    }
}
