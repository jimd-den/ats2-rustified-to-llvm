use ats2_domain::errors::CompileError;
use ats2_domain::tokens::{FloatBits, Pos, Span, Token, TokenKind};

/// A stateless lexer.  `lex` is a pure function of the source text.
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

/// The scanning state: position bookkeeping plus the two output buffers
/// (tokens and errors).  All positions are byte offsets; line/column are
/// maintained as characters pass under the cursor.
struct Scanner<'a> {
    src: &'a str,
    pos: usize,
    line: usize,
    col: usize,
    tokens: Vec<Token>,
    errors: Vec<CompileError>,
}

impl<'a> Scanner<'a> {
    fn new(src: &'a str) -> Self {
        Self {
            src,
            pos: 0,
            line: 1,
            col: 1,
            tokens: Vec::new(),
            errors: Vec::new(),
        }
    }

    /// The character at the cursor, if any.
    fn peek(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }

    /// The character after the cursor, if any.
    fn peek2(&self) -> Option<char> {
        let mut it = self.src[self.pos..].chars();
        it.next();
        it.next()
    }

    /// Advance the cursor by one character, maintaining line/column.
    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += c.len_utf8();
        if c == '\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        Some(c)
    }

    /// The position at the cursor.
    fn pos(&self) -> Pos {
        Pos::new(self.line, self.col, self.pos)
    }

    /// A span from a previously captured start to the cursor.
    fn span_from(&self, start: Pos) -> Span {
        Span::new(start, self.pos())
    }

    /// Record a lex error at a span.
    fn error(&mut self, span: Span, message: impl Into<String>) {
        self.errors.push(CompileError::lex(span, message));
    }

    /// Emit a token spanning from `start` to the cursor.
    fn push(&mut self, kind: TokenKind, start: Pos) {
        self.tokens.push(Token::new(kind, self.span_from(start)));
    }

    /// Lex the whole source.  Trivia is skipped until a real token or EOF.
    fn scan_all(&mut self) {
        loop {
            self.skip_trivia();
            let start = self.pos();
            let Some(c) = self.peek() else {
                self.tokens
                    .push(Token::new(TokenKind::Eof, Span::new(start, start)));
                return;
            };
            self.scan_token(c, start);
        }
    }

    /// Dispatch one token by its first character.  Two-character
    /// operators that share a first character are matched here; everything
    /// single-character falls through to `scan_simple`.
    fn scan_token(&mut self, c: char, start: Pos) {
        match c {
            'a'..='z' | 'A'..='Z' | '_' => self.scan_identifier(start),
            // `$break`, `$UN`, `$delay`: in ATS the `$` opens a name.
            '$' if self
                .peek2()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_') =>
            {
                self.bump();
                self.scan_identifier(start)
            }
            '0'..='9' => self.scan_number(start),
            '"' => self.scan_string(start),
            '(' if self.peek2() == Some('*') => self.skip_block_comment(start),
            // `%{ ... %}` — a block of C, which ATS hands straight to
            // the C compiler.  This compiler emits LLVM IR and never
            // runs one, so there is nothing to do with the block; the
            // point of recognising it here is that it must not be
            // *lexed* either.  Its braces, quotes and `/*` are C's, and
            // reading them as ATS turns a well-formed program into a
            // syntax error.  The opener has several spellings — `%{^`
            // puts the code above the output, `%{$` below — and all of
            // them end at `%}`.
            '%' if self.peek2() == Some('{') => self.skip_inline_c(start),
            '-' if self.peek2() == Some('>') => {
                self.bump();
                self.bump();
                self.push(TokenKind::Arrow, start);
            }
            // `==` is how the static language spells equality: `{n:int |
            // i+j == n-1}`.  It is the same relation `=` already means in
            // an expression, so it collapses to the same token — and it
            // has to, because two `=` in a row parse as an equality
            // whose right-hand side is another `=`, which is no
            // expression at all.  Losing that costs the *whole*
            // quantifier, sorts included.
            '=' if self.peek2() == Some('=') => {
                self.bump();
                self.bump();
                self.push(TokenKind::Eq, start);
            }
            '<' if self.peek2() == Some('=') => {
                self.bump();
                self.bump();
                self.push(TokenKind::Le, start);
            }
            '<' if self.peek2() == Some('>') => {
                self.bump();
                self.bump();
                self.push(TokenKind::Ne, start);
            }
            // ATS spells "not equal" both ways.  `!` is otherwise a
            // prefix (dereference) or a macro marker, and neither can be
            // followed by `=`, so there is nothing to disambiguate.
            '!' if self.peek2() == Some('=') => {
                self.bump();
                self.bump();
                self.push(TokenKind::Ne, start);
            }
            '>' if self.peek2() == Some('=') => {
                self.bump();
                self.bump();
                self.push(TokenKind::Ge, start);
            }
            '=' if self.peek2() == Some('>') => {
                self.bump();
                self.bump();
                self.push(TokenKind::FatArrow, start);
            }
            ':' if self.peek2() == Some(':') => {
                self.bump();
                self.bump();
                self.push(TokenKind::ColonColon, start);
            }
            ':' if self.peek2() == Some('=') => {
                self.bump();
                self.bump();
                self.push(TokenKind::ColonEq, start);
            }
            // `'{` and `@{` open a record.  Recognised here because the
            // brace alone means something else entirely.
            '\'' | '@' if self.peek2() == Some('{') => {
                self.bump();
                self.bump();
                self.push(TokenKind::RecordOpen, start);
            }
            '\'' => self.scan_char(start),
            _ => self.scan_simple(c, start),
        }
    }

    /// Every one-character token, mapped from its character.  Unknown
    /// characters are reported as lex errors.
    fn scan_simple(&mut self, c: char, start: Pos) {
        let kind = match c {
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '*' => TokenKind::Star,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            ',' => TokenKind::Comma,
            ';' => TokenKind::Semicolon,
            ':' => TokenKind::Colon,
            '|' => TokenKind::Pipe,
            '.' => TokenKind::Dot,
            '!' => TokenKind::Bang,
            '~' => TokenKind::Tilde,
            '+' => TokenKind::Plus,
            '-' => TokenKind::Minus,
            '/' => TokenKind::Slash,
            '<' => TokenKind::Lt,
            '>' => TokenKind::Gt,
            '=' => TokenKind::Eq,
            '&' => TokenKind::Amp,
            '?' => TokenKind::Question,
            '%' => TokenKind::Percent,
            '\\' => TokenKind::Backslash,
            '^' => TokenKind::Caret,
            '@' => TokenKind::At,
            '$' => TokenKind::Dollar,
            '#' => TokenKind::Hash,
            _ => {
                self.bump();
                self.error(
                    Span::new(start, self.pos()),
                    format!("unexpected character `{c}`"),
                );
                return;
            }
        };
        self.bump();
        self.push(kind, start);
    }

    /// Skip whitespace, line comments, and (nested) block comments.
    fn skip_trivia(&mut self) {
        loop {
            match self.peek() {
                Some(' ') | Some('\t') | Some('\r') | Some('\n') => {
                    self.bump();
                }
                Some('/') if self.peek2() == Some('/') => self.skip_line_comment(),
                Some('(') if self.peek2() == Some('*') => {
                    let start = self.pos();
                    self.skip_block_comment(start);
                }
                _ => return,
            }
        }
    }

    /// Consume everything up to (not including) the end of the line.
    fn skip_line_comment(&mut self) {
        while let Some(c) = self.peek() {
            if c == '\n' {
                return;
            }
            self.bump();
        }
    }

    /// Read a `%{ ... %}` block of foreign code, and keep it.
    ///
    /// The text is C, which is not this compiler's language and never
    /// will be — so it is carried through untouched and handed to the
    /// toolchain, which speaks it. Skipping it silently was the worse
    /// answer: a program that declares `extern fun f = "ext#f"` and
    /// defines `f` here would compile and then fail to link, naming a
    /// symbol whose definition was thrown away three stages earlier.
    ///
    /// `%{^` puts the code above the output and `%{$` below; both end at
    /// `%}`, and the marker is dropped with the opener.  Unterminated is
    /// an error rather than a silent run to end of file: swallowing the
    /// rest of the program would report itself as some unrelated thing
    /// missing, hundreds of lines away.
    fn skip_inline_c(&mut self, start: Pos) {
        self.bump();
        self.bump(); // eat "%{"
        if matches!(self.peek(), Some('^' | '$' | '#')) {
            self.bump();
        }
        let from = self.pos;
        loop {
            match self.peek() {
                None => {
                    self.error(self.span_from(start), "unterminated `%{` block (no `%}`)");
                    return;
                }
                Some('%') if self.peek2() == Some('}') => {
                    let text = self.src[from..self.pos].to_string();
                    self.bump();
                    self.bump();
                    self.push(TokenKind::InlineC(text), start);
                    return;
                }
                Some(_) => {
                    self.bump();
                }
            }
        }
    }

    /// Consume a `(* ... *)` comment, honoring nesting.  `start` is the
    /// position of the opening `(` so the error can point at it.
    fn skip_block_comment(&mut self, start: Pos) {
        self.bump();
        self.bump(); // eat "(*"
        let mut depth = 1usize;
        while depth > 0 {
            match self.peek() {
                None => {
                    self.error(Span::new(start, self.pos()), "unterminated block comment");
                    return;
                }
                Some('(') if self.peek2() == Some('*') => {
                    self.bump();
                    self.bump();
                    depth += 1;
                }
                Some('*') if self.peek2() == Some(')') => {
                    self.bump();
                    self.bump();
                    depth -= 1;
                }
                _ => {
                    self.bump();
                }
            }
        }
    }

    /// An identifier (or keyword): letters, digits, primes, underscores.
    ///
    /// The prime is the interesting case.  ATS names may end in one
    /// (`x'`, `lst'`), but `'` also opens a character literal, and both
    /// can follow an identifier: `lst'` and `c - '0'`.  The rule that
    /// separates them is *lookahead for the closing quote*: a `'` starts a
    /// literal only when the source actually spells one out (`'0'`,
    /// `'\n'`); otherwise it belongs to the name being scanned.
    fn scan_identifier(&mut self, start: Pos) {
        while let Some(c) = self.peek() {
            // A `$` inside a name marks a template's hole, as in
            // `string_foreach$cont`.
            if c.is_ascii_alphanumeric() || c == '_' || c == '$' {
                self.bump();
            } else if c == '\'' && !self.at_char_literal() {
                self.bump();
            } else {
                break;
            }
        }
        // `case+`, `case-`, `val+`, `val-`: the sign is part of the keyword
        // and merely tightens exhaustiveness checking, which we do not do.
        let bare = &self.src[start.offset..self.pos];
        if matches!(bare, "case" | "val" | "fun" | "if" | "sif") {
            if matches!(self.peek(), Some('+') | Some('-')) {
                self.bump();
            }
        }
        let text = self.src[start.offset..self.pos].trim_end_matches(['+', '-']);
        let kind = match keyword(text) {
            Some(k) => k,
            None if text == "_" => TokenKind::Underscore,
            None => TokenKind::Ident(text.to_string()),
        };
        self.push(kind, start);
    }

    /// Whether the cursor sits on a complete character literal.
    ///
    /// Used to decide whether a `'` continues an identifier or opens a
    /// literal; it only ever looks a few characters ahead.
    fn at_char_literal(&self) -> bool {
        let rest = &self.src[self.pos..];
        let mut it = rest.chars();
        if it.next() != Some('\'') {
            return false;
        }
        match it.next() {
            // `'\n'`, `'\000'` — an escape, then eventually a quote.
            Some('\\') => rest[2..].chars().take(4).any(|c| c == '\''),
            Some(_) => it.next() == Some('\''),
            None => false,
        }
    }

    /// An integer literal: decimal, or hexadecimal after `0x`/`0X`.
    fn scan_number(&mut self, start: Pos) {
        let is_hex = self.peek() == Some('0') && matches!(self.peek2(), Some('x') | Some('X'));
        if is_hex {
            self.bump();
            self.bump(); // eat "0x"
        }
        let digits_begin = self.pos;
        self.consume_digits(is_hex);
        // `1.5` is a float; `xs.0` is a projection, so the `.` only joins
        // the number when a digit follows it.
        let mut is_float = false;
        if !is_hex && self.peek() == Some('.') && self.peek2().is_some_and(|c| c.is_ascii_digit()) {
            is_float = true;
            self.bump();
            self.consume_digits(false);
        }
        let text = &self.src[start.offset..self.pos];
        if is_hex && self.pos == digits_begin {
            self.error(self.span_from(start), "hex literal needs digits after `0x`");
            return;
        }
        if is_float {
            let text = text.to_string();
            return match text.parse::<f64>() {
                Ok(v) => self.push(TokenKind::FloatLit(FloatBits::new(v)), start),
                Err(_) => self.error(
                    self.span_from(start),
                    format!("`{text}` is not a valid number"),
                ),
            };
        }
        // A width/signedness suffix (`0ull`, `10L`, `3u`) says nothing to a
        // subset with a single integer width, so it is consumed and dropped.
        let text = text.to_string();
        let suffix_begin = self.pos;
        while let Some(c) = self.peek() {
            if matches!(c, 'u' | 'U' | 'l' | 'L') {
                self.bump();
            } else {
                break;
            }
        }
        let _ = suffix_begin;
        if let Some(c) = self.peek() {
            if c.is_ascii_alphanumeric() || c == '_' {
                self.error(
                    self.span_from(start),
                    format!("invalid integer literal `{text}`"),
                );
                return;
            }
        }
        let value = if is_hex {
            i64::from_str_radix(&text[2..], 16)
        } else {
            text.parse::<i64>()
        };
        match value {
            Ok(v) => self.push(TokenKind::IntLit(v), start),
            Err(_) => self.error(
                self.span_from(start),
                format!("integer literal `{text}` is out of range"),
            ),
        }
    }

    /// Consume every consecutive digit of the current literal.
    fn consume_digits(&mut self, hex: bool) {
        while let Some(c) = self.peek() {
            let ok = if hex {
                c.is_ascii_hexdigit()
            } else {
                c.is_ascii_digit()
            };
            if ok {
                self.bump();
            } else {
                break;
            }
        }
    }

    /// A string literal.  The token stores the *raw* interior — escapes
    /// intact — so decoding can happen later, at parse time.
    fn scan_string(&mut self, start: Pos) {
        self.bump(); // opening quote
        loop {
            match self.peek() {
                None => {
                    self.error(Span::new(start, self.pos()), "unterminated string literal");
                    return;
                }
                Some('"') => {
                    self.bump();
                    break;
                }
                Some('\\') => {
                    self.bump();
                    if self.peek().is_none() {
                        self.error(Span::new(start, self.pos()), "unterminated string literal");
                        return;
                    }
                    self.bump();
                }
                Some(_) => {
                    self.bump();
                }
            }
        }
        let raw = &self.src[start.offset + 1..self.pos - 1];
        self.push(TokenKind::StrLit(raw.to_string()), start);
    }

    /// A character literal: `'a'`, `'\n'`, or the octal `'\000'`.  The
    /// decoded byte is stored directly, since `char` lowers to `i8`.
    fn scan_char(&mut self, start: Pos) {
        self.bump(); // opening quote
        let byte = match self.peek() {
            None => {
                self.error(self.span_from(start), "unterminated character literal");
                return;
            }
            Some('\\') => {
                self.bump();
                let Some(e) = self.bump() else {
                    self.error(self.span_from(start), "unterminated character literal");
                    return;
                };
                match e {
                    'n' => b'\n',
                    't' => b'\t',
                    'r' => b'\r',
                    '0'..='7' => {
                        // an octal escape: up to three digits, `'\000'`
                        let mut v = e as u32 - '0' as u32;
                        while let Some(d @ '0'..='7') = self.peek() {
                            v = v * 8 + (d as u32 - '0' as u32);
                            self.bump();
                        }
                        if v > 255 {
                            self.error(self.span_from(start), "character escape is out of range");
                            return;
                        }
                        v as u8
                    }
                    '\\' => b'\\',
                    '\'' => b'\'',
                    '"' => b'"',
                    'a' => 7,
                    'b' => 8,
                    'f' => 12,
                    'v' => 11,
                    other => {
                        self.error(
                            self.span_from(start),
                            format!("unknown character escape `\\{other}`"),
                        );
                        return;
                    }
                }
            }
            Some(c) => {
                if !c.is_ascii() {
                    self.error(
                        self.span_from(start),
                        "only ASCII character literals are supported",
                    );
                    return;
                }
                self.bump();
                c as u8
            }
        };
        if self.peek() != Some('\'') {
            self.error(
                self.span_from(start),
                "expected `'` to close the character literal",
            );
            return;
        }
        self.bump();
        self.push(TokenKind::CharLit(byte), start);
    }
}

/// Build a float literal's stored form.  A small helper so callers need
/// not reach into the token vocabulary for it.
pub fn float_bits(value: f64) -> FloatBits {
    FloatBits::new(value)
}

/// Map an identifier's text to its keyword token, if it is reserved.
fn keyword(text: &str) -> Option<TokenKind> {
    Some(match text {
        "datatype" => TokenKind::Datatype,
        "fun" => TokenKind::Fun,
        "implement" => TokenKind::Implement,
        "if" => TokenKind::If,
        "then" => TokenKind::Then,
        "else" => TokenKind::Else,
        "let" => TokenKind::Let,
        "in" => TokenKind::In,
        "end" => TokenKind::End,
        "lam" => TokenKind::Lam,
        "val" => TokenKind::Val,
        "true" => TokenKind::True,
        "false" => TokenKind::False,
        "andalso" => TokenKind::Andalso,
        "orelse" => TokenKind::Orelse,
        "mod" => TokenKind::Mod,
        "fn" => TokenKind::Fn,
        "local" => TokenKind::Local,
        "case" => TokenKind::Case,
        "of" => TokenKind::Of,
        "when" => TokenKind::When,
        "var" => TokenKind::Var,
        "while" => TokenKind::While,
        "for" => TokenKind::For,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ats2_domain::errors::ErrorKind;

    fn kinds(source: &str) -> Vec<TokenKind> {
        Lexer::lex(source)
            .expect("lex")
            .into_iter()
            .map(|t| t.kind)
            .collect()
    }

    #[test]
    fn inline_c_arrives_whole_and_unlexed() {
        // `%{^ ... %}` is a block of C that ATS passes straight through
        // to the C compiler.  It must not be *lexed*, or a stray brace or
        // quote inside becomes a syntax error in a program that is
        // perfectly well-formed ATS — and it must not be dropped either,
        // because it is the body of some `extern fun` declared nearby,
        // and a program without it links to nothing.
        let k = kinds("%{^\nint f (void) { return 1 ; }\n%}\nfun g (): int = 1");
        assert_eq!(
            k[0],
            TokenKind::InlineC("\nint f (void) { return 1 ; }\n".into())
        );
        assert_eq!(k[1], TokenKind::Fun, "the ATS after it is lexed as ATS");
    }

    #[test]
    fn a_brace_or_quote_inside_inline_c_is_just_a_byte() {
        let k = kinds("%{\nchar *s = \"}\"; /* { */\n%}\nfun g (): int = 1");
        assert!(matches!(k[0], TokenKind::InlineC(_)), "{:?}", k[0]);
        assert_eq!(k[1], TokenKind::Fun);
    }

    #[test]
    fn lexes_a_record_opener_as_one_token() {
        // `'{` opens a boxed record and `@{` a flat one.  Neither is a
        // quote followed by a brace: a brace alone opens a *block*, and
        // reading the record that way would parse its fields as
        // statements.
        assert_eq!(kinds("'{ x= 1 }")[0], TokenKind::RecordOpen);
        assert_eq!(kinds("@{ x= 1 }")[0], TokenKind::RecordOpen);
    }

    #[test]
    fn lexes_the_cons_operator_as_one_token() {
        assert_eq!(kinds("x :: xs")[1], TokenKind::ColonColon);
    }

    // --- identifiers and keywords ---------------------------------

    #[test]
    fn lexes_identifiers() {
        let k = kinds("fact x' lst'");
        assert_eq!(k[0], TokenKind::Ident("fact".into()));
        assert_eq!(k[1], TokenKind::Ident("x'".into()));
        assert_eq!(k[2], TokenKind::Ident("lst'".into()));
        assert_eq!(k[3], TokenKind::Eof);
    }

    #[test]
    fn keywords_are_recognized_as_keywords_not_identifiers() {
        let k = kinds(
            "datatype fun implement if then else let in end lam val true false andalso orelse mod",
        );
        let expected = vec![
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
            TokenKind::Eof,
        ];
        assert_eq!(k, expected);
    }

    #[test]
    fn keyword_lookalike_with_prime_is_an_identifier() {
        // `fun'` is not the keyword `fun` — ATS primes extend names.
        let k = kinds("fun'");
        assert_eq!(k[0], TokenKind::Ident("fun'".into()));
    }

    #[test]
    fn lexes_a_floating_point_literal() {
        let k = kinds("0.0 1.5 12.25");
        assert_eq!(k[0], TokenKind::FloatLit(FloatBits::new(0.0)));
        assert_eq!(k[1], TokenKind::FloatLit(FloatBits::new(1.5)));
        assert_eq!(k[2], TokenKind::FloatLit(FloatBits::new(12.25)));
    }

    #[test]
    fn a_dot_after_an_integer_needs_a_digit_to_make_a_float() {
        // `xs.0` is a tuple projection, not the number `xs.0`.
        let k = kinds("1 . 0");
        assert_eq!(k[0], TokenKind::IntLit(1));
        assert_eq!(k[1], TokenKind::Dot);
        assert_eq!(k[2], TokenKind::IntLit(0));
    }

    #[test]
    fn a_dollar_starts_an_identifier() {
        // `$break`, `$delay`, `$showtype` — ATS's special forms all wear
        // a `$`, and they are names, not punctuation.
        let k = kinds("$break $delay");
        assert_eq!(k[0], TokenKind::Ident("$break".into()));
        assert_eq!(k[1], TokenKind::Ident("$delay".into()));
    }

    #[test]
    fn a_dollar_may_sit_inside_an_identifier() {
        // A template's "hole" is spelled with an embedded `$`.
        let k = kinds("string_foreach$cont");
        assert_eq!(k[0], TokenKind::Ident("string_foreach$cont".into()));
    }

    #[test]
    fn a_qualified_dollar_name_keeps_the_dot_separate() {
        // `$UN.cast` is the name `$UN`, a `.`, and the name `cast`.
        let k = kinds("$UN.cast");
        assert_eq!(k[0], TokenKind::Ident("$UN".into()));
        assert_eq!(k[1], TokenKind::Dot);
        assert_eq!(k[2], TokenKind::Ident("cast".into()));
    }

    #[test]
    fn underscore_alone_is_a_wildcard_token() {
        let k = kinds("_ _x x_");
        assert_eq!(k[0], TokenKind::Underscore);
        assert_eq!(k[1], TokenKind::Ident("_x".into()));
        assert_eq!(k[2], TokenKind::Ident("x_".into()));
    }

    // --- literals -------------------------------------------------

    #[test]
    fn lexes_integer_literals() {
        let k = kinds("42 0 007");
        assert_eq!(k[0], TokenKind::IntLit(42));
        assert_eq!(k[1], TokenKind::IntLit(0));
        assert_eq!(k[2], TokenKind::IntLit(7));
    }

    #[test]
    fn lexes_hex_integer_literals() {
        let k = kinds("0x1F 0Xff");
        assert_eq!(k[0], TokenKind::IntLit(31));
        assert_eq!(k[1], TokenKind::IntLit(255));
    }

    #[test]
    fn integer_overflow_is_a_lex_error() {
        let errs = Lexer::lex("99999999999999999999999999").expect_err("should fail");
        assert_eq!(errs[0].kind(), ErrorKind::Lex);
        assert!(errs[0].message().contains("range"), "{}", errs[0]);
    }

    #[test]
    fn digits_followed_by_letters_are_rejected() {
        let errs = Lexer::lex("123abc").expect_err("should fail");
        assert_eq!(errs[0].kind(), ErrorKind::Lex);
    }

    #[test]
    fn lexes_string_literals_with_raw_interiors() {
        // Source text:  "hello"   "a\nb"   "q\"w"
        let k = kinds(r##""hello" "a\nb" "q\"w""##);
        assert_eq!(k[0], TokenKind::StrLit(r#"hello"#.into()));
        // Escape sequences stay raw inside the token; decoding is a later stage.
        assert_eq!(k[1], TokenKind::StrLit(r#"a\nb"#.into()));
        assert_eq!(k[2], TokenKind::StrLit(r#"q\"w"#.into()));
    }

    // --- comments -------------------------------------------------

    #[test]
    fn skips_line_comments() {
        let k = kinds("// a comment\n42 // trailing\n");
        assert_eq!(k[0], TokenKind::IntLit(42));
        assert_eq!(k[1], TokenKind::Eof);
    }

    #[test]
    fn skips_block_comments() {
        let k = kinds("(* a comment *) 42");
        assert_eq!(k[0], TokenKind::IntLit(42));
    }

    #[test]
    fn block_comments_nest() {
        let k = kinds("(* outer (* inner *) still outer *) 1 + 2");
        assert_eq!(k[0], TokenKind::IntLit(1));
        assert_eq!(k[1], TokenKind::Plus);
        assert_eq!(k[2], TokenKind::IntLit(2));
    }

    #[test]
    fn unterminated_block_comment_is_an_error() {
        let errs = Lexer::lex("(* never closed").expect_err("should fail");
        assert!(errs[0].message().contains("comment"), "{}", errs[0]);
    }

    #[test]
    fn unterminated_string_is_an_error() {
        let errs = Lexer::lex("\"abc").expect_err("should fail");
        assert_eq!(errs[0].kind(), ErrorKind::Lex);
        assert!(errs[0].message().contains("string"), "{}", errs[0]);
    }

    // --- operators and punctuation --------------------------------

    #[test]
    fn lexes_the_full_operator_and_punctuation_vocabulary() {
        let k = kinds("+ - * / ~ = <> < <= > >= -> => ( ) [ ] { } , ; : | . ! _ @ $ #");
        let expected = vec![
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
            TokenKind::At,
            TokenKind::Dollar,
            TokenKind::Hash,
            TokenKind::Eof,
        ];
        assert_eq!(k, expected);
    }

    #[test]
    fn two_character_operators_win_over_single_character_ones() {
        let k = kinds("=> <> <= -> >=");
        assert_eq!(k[0], TokenKind::FatArrow);
        assert_eq!(k[1], TokenKind::Ne);
        assert_eq!(k[2], TokenKind::Le);
        assert_eq!(k[3], TokenKind::Arrow);
        assert_eq!(k[4], TokenKind::Ge);
        assert_eq!(k[5], TokenKind::Eof);
    }

    // --- stream shape ---------------------------------------------

    #[test]
    fn every_stream_ends_in_exactly_one_eof() {
        for source in ["", "42", "fun f(): int = 1", "(* c *)"] {
            let tokens = Lexer::lex(source).expect("lex");
            assert_eq!(
                tokens.last().expect("stream").kind,
                TokenKind::Eof,
                "src: {source}"
            );
            let eofs = tokens.iter().filter(|t| t.kind == TokenKind::Eof).count();
            assert_eq!(eofs, 1, "src: {source}");
        }
    }

    #[test]
    fn empty_source_yields_only_eof() {
        assert_eq!(kinds(""), vec![TokenKind::Eof]);
        assert_eq!(kinds("   \n\t  "), vec![TokenKind::Eof]);
    }

    // --- positions ------------------------------------------------

    #[test]
    fn spans_track_lines_columns_and_offsets() {
        let tokens = Lexer::lex("if\nx").expect("lex");
        let if_tok = &tokens[0];
        let x_tok = &tokens[1];
        assert_eq!(if_tok.span.start, Pos::new(1, 1, 0));
        assert_eq!(if_tok.span.end, Pos::new(1, 3, 2));
        assert_eq!(x_tok.span.start, Pos::new(2, 1, 3));
        assert_eq!(x_tok.span.end, Pos::new(2, 2, 4));
        // The EOF sits directly after the last token.
        assert_eq!(tokens[2].span.start, x_tok.span.end);
    }

    #[test]
    fn spans_cover_a_multi_line_program() {
        let src = "fun f(): int =\n  1\n";
        let tokens = Lexer::lex(src).expect("lex");
        let one = tokens
            .iter()
            .find(|t| t.kind == TokenKind::IntLit(1))
            .expect("1");
        assert_eq!(one.span.start.line, 2);
        assert_eq!(one.span.start.column, 3);
    }

    // --- robustness -----------------------------------------------

    #[test]
    fn rejects_characters_outside_the_vocabulary() {
        // `?` and `&` joined the vocabulary when the sample corpus needed
        // them; the backtick still has no meaning in ATS.
        let errs = Lexer::lex("a ` b").expect_err("should fail");
        assert_eq!(errs[0].kind(), ErrorKind::Lex);
        assert!(errs[0].message().contains("`"), "{}", errs[0]);
        assert!(errs[0].span().is_some());
    }

    #[test]
    fn reports_all_lex_errors_in_one_pass() {
        // Three independent problems: bad char, unterminated string, bad char.
        let errs = Lexer::lex(r#"` " `"#).expect_err("should fail");
        assert!(errs.len() >= 2, "expected several errors, got {errs:?}");
    }

    #[cfg(test)]
    mod equality_tests {
        use super::*;

        #[test]
        fn double_equals_is_one_token_and_means_what_one_equals_means() {
            // The static language writes `==`; the dynamic one writes `=`.
            // They are the same relation, so they are the same token.
            let tokens = Lexer::lex("i == j").expect("lex");
            let kinds: Vec<&TokenKind> = tokens.iter().map(|t| &t.kind).collect();
            assert_eq!(
                kinds,
                vec![
                    &TokenKind::Ident("i".into()),
                    &TokenKind::Eq,
                    &TokenKind::Ident("j".into()),
                    &TokenKind::Eof
                ]
            );
        }

        #[test]
        fn a_single_equals_is_untouched() {
            let tokens = Lexer::lex("x = 1").expect("lex");
            assert_eq!(tokens[1].kind, TokenKind::Eq);
            assert_eq!(tokens[2].kind, TokenKind::IntLit(1));
        }
    }
}
