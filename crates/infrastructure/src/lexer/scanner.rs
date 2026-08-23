use super::keywords::keyword;
use ats2_domain::errors::CompileError;
use ats2_domain::tokens::{Pos, Span, Token, TokenKind};

pub struct Scanner<'a> {
    pub(crate) src: &'a str,
    pub(crate) pos: usize,
    pub(crate) line: usize,
    pub(crate) col: usize,
    pub(crate) tokens: Vec<Token>,
    pub(crate) errors: Vec<CompileError>,
}

impl<'a> Scanner<'a> {
    pub fn new(src: &'a str) -> Self {
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
    pub(crate) fn peek(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }

    /// The character after the cursor, if any.
    pub(crate) fn peek2(&self) -> Option<char> {
        let mut it = self.src[self.pos..].chars();
        it.next();
        it.next()
    }

    /// Advance the cursor by one character, maintaining line/column.
    pub(crate) fn bump(&mut self) -> Option<char> {
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
    pub(crate) fn pos(&self) -> Pos {
        Pos::new(self.line, self.col, self.pos)
    }

    /// A span from a previously captured start to the cursor.
    pub(crate) fn span_from(&self, start: Pos) -> Span {
        Span::new(start, self.pos())
    }

    /// Record a lex error at a span.
    pub(crate) fn error(&mut self, span: Span, message: impl Into<String>) {
        self.errors.push(CompileError::lex(span, message));
    }

    /// Emit a token spanning from `start` to the cursor.
    pub(crate) fn push(&mut self, kind: TokenKind, start: Pos) {
        self.tokens.push(Token::new(kind, self.span_from(start)));
    }
    /// Lex the whole source.  Trivia is skipped until a real token or EOF.
    pub fn scan_all(&mut self) {
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
            // ATS spells the two short-circuiting connectives both as
            // words and as symbols, and means the same thing by each —
            // so `||` and `&&` collapse onto the tokens `orelse` and
            // `andalso` already produce.  Reading them here is what
            // stops `pred(x) || rest` being lexed as two arm separators
            // and failing as an expression.
            //
            // Neither doubled form is ambiguous with the single one:
            // `|` separates arms and never abuts another `|`, and `&`
            // marks a borrow, which is a *prefix* and so never follows
            // a value.
            '|' if self.peek2() == Some('|') => {
                self.bump();
                self.bump();
                self.push(TokenKind::Orelse, start);
            }
            '&' if self.peek2() == Some('&') => {
                self.bump();
                self.bump();
                self.push(TokenKind::Andalso, start);
            }
            // The shifts are deliberately *not* lexed here.  `>>` already
            // means something in a type — `&(@[int][m]) >> _`, the view a
            // parameter is left in — and that is read as two `>` tokens
            // in several places.  Collapsing them into one token here
            // fixed the expression `1 >> 2` and broke every one of those.
            // So the token stream keeps its shape and the *expression*
            // parser recognises a shift by adjacency instead, where the
            // question cannot arise: see `current_binop`.
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
            // `'{` and `@{` open a record.
            '\'' | '@' if self.peek2() == Some('{') => {
                self.bump();
                self.bump();
                self.push(TokenKind::RecordOpen, start);
            }
            // `'(` opens a tuple.
            '\'' if self.peek2() == Some('(') => {
                self.bump();
                self.bump();
                self.push(TokenKind::LParen, start);
            }
            // `'[` opens an array/bracket.
            '\'' if self.peek2() == Some('[') => {
                self.bump();
                self.bump();
                self.push(TokenKind::LBracket, start);
            }
            // `'$` — a quoted special form, whose quote is decoration
            // and is dropped.  The char literal `'$'` is written the
            // same way for its first two characters, so the literal is
            // checked for first: without that, the quote was swallowed
            // and a lexer scanning `'$'` produced a stray `$` where an
            // expression was expected.
            '\'' if self.peek2() == Some('$') && !self.at_char_literal() => {
                self.bump();
            }
            '\'' if !self.at_char_literal() => {
                self.bump();
                if let Some(c) = self.peek() {
                    if c.is_ascii_alphabetic() || c == '_' {
                        self.scan_identifier(start);
                    }
                }
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
    /// Skip whitespace, line comments, and (nested) block comments.
    fn skip_trivia(&mut self) {
        loop {
            match self.peek() {
                Some(' ') | Some('\t') | Some('\r') | Some('\n') => {
                    self.bump();
                }
                Some('/') if self.peek2() == Some('/') => self.skip_line_comment(),
                Some('/') if self.peek2() == Some('*') => {
                    let start = self.pos();
                    self.skip_c_block_comment(start);
                }
                Some('(') if self.peek2() == Some('*') => {
                    let start = self.pos();
                    self.skip_block_comment(start);
                }
                _ => return,
            }
        }
    }

    /// Consume a C-style `/* ... */` comment.
    fn skip_c_block_comment(&mut self, start: Pos) {
        self.bump();
        self.bump(); // eat "/*"
        while let Some(c) = self.peek() {
            if c == '*' && self.peek2() == Some('/') {
                self.bump();
                self.bump();
                return;
            }
            self.bump();
        }
        self.error(
            self.span_from(start),
            "unterminated `/*` comment (missing `*/`)",
        );
    }
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

}
