use super::scanner::Scanner;
use ats2_domain::tokens::{Pos, Span, TokenKind};

impl<'a> Scanner<'a> {
    pub(crate) fn scan_string(&mut self, start: Pos) {
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
    pub(crate) fn scan_char(&mut self, start: Pos) {
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
                    '\"' => b'\"',
                    'a' => 7,
                    'b' => 8,
                    'f' => 12,
                    'v' => 11,
                    punct @ ('(' | ')' | '[' | ']' | '{' | '}' | '$' | '#' | '%' | ' ' | ':' | ',' | '.') => punct as u8,
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
