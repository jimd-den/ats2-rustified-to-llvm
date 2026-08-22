use super::scanner::Scanner;
use ats2_domain::tokens::{FloatBits, Pos, TokenKind};

impl<'a> Scanner<'a> {
    pub(crate) fn scan_number(&mut self, start: Pos) {
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
    pub(crate) fn consume_digits(&mut self, hex: bool) {
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
}
pub fn float_bits(value: f64) -> FloatBits {
    FloatBits::new(value)
}
