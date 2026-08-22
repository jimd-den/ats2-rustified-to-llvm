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
        let digits_end = self.pos;

        if is_hex && self.pos == digits_begin {
            self.error(self.span_from(start), "hex literal needs digits after `0x`");
            return;
        }

        // `1.5` is a float; `xs.0` is a projection, so the `.` only joins
        // the number when a digit follows it.
        let mut is_float = false;
        if !is_hex && self.peek() == Some('.') && self.peek2().is_some_and(|c| c.is_ascii_digit()) {
            is_float = true;
            self.bump();
            self.consume_digits(false);
        }

        // Scientific notation: `1e-3`, `2.0e5`
        if !is_hex && matches!(self.peek(), Some('e') | Some('E')) {
            let next_ch = self.peek2();
            if matches!(next_ch, Some('+') | Some('-')) || next_ch.is_some_and(|c| c.is_ascii_digit()) {
                is_float = true;
                self.bump(); // eat 'e'/'E'
                if matches!(self.peek(), Some('+') | Some('-')) {
                    self.bump();
                }
                self.consume_digits(false);
            }
        }

        // Float suffix: `1.0f`, `1f`, `1.0d`
        let float_num_end = self.pos;
        let is_float_suffix = !is_hex && matches!(self.peek(), Some('f') | Some('F') | Some('d') | Some('D'));
        if is_float_suffix {
            is_float = true;
            self.bump();
        }

        if is_float {
            let float_str = &self.src[start.offset..float_num_end];
            return match float_str.parse::<f64>() {
                Ok(v) => self.push(TokenKind::FloatLit(FloatBits::new(v)), start),
                Err(_) => self.error(
                    self.span_from(start),
                    format!("`{float_str}` is not a valid number"),
                ),
            };
        }

        // Integer width/signedness suffixes (`0ull`, `10L`, `3u`, `0x10ULL`)
        while let Some(c) = self.peek() {
            if matches!(c, 'u' | 'U' | 'l' | 'L' | 'z' | 'Z' | 't' | 'T') {
                self.bump();
            } else {
                break;
            }
        }

        let full_text = &self.src[start.offset..self.pos];
        if let Some(c) = self.peek() {
            if c.is_ascii_alphanumeric() || c == '_' {
                self.error(
                    self.span_from(start),
                    format!("invalid integer literal `{full_text}`"),
                );
                return;
            }
        }

        let raw_digits = if is_hex {
            &self.src[digits_begin..digits_end]
        } else {
            &self.src[start.offset..digits_end]
        };

        let value = if is_hex {
            i64::from_str_radix(raw_digits, 16)
        } else {
            raw_digits.parse::<i64>()
        };

        match value {
            Ok(v) => self.push(TokenKind::IntLit(v), start),
            Err(_) => self.error(
                self.span_from(start),
                format!("integer literal `{full_text}` is out of range"),
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

/// Build a float literal's stored form.
pub fn float_bits(value: f64) -> FloatBits {
    FloatBits::new(value)
}
