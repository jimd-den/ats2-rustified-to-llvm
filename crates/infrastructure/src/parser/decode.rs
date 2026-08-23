use ats2_domain::errors::CompileError;
use ats2_domain::tokens::Span;

/// right-associative, so the same power is used on both sides.
pub(crate) const CONS_BP: u8 = 6;

/// Decode a raw string interior into its semantic value.  The lexer kept
/// the escapes verbatim; this is where `\n` becomes a real newline.
pub(crate) fn decode_string(raw: &str, span: Span) -> Result<String, CompileError> {
    let mut out = String::new();
    let mut chars = raw.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        let Some(esc) = chars.next() else {
            return Err(CompileError::parse(span, "dangling escape sequence"));
        };
        match esc {
            '\n' => {}
            'n' => out.push('\n'),
            't' => out.push('\t'),
            'r' => out.push('\r'),
            'a' => out.push('\x07'),
            'b' => out.push('\x08'),
            'f' => out.push('\x0c'),
            'v' => out.push('\x0b'),
            '0'..='7' => {
                let mut v = esc as u32 - '0' as u32;
                for _ in 0..2 {
                    if let Some(d @ '0'..='7') = chars.clone().next() {
                        chars.next();
                        v = v * 8 + (d as u32 - '0' as u32);
                    } else {
                        break;
                    }
                }
                out.push(std::char::from_u32(v).unwrap_or('\0'));
            }
            'x' => {
                let mut hex = String::new();
                for _ in 0..2 {
                    if let Some(h) = chars.clone().next() {
                        if h.is_ascii_hexdigit() {
                            chars.next();
                            hex.push(h);
                        }
                    }
                }
                if let Ok(b) = u8::from_str_radix(&hex, 16) {
                    out.push(b as char);
                } else {
                    return Err(CompileError::parse(span, "invalid hex escape sequence"));
                }
            }
            '\\' | '"' | '\'' | '(' | ')' | '[' | ']' | '{' | '}' | '$' | '#' | '%' | ' ' => {
                out.push(esc);
            }
            other => {
                return Err(CompileError::parse(
                    span,
                    format!("unknown escape sequence `\\{other}`"),
                ));
            }
        }
    }
    Ok(out)
}

/// The binding power of a backslash-infix application, `x \f y`.
///
/// Tighter than the comparisons, so `x \intmod y = 0` groups the way it
/// reads, and looser than ordinary arithmetic, so `a + b \f c` puts the
/// sum on the left rather than splitting it.
pub(crate) const BACKSLASH_BP: u8 = 6;
