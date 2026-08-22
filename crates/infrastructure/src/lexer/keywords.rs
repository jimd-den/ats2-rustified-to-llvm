use ats2_domain::tokens::TokenKind;

pub(crate) fn keyword(text: &str) -> Option<TokenKind> {
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
        // `try e with | p => h` — `with` starts the handler list; it is
        // a keyword so it is not read as an identifier in juxtaposition.
        "with" => TokenKind::With,
        _ => return None,
    })
}
