use super::*;
use ats2_domain::tokens::{FloatBits, Pos, Span, TokenKind};


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

