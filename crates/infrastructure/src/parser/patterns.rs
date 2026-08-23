use super::context::*;
use super::decode::*;
use super::expr::*;
use super::types::*;
use ats2_domain::ast::*;
use ats2_domain::errors::CompileError;
use ats2_domain::statics::*;
use ats2_domain::tokens::*;
use std::collections::{HashMap, HashSet};


impl<'a> ParseCtx<'a> {
    pub(crate) fn parse_val_bind(&mut self, mutable: bool) -> Result<BindKind, CompileError> {
        // A name set aside by some earlier binding's pattern is not
        // this one's: cleared here so a `val` with no proof half
        // cannot inherit the last one that had.
        self.last_proof_name = None;
        // `val [r:int] (pf | r) = ...` — the binding opens an
        // existential: the caller learns there *is* such an `r` and
        // gives it a name.  The name is static, so it binds nothing at
        // run time — but it is what lets the caller *reason* about the
        // witness the callee refused to name, so it is kept.
        let opened: Vec<(String, Sort)> = self
            .parse_existentials()
            .into_iter()
            .flat_map(|q| q.vars)
            .collect();
        // Does a pattern start here?  A literal always does; a name does
        // when it is applied — `cons(n, ns)` — since a binding's name is
        // never followed by `(`.
        let starts_pattern = match &self.peek().kind {
            TokenKind::IntLit(_)
            | TokenKind::CharLit(_)
            | TokenKind::True
            | TokenKind::False
            | TokenKind::StrLit(_)
            | TokenKind::Tilde
            // `val-@cons(n, ns)` — a match that takes the value apart in
            // place.  The `@` marks the view, and a binding's *name* can
            // never start with one, so it always means a pattern.
            | TokenKind::At
            | TokenKind::LParen
            | TokenKind::Underscore => true,
            TokenKind::Ident(_) => {
                self.tokens.get(self.pos + 1).is_some_and(|t| t.kind == TokenKind::LParen)
            }
            _ => false,
        };
        if starts_pattern {
            let pattern = self.parse_pattern()?;
            if let Pattern::Var(n) = pattern {
                // `(x)` is just `x` spelled with its brackets.
                return Ok(BindKind::Simple(self.finish_let_bind(
                    &opened,
                    Some(n),
                    None,
                    mutable,
                )?));
            }
            if let Pattern::Tuple(items) = &pattern {
                if items.is_empty() {
                    return Ok(BindKind::Simple(
                        self.finish_let_bind(&opened, None, None, mutable)?,
                    ));
                }
                if items.len() == 1 {
                    if let Pattern::Var(n) = &items[0] {
                        let n = n.clone();
                        return Ok(BindKind::Simple(self.finish_let_bind(
                            &opened,
                            Some(n),
                            None,
                            mutable,
                        )?));
                    }
                }
            }
            if let Pattern::Wildcard = pattern {
                return Ok(BindKind::Simple(
                    self.finish_let_bind(&opened, None, None, mutable)?,
                ));
            }
            self.expect(&TokenKind::Eq, "expected `=` in the binding")?;
            let value = self.parse_expr(0)?;
            return Ok(BindKind::Pattern(pattern, value));
        }
        let name = if matches!(self.peek().kind, TokenKind::Ident(_)) {
            Some(self.expect_ident("expected a binding name")?)
        } else {
            return Err(self.error_here("expected a name, `_` or a pattern after `val`"));
        };
        Ok(BindKind::Simple(
            self.finish_let_bind(&opened, name, None, mutable)?,
        ))
    }

    /// The `: type` and `= value` (or uninitialized zero) of a binding.

    pub(crate) fn finish_let_bind(
        &mut self,
        opened: &[(String, Sort)],
        name: Option<String>,
        _dummy: Option<()>,
        mutable: bool,
    ) -> Result<LetBind, CompileError> {
        let ty = if self.at(&TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };
        // `var i: int` — a cell declared now and written later.  ATS's
        // type system forbids reading it in between, so a zero of the
        // annotated type stands in for "not yet written".
        let value = if mutable && !self.at(&TokenKind::Eq) {
            let Some(ty) = &ty else {
                return Err(self.error_here("an uninitialized `var` needs a type annotation"));
            };
            zero_of(ty)
                .ok_or_else(|| self.error_here("this type has no zero value to start from"))?
        } else {
            self.expect(&TokenKind::Eq, "expected `=` in the binding")?;
            self.parse_expr(0)?
        };
        Ok(LetBind {
            opened: opened.to_vec(),
            proof: false,
            name,
            ty,
            value,
            mutable,
            destructures: None,
            // Whatever the pattern just read set aside, taken exactly
            // once: a later binding with no proof half of its own must
            // not inherit this one's.
            proof_name: self.last_proof_name.take(),
        })
    }

    /// `typedef T = t` — record the alias, and report whether it was one
    /// this parser understands.
    ///
    /// The parameterized form (`typedef m (a:t@ype) = ...`) and record
    /// types are not modelled, so a `typedef` that does not fit is left
    /// to the directive skipper rather than half-recorded.

    pub(crate) fn parse_proof_binding(&mut self) -> Option<LetBind> {
        let save = self.pos;
        self.advance(); // `prval` / `prvar`
        let mut destructures = None;
        let name = match self.peek().kind.clone() {
            // `prval pf = ...` — a name, unless it is a constructor
            // pattern (`EQINT()`), which binds nothing this compiler has.
            TokenKind::Ident(n)
                if self
                    .tokens
                    .get(self.pos + 1)
                    .is_some_and(|t| t.kind == TokenKind::Eq) =>
            {
                self.advance();
                Some(n)
            }
            _ => {
                // Anything else on the left — `()`, `EQINT()`, a pattern
                // — is stepped over to reach the `=`.  A *constructor*
                // pattern is stepped over having first been read: it is
                // the one thing on this side that carries meaning, and
                // it is what buys the guard the body then relies on.
                if let Ok(pattern) = self.parse_pattern() {
                    if matches!(pattern, Pattern::Ctor(..)) {
                        destructures = Some(pattern);
                    }
                }
                while !self.at(&TokenKind::Eq) && !self.at(&TokenKind::Eof) {
                    let before = self.pos;
                    self.advance();
                    if self.pos == before {
                        self.pos = save;
                        return None;
                    }
                }
                None
            }
        };
        if !self.at(&TokenKind::Eq) {
            self.pos = save;
            return None;
        }
        self.advance();
        match self.parse_expr(0) {
            Ok(value) => Some(LetBind {
                opened: Vec::new(),
                proof: true,
                name,
                ty: None,
                value,
                mutable: false,
                destructures,
                proof_name: None,
            }),
            Err(_) => {
                self.pos = save;
                None
            }
        }
    }

    /// Skip an ignorable declaration inside a body, stopping before the
    /// next thing that can start one (or before `in`/`end`/`}`).
    ///
    /// Bracket depth is tracked, because the tokens that end a
    /// declaration also appear *inside* one: `prval () = fact_ind{n}()`
    /// contains a `}` that closes a static argument list, not the
    /// enclosing block.  Stopping there would lose the `in` that follows
    /// and turn a proof-level line into a parse error.

    pub(crate) fn parse_pattern(&mut self) -> Result<Pattern, CompileError> {
        let head = self.parse_pattern_primary()?;
        if self.at(&TokenKind::ColonColon) {
            self.advance();
            let tail = self.parse_pattern()?;
            let cons = self.cons_name.clone();
            return Ok(Pattern::Ctor(cons, vec![head, tail]));
        }
        Ok(head)
    }

    /// Whether the next token begins a pattern argument that may be
    /// written against a constructor name without parentheses: `C _`,
    /// `C x`, `C 0`.

    pub(crate) fn starts_a_juxtaposed_pattern(&self) -> bool {
        matches!(
            self.peek().kind,
            TokenKind::Underscore
                | TokenKind::IntLit(_)
                | TokenKind::CharLit(_)
                | TokenKind::StrLit(_)
                | TokenKind::True
                | TokenKind::False
                | TokenKind::Tilde
                | TokenKind::At
                | TokenKind::Ident(_)
        )
    }

    /// One pattern with no trailing operator.

    pub(crate) fn parse_pattern_primary(&mut self) -> Result<Pattern, CompileError> {
        match self.peek().kind.clone() {
            // `~BTcons (l, x, r)` — a pattern that *consumes* the linear
            // value it matches.  Freeing is what the tilde marks, and
            // with an arena there is nothing to free, so it decorates
            // the pattern without changing it.
            TokenKind::Tilde => {
                self.advance();
                self.parse_pattern()
            }
            // `val-@cons(n, ns)` — the `@` says the match takes the
            // value apart *in place*: the names it binds are the value's
            // own cells, so writing to one writes into the value.
            TokenKind::At => {
                self.advance();
                Ok(Pattern::InPlace(Box::new(self.parse_pattern()?)))
            }
            TokenKind::Underscore => {
                self.advance();
                Ok(Pattern::Wildcard)
            }
            TokenKind::IntLit(n) => {
                self.advance();
                Ok(Pattern::Int(n))
            }
            TokenKind::CharLit(b) => {
                self.advance();
                Ok(Pattern::Char(b))
            }
            TokenKind::True => {
                self.advance();
                Ok(Pattern::Bool(true))
            }
            TokenKind::False => {
                self.advance();
                Ok(Pattern::Bool(false))
            }
            TokenKind::StrLit(raw) => {
                let span = self.peek().span;
                self.advance();
                Ok(Pattern::Str(decode_string(&raw, span)?))
            }
            TokenKind::LParen => {
                self.advance();
                if self.at(&TokenKind::RParen) {
                    self.advance();
                    // `()` — the unit pattern, which tests nothing.
                    return Ok(Pattern::Tuple(vec![]));
                }
                // `(pf | v)`, `(pfat, pfgc | p)` — everything left of the
                // bar is proof, which exists only for the type checker.
                // The bar may arrive after any number of them, so the
                // comma loop and the bar are read together.
                //
                // What preceded a bar binds no storage, so it is not a
                // pattern the value is matched against — but it is not
                // nothing either: the proof half is where the claim
                // lives, and a body that later spends it (`prval C () =
                // pf`) can say nothing about a name that was thrown
                // away. The last one is remembered for the binding to
                // pick up; the rest bind no claim this checker reads.
                let mut items = Vec::new();
                loop {
                    items.push(self.parse_pattern()?);
                    if self.at(&TokenKind::Comma) {
                        self.advance();
                        continue;
                    }
                    if self.at(&TokenKind::Pipe) {
                        self.advance();
                        if let Some(Pattern::Var(n)) = items.last() {
                            self.last_proof_name = Some(n.clone());
                        }
                        items.clear();
                        continue;
                    }
                    break;
                }
                self.expect(&TokenKind::RParen, "expected `)` after the pattern")?;
                if items.len() == 1 {
                    Ok(items.into_iter().next().expect("one item"))
                } else {
                    Ok(Pattern::Tuple(items))
                }
            }
            TokenKind::Ident(name) => {
                self.advance();
                // `$C.Red` — a constructor reached through a `staload`
                // alias.  The qualifier is dropped exactly as it is in
                // an expression and a type.
                let name = if name.starts_with('$')
                    && self.at(&TokenKind::Dot)
                    && matches!(
                        self.tokens.get(self.pos + 1).map(|t| &t.kind),
                        Some(TokenKind::Ident(_))
                    ) {
                    self.advance(); // `.`
                    self.expect_ident("expected a constructor name")?
                } else {
                    name
                };
                let name = self.renames.get(&name).cloned().unwrap_or(name);
                self.skip_template_arguments();
                // The parentheses are what separate a constructor from a
                // variable: `nil()` tests, `other` binds.
                if self.at(&TokenKind::LParen) {
                    self.advance();
                    let mut fields = Vec::new();
                    if !self.at(&TokenKind::RParen) {
                        loop {
                            fields.push(self.parse_pattern()?);
                            if self.at(&TokenKind::Comma) {
                                self.advance();
                            } else {
                                break;
                            }
                        }
                    }
                    self.expect(
                        &TokenKind::RParen,
                        "expected `)` after the constructor fields",
                    )?;
                    Ok(Pattern::Ctor(name, fields))
                } else if self.starts_a_juxtaposed_pattern() {
                    // `C _`, `C x` — a constructor applied to one argument
                    // written without the parentheses ATS allows omitting.
                    let arg = self.parse_pattern_primary()?;
                    Ok(Pattern::Ctor(name, vec![arg]))
                } else {
                    Ok(Pattern::Var(name))
                }
            }
            _ => Err(self.error_here("expected a pattern")),
        }
    }
}
