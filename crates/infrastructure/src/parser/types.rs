use super::context::*;
use super::decode::*;
use super::expr::*;
use super::patterns::*;
use ats2_domain::ast::*;
use ats2_domain::errors::CompileError;
use ats2_domain::statics::*;
use ats2_domain::tokens::*;
use std::collections::{HashMap, HashSet};


impl<'a> ParseCtx<'a> {
    pub(crate) fn parse_quantifiers(&mut self) -> Vec<Quant> {
        self.parse_quantifiers_and_metric().0
    }

    /// The same, keeping the `.<n>.` metric that may sit among them.
    ///
    /// Quantifier and metric interleave in real signatures — `{n:nat}
    /// .<n>.` and `.<n>. {n:nat}` are both written — so one routine reads
    /// the run rather than two taking turns and each stopping at the
    /// other.

    pub(crate) fn parse_quantifiers_and_metric(&mut self) -> (Vec<Quant>, Vec<SExp>) {
        let mut metric = Vec::new();
        let mut out = Vec::new();
        loop {
            if let Some(terms) = self.parse_metric() {
                metric = terms;
                continue;
            }
            if self.at(&TokenKind::LBrace) {
                let save = self.pos;
                match self.parse_one_quantifier(&TokenKind::RBrace) {
                    Some(q) => out.push(q),
                    None => {
                        self.pos = save;
                        self.skip_balanced(&TokenKind::LBrace, &TokenKind::RBrace);
                    }
                }
                continue;
            }
            let before = self.pos;
            self.skip_static_annotations();
            if self.pos == before {
                return (out, metric);
            }
        }
    }

    /// `.<n>.`, `.<m, n>.`, `.<>.` — a termination metric, if one is here.
    ///
    /// Returns `None` when the next tokens are not a metric at all, and
    /// an *empty* vector for `.<>.`, which is ATS for "no metric": the
    /// two are different answers and collapsing them would turn "I claim
    /// nothing" into "I claim something about nothing".

    pub(crate) fn parse_metric(&mut self) -> Option<Vec<SExp>> {
        if !self.at(&TokenKind::Dot) {
            return None;
        }
        // The lexer reads `<>` as one not-equal token, so `.<>.` arrives
        // as three tokens rather than four.
        match self.tokens.get(self.pos + 1).map(|t| t.kind.clone()) {
            Some(TokenKind::Ne) => {
                self.advance();
                self.advance();
                if self.at(&TokenKind::Dot) {
                    self.advance();
                }
                Some(Vec::new())
            }
            Some(TokenKind::Lt) => {
                let save = self.pos;
                self.advance();
                self.advance();
                let mut terms = Vec::new();
                // Above the comparisons' binding power, so the closing
                // `>` ends the metric instead of being read as
                // "greater than" — `.<n>.` would otherwise parse as the
                // start of `n > .`, and swallow the signature with it.
                const ABOVE_COMPARISON: u8 = 6;
                while !self.at(&TokenKind::Gt) && !self.at(&TokenKind::Eof) {
                    let Ok(e) = self.parse_expr(ABOVE_COMPARISON) else {
                        break;
                    };
                    let Some(term) = sexp_of_expr(&e) else { break };
                    terms.push(term);
                    if self.at(&TokenKind::Comma) {
                        self.advance();
                    } else {
                        break;
                    }
                }
                if !self.at(&TokenKind::Gt) {
                    // A metric outside the fragment costs its own claim,
                    // not the signature it was written on.
                    self.pos = save;
                    self.skip_static_annotations();
                    return Some(Vec::new());
                }
                self.advance();
                if self.at(&TokenKind::Dot) {
                    self.advance();
                }
                Some(terms)
            }
            _ => None,
        }
    }

    /// `{m,n : nat | m > n}` — one group of static variables.
    ///
    /// The universal and existential forms differ only in their
    /// brackets, so the closer is a parameter and one routine reads both.

    pub(crate) fn parse_one_quantifier(&mut self, close: &TokenKind) -> Option<Quant> {
        let opener = self.pos;
        self.advance(); // `{` or `[`
        if let Some(q) = self.parse_binder_group(close) {
            return Some(q);
        }
        // `[fact(0) == 1]` — a bracket with nothing bound.  A proof
        // function states what it proves this way: no witness is named
        // because there is nothing to name, the claim *is* the content.
        // Read as a binder it parses as nothing at all, and the axiom
        // says nothing.
        self.pos = opener + 1;
        let claim = self.parse_expr(0).ok().as_ref().and_then(sexp_of_expr);
        match claim {
            // Only a *relation* qualifies.  `{n}` at a call site is an
            // instantiation, and reading a bare name as a guard would
            // turn every instantiation into an assumption.
            Some(claim) if is_relation(&claim) && self.at(close) => {
                self.advance();
                Some(Quant {
                    vars: Vec::new(),
                    guard: Some(claim),
                })
            }
            _ => {
                self.pos = opener;
                None
            }
        }
    }

    /// `{m,n : nat | m > n}` — the binder half of a quantifier, if that
    /// is what is here.  The opener has already been consumed.

    pub(crate) fn parse_binder_group(&mut self, close: &TokenKind) -> Option<Quant> {
        let save = self.pos;
        let mut names = Vec::new();
        loop {
            match self.peek().kind.clone() {
                TokenKind::Ident(n) => {
                    self.advance();
                    names.push(n);
                }
                _ => {
                    self.pos = save;
                    return None;
                }
            }
            if self.at(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        // A group with no sort (`{n}`) is an instantiation, not a
        // binder, and this is not the place that reads one.
        if !self.at(&TokenKind::Colon) {
            self.pos = save;
            return None;
        }
        self.advance();
        let Some(sort) = self.parse_sort_name() else {
            self.pos = save;
            return None;
        };
        let mut vars: Vec<(String, Sort)> = names
            .into_iter()
            .map(|n| (n, Sort::from_name(&sort)))
            .collect();
        // `{a:t0p;b:vt0p}` — several binder groups may share one pair of
        // braces, separated by semicolons. Semicolons after `|` still join
        // guard conjuncts and are handled below.
        while self.at(&TokenKind::Semicolon) {
            self.advance();
            let mut names = Vec::new();
            loop {
                let TokenKind::Ident(name) = self.peek().kind.clone() else {
                    self.pos = save;
                    return None;
                };
                self.advance();
                names.push(name);
                if self.at(&TokenKind::Comma) {
                    self.advance();
                } else {
                    break;
                }
            }
            if !self.at(&TokenKind::Colon) {
                self.pos = save;
                return None;
            }
            self.advance();
            let Some(sort) = self.parse_sort_name() else {
                self.pos = save;
                return None;
            };
            vars.extend(names.into_iter().map(|name| (name, Sort::from_name(&sort))));
        }
        // `{i,j:nat | i <= j+1; i+j == n-1}` — ATS writes a conjunction
        // of claims with semicolons, and this is how every loop
        // invariant in the corpus is spelled.  Reading only the first
        // conjunct would not merely weaken the guard: the quantifier
        // would fail to close, and the *sorts* would be lost with it, so
        // the loop would forget even that its counters are naturals.
        let guard = if self.at(&TokenKind::Pipe) {
            self.advance();
            let mut conjuncts = Vec::new();
            loop {
                let e = self.parse_expr(0).ok()?;
                conjuncts.push(sexp_of_expr(&e)?);
                if !self.at(&TokenKind::Semicolon) {
                    break;
                }
                self.advance();
            }
            conjuncts
                .into_iter()
                .reduce(|a, b| SExp::App("&&".into(), vec![a, b]))
        } else {
            None
        };
        if !self.at(close) {
            self.pos = save;
            return None;
        }
        self.advance();
        Some(Quant { vars, guard })
    }

    /// `:<!wrt>`, `:<!laz>`, `:<cloref1>` — the *effects* a function may
    /// have.
    ///
    /// ATS tracks effects in the type: whether a function writes, may
    /// not terminate, is lazy, or is a closure.  None of that changes
    /// what is emitted for it, so the annotation is read and dropped —
    /// but it has to be read, because it sits exactly where a return
    /// type is expected.

    pub(crate) fn parse_sort_name(&mut self) -> Option<String> {
        let TokenKind::Ident(mut name) = self.peek().kind.clone() else {
            return None;
        };
        self.advance();
        while self.at(&TokenKind::At) {
            self.advance();
            let TokenKind::Ident(rest) = self.peek().kind.clone() else {
                return None;
            };
            self.advance();
            name = format!("{name}@{rest}");
        }
        Some(name)
    }

    /// `[r:int]` — the existential quantifier on a result type.

    pub(crate) fn parse_existentials(&mut self) -> Vec<Quant> {
        let mut out = Vec::new();
        loop {
            // `#[n:nat] t` — ATS writes an existential type with a hash
            // before the bracket, its marker for "exists".  It binds the
            // same way the bare `[n:nat] t` form does, so the `#` is read
            // and dropped and the bracket is read as usual.
            if self.at(&TokenKind::Hash) {
                self.advance();
            }
            if !self.at(&TokenKind::LBracket) {
                return out;
            }
            let save = self.pos;
            match self.parse_one_quantifier(&TokenKind::RBracket) {
                Some(q) => out.push(q),
                None => {
                    self.pos = save;
                    self.skip_balanced(&TokenKind::LBracket, &TokenKind::RBracket);
                }
            }
        }
    }


    pub(crate) fn parse_template_arguments(&mut self) -> Result<Option<Vec<Ty>>, CompileError> {
        Ok(self.parse_instantiation()?.0)
    }

    /// The same, keeping the *static* reading of the brace groups.
    ///
    /// Returned rather than stashed on the cursor because reading a
    /// static term parses an expression, which re-enters this routine —
    /// and shared state does not survive its own recursion.

    pub(crate) fn parse_instantiation(&mut self) -> Result<(Option<Vec<Ty>>, Vec<SExp>), CompileError> {
        // `BTnil{int}()`, `list_vt_cons{int}{0}(...)` — ATS writes a
        // template's arguments in braces as readily as in angle
        // brackets, and the two notations mix freely.  A brace group is
        // read as types when it can be: `from{n:int}` carries a sort and
        // is a quantifier-like static argument, so a group that does not
        // parse as types is put back and skipped as before.
        let mut brace_args: Vec<Ty> = Vec::new();
        let mut saw_brace_group = false;
        // A template instantiation names *every* argument.  One group
        // that is not types makes the whole run static — otherwise
        // `g{n+1}{n}` would be half an instance and half a claim.
        let mut every_group_typed = true;
        let mut static_args: Vec<SExp> = Vec::new();
        while self.at(&TokenKind::LBrace) {
            let save = self.pos;
            static_args.extend(self.read_static_group(save).unwrap_or_default());
            self.advance();
            let mut group = Vec::new();
            let parsed = (|| -> Result<(), CompileError> {
                loop {
                    group.push(self.parse_type()?);
                    if self.at(&TokenKind::Comma) {
                        self.advance();
                    } else {
                        break;
                    }
                }
                Ok(())
            })();
            if parsed.is_ok() && self.at(&TokenKind::RBrace) {
                self.advance();
                saw_brace_group = true;
                brace_args.extend(group);
            } else {
                every_group_typed = false;
                self.pos = save;
                self.skip_balanced(&TokenKind::LBrace, &TokenKind::RBrace);
            }
        }
        while self.at(&TokenKind::LBrace) {
            let save = self.pos;
            static_args.extend(self.read_static_group(save).unwrap_or_default());
            every_group_typed = false;
            self.skip_balanced(&TokenKind::LBrace, &TokenKind::RBrace);
        }
        // `f<>` — "work it out".  The lexer reads `<>` as the not-equal
        // token, so the empty argument list arrives as one token and has
        // to be matched on its own.
        if self.at(&TokenKind::Ne)
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|t| t.kind == TokenKind::LParen)
        {
            self.advance();
            return Ok((Some(Vec::new()), static_args));
        }
        if !(self.at(&TokenKind::Lt) && self.looks_like_template_args()) {
            // No angle group follows: the braces alone decide whether an
            // instance was named.
            return Ok((
                if saw_brace_group && every_group_typed {
                    Some(brace_args)
                } else {
                    None
                },
                static_args,
            ));
        }
        let mut args = Vec::new();
        // `array_foreach$fwork<a><tenv>` — a template may take its
        // arguments in several groups, one per quantifier it was
        // declared with.  They select one instance between them, so the
        // groups are concatenated.
        loop {
            self.advance(); // `<`
            if !self.at(&TokenKind::Gt) {
                loop {
                    args.push(self.parse_type()?);
                    if self.at(&TokenKind::Comma) {
                        self.advance();
                    } else {
                        break;
                    }
                }
            }
            self.expect(&TokenKind::Gt, "expected `>` after the type arguments")?;
            if self.at(&TokenKind::Ne)
                && self
                    .tokens
                    .get(self.pos + 1)
                    .is_some_and(|t| t.kind == TokenKind::LParen)
            {
                self.advance();
                break;
            }
            if !(self.at(&TokenKind::Lt) && self.looks_like_template_args()) {
                break;
            }
        }
        while self.at(&TokenKind::LBrace) {
            let save = self.pos;
            self.read_static_group(save);
            self.skip_balanced(&TokenKind::LBrace, &TokenKind::RBrace);
        }
        // Braces and angle brackets name one instance between them, so
        // the brace groups are prepended to whatever the angle groups
        // added.
        if !brace_args.is_empty() {
            args.splice(0..0, brace_args);
        }
        Ok((Some(args), static_args))
    }

    /// Skip the `<...>` / `{...}` arguments that select a template
    /// instantiation, if any are present here.
    ///
    /// `<` is ambiguous with the less-than operator, so a `<` only counts
    /// as an opening bracket when a matching `>` follows with nothing but
    /// names and commas in between, and a `(` after it.

    pub(crate) fn skip_template_arguments(&mut self) {
        while self.at(&TokenKind::LBrace)
            || (self.at(&TokenKind::Lt) && self.looks_like_template_args())
        {
            if self.at(&TokenKind::LBrace) {
                self.skip_balanced(&TokenKind::LBrace, &TokenKind::RBrace);
            } else {
                while !self.at(&TokenKind::Eof) && !self.at(&TokenKind::Gt) {
                    self.advance();
                }
                self.advance(); // `>`
            }
        }
    }

    /// Whether the `<` at the cursor opens a template argument list rather
    /// than being the comparison operator.
    ///
    /// The two are genuinely ambiguous — `f<int>(x)` and `f < int > (x)`
    /// are the same tokens — so the decision rests on what follows the
    /// `>`.  A call is the usual case, but an instance may also be *named*
    /// without being called, as in `macdef g = id<int>`, and there the
    /// `>` is followed by whatever ends the expression.  A comparison
    /// cannot end there, so treating those as template arguments loses
    /// nothing.

    pub(crate) fn parse_params(&mut self) -> Result<Vec<Param>, CompileError> {
        self.parse_params_maybe_untyped(false)
    }

    /// As `parse_params`, but optionally allowing parameters with no
    /// annotation.
    ///
    /// An `implement` may leave them out because the matching `extern`
    /// already said what they are; a `fun` may not, because there is
    /// nowhere else for the information to come from.  An unannotated
    /// parameter is recorded as `_` and resolved against the declaration
    /// when the program is emitted.

    pub(crate) fn parse_params_maybe_untyped(
        &mut self,
        allow_untyped: bool,
    ) -> Result<Vec<Param>, CompileError> {
        self.parse_params_with_policy(allow_untyped, false)
            .map(|(params, _)| params)
    }

    /// Parse declaration parameters while retaining names that are
    /// syntactically ambiguous between a value parameter and an imported type.
    ///
    /// ATS permits `fun f(imported_type): result` without naming the parameter.
    /// Dependency parsing does not yet carry imported type aliases into the
    /// parser, so an unknown bare identifier is provisionally a type here.
    /// `parse_fun_def` rejects that provisional reading if an implementation
    /// body follows, where the identifier necessarily names a value instead.

    pub(crate) fn parse_params_with_unknown_bare_types(
        &mut self,
    ) -> Result<(Vec<Param>, Vec<String>), CompileError> {
        self.parse_params_with_policy(false, true)
    }


    pub(crate) fn parse_params_with_policy(
        &mut self,
        allow_untyped: bool,
        unknown_bare_is_type: bool,
    ) -> Result<(Vec<Param>, Vec<String>), CompileError> {
        let (mut all, mut ambiguous) =
            self.parse_one_param_list(allow_untyped, unknown_bare_is_type)?;
        while self.at(&TokenKind::LParen) {
            let (params, names) = self.parse_one_param_list(allow_untyped, unknown_bare_is_type)?;
            all.extend(params);
            ambiguous.extend(names);
        }
        Ok((all, ambiguous))
    }

    /// Whether a parameter's type is prefixed by a borrow marker.
    ///
    /// `!t` lends a linear value: the caller keeps it and gets it back.
    /// `&t` lends a *cell*: the callee may write through it and may not
    /// consume it.  Both mean the same thing to a resource check — the
    /// value is not being handed over — and neither changes the type,
    /// which is why the marker is read here rather than in `parse_type`.

    pub(crate) fn parse_one_param_list(
        &mut self,
        allow_untyped: bool,
        unknown_bare_is_type: bool,
    ) -> Result<(Vec<Param>, Vec<String>), CompileError> {
        self.expect(
            &TokenKind::LParen,
            "expected `(` to begin the parameter list",
        )?;
        let mut params = Vec::new();
        let mut ambiguous = Vec::new();
        if !self.at(&TokenKind::RParen) {
            loop {
                // `fun f (string, int): int` — a *declaration* may give
                // the types alone, because a signature has no body to
                // name them for.  A generated name keeps the parameter
                let named = (matches!(self.peek().kind, TokenKind::Ident(_)) || self.at(&TokenKind::Underscore))
                    && self.tokens.get(self.pos + 1).is_some_and(|t| {
                        matches!(
                            t.kind,
                            TokenKind::Colon | TokenKind::Comma | TokenKind::RParen
                        )
                    });
                if !named {
                    let borrowed = self.at_borrow_marker();
                    let ty = self.parse_type()?;
                    self.gensym += 1;
                    params.push(Param {
                        borrowed,
                        name: format!("arg${}", self.gensym),
                        ty,
                    });
                    if self.at(&TokenKind::Comma) {
                        self.advance();
                        continue;
                    }
                    break;
                }
                let mut name = if self.at(&TokenKind::Underscore) {
                    self.advance();
                    self.gensym += 1;
                    format!("arg${}", self.gensym)
                } else {
                    self.expect_ident("expected a parameter name")?
                };
                let mut borrowed = false;
                let ty = if self.at(&TokenKind::Colon) {
                    self.advance();
                    borrowed = self.at_borrow_marker();
                    self.parse_type()?
                } else if let Some(known) = well_known_param_type(&name) {
                    // `main`'s two parameters have types fixed by the
                    // language, so ATS lets them go unwritten.
                    known
                } else if self.is_known_type_name(&name) {
                    // `fun f (SHR(list0(INV(a))), int): ...` — a bare
                    // type with no name; a signature need not name its
                    // parameters, so a type name standing alone is a
                    // parameter of that type.
                    self.gensym += 1;
                    let canonical = crate::prelude::canonical_type(&name)
                        .map(|(canonical, _)| canonical)
                        .or_else(|| indexed_base(&name))
                        .unwrap_or(&name);
                    let ty = Ty::Name(canonical.into());
                    name = format!("arg${}", self.gensym);
                    ty
                } else if unknown_bare_is_type {
                    ambiguous.push(name.clone());
                    self.gensym += 1;
                    let ty = Ty::Name(name.clone());
                    name = format!("arg${}", self.gensym);
                    ty
                } else if allow_untyped {
                    Ty::Name("_".into())
                } else {
                    return Err(
                        self.error_here(format!("parameter `{name}` needs a type annotation"))
                    );
                };
                params.push(Param { borrowed, name, ty });
                if self.at(&TokenKind::Comma) {
                    self.advance();
                } else {
                    break;
                }
            }
        }
        self.expect(&TokenKind::RParen, "expected `)` after the parameters")?;
        Ok((params, ambiguous))
    }

    // --- types -----------------------------------------------------

    /// A type, including the modifiers ATS writes in front of one.
    ///
    /// `&t` (by reference), `!t` (a borrowed linear value), and `t?`
    /// (allocated but not yet initialized) all describe how a value is
    /// *handled* rather than what it is.  Since this compiler neither
    /// tracks linearity nor checks initialization, each is transparent:
    /// the underlying type is what survives.

    pub(crate) fn parse_type(&mut self) -> Result<Ty, CompileError> {
        // `[r:int] t` — an existential quantifier in front of the type.
        self.skip_static_annotations();
        let inner = match self.peek().kind {
            TokenKind::Amp | TokenKind::Bang => {
                self.advance();
                return self.parse_type();
            }
            TokenKind::Ident(_) => self.parse_named_type()?,
            // `'{ cmp= (a, a) -> int }` — a record type.  The field name
            // and its type are joined by `=` rather than `:`, which is
            // ATS's spelling and the reason a record cannot be mistaken
            // for a brace-quantifier.
            TokenKind::RecordOpen => {
                self.advance();
                let mut fields = Vec::new();
                while let TokenKind::Ident(name) = self.peek().kind.clone() {
                    self.advance();
                    self.expect(&TokenKind::Eq, "expected `=` after the field name")?;
                    fields.push((name, self.parse_type()?));
                    if self.at(&TokenKind::Comma) {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RBrace, "expected `}` after the record fields")?;
                return self.finish_arrow_type(Ty::Record(fields));
            }
            TokenKind::LParen => self.parse_paren_type()?,
            // `@(t, u)` is the unboxed tuple; `@[t][n]` an array.
            TokenKind::At => {
                self.advance();
                if self.at(&TokenKind::LBracket) {
                    // `@[t][n]` — `n` cells of `t`.  The element type is
                    // kept: an array of ints and an array of strings
                    // differ in what a load off them yields, which is
                    // exactly what the emitter needs to know.
                    self.advance();
                    let elem = self.parse_type()?;
                    if self.at(&TokenKind::RBracket) {
                        self.advance();
                    }
                    // `@[t][n]` — the second bracket is how many cells
                    // there are, which is the only thing that can make a
                    // subscript into it checkable.
                    let mut sizes = Vec::new();
                    while self.at(&TokenKind::LBracket) {
                        let save = self.pos;
                        self.advance();
                        match self.parse_expr(0).ok().as_ref().and_then(sexp_of_expr) {
                            Some(term) if self.at(&TokenKind::RBracket) => {
                                self.advance();
                                sizes.push(term);
                            }
                            _ => {
                                self.pos = save;
                                self.skip_balanced(&TokenKind::LBracket, &TokenKind::RBracket);
                            }
                        }
                    }
                    let base = Ty::App("array".into(), vec![elem]);
                    if sizes.is_empty() {
                        base
                    } else {
                        Ty::Index(Box::new(base), sizes)
                    }
                } else {
                    self.parse_type()?
                }
            }
            TokenKind::Underscore => {
                self.advance();
                Ty::Name("_".into())
            }
            _ => return Err(self.error_here("expected a type")),
        };
        // `t?` — the storage exists, the value does not yet.
        if self.at(&TokenKind::Question) {
            self.advance();
        }
        // `t >> t'` — what the parameter's view becomes once the
        // function returns.  Both sides describe the same machine value;
        // the difference is who may then do what with it, which is a
        // fact about the proof, not about the word.
        if self.at(&TokenKind::Gt)
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|t| t.kind == TokenKind::Gt)
        {
            self.advance();
            self.advance();
            let _after = self.parse_type()?;
        }
        Ok(inner)
    }

    /// `name` or `name(args)`, optionally followed by `-> rest`.

    pub(crate) fn parse_named_type(&mut self) -> Result<Ty, CompileError> {
        let mut name = self.expect_ident("expected a type name")?;
        // `$STDLIB.FILEref` — a type reached through a `staload` alias.
        // The lexer reads `$STDLIB` as one name, and the `.FILEref` is a
        // whole token after it.  This compiler keeps one flat namespace,
        // so the qualifier is dropped and the name stands on its own, as
        // it does in an expression.
        if name.starts_with('$')
            && self.at(&TokenKind::Dot)
            && matches!(
                self.tokens.get(self.pos + 1).map(|t| &t.kind),
                Some(TokenKind::Ident(n)) if !n.starts_with('$')
            )
        {
            self.advance(); // `.`
            name = self.expect_ident("expected a type name")?;
        }
        // `list0@(INV(a), b)` — the `@` between a type former and its
        // arguments is a view/linear marker.  It decorates the type
        // without changing what it is, so it is dropped and the
        // application is read as usual.
        if self.at(&TokenKind::At)
            && matches!(
                self.tokens.get(self.pos + 1).map(|t| &t.kind),
                Some(TokenKind::LParen)
            )
        {
            self.advance(); // `@`
        }
        // A bare alias with no arguments still names the canonical type.
        if let Some((canonical, _)) = crate::prelude::canonical_type(&name) {
            name = canonical.to_string();
        }
        if let Some(canonical) = crate::prelude::canonical_scalar_type(&name) {
            name = canonical.to_string();
        }
        // `int(n)`, `natLt(n+1)`, `string(n)` — the arguments are static
        // terms, not types, so they are read as terms and kept.
        if let Some(base) = indexed_base(&name) {
            let idx = self.parse_index_terms();
            if idx.is_empty() {
                // `Nat` is `[i:nat] int i` — an integer nobody has
                // named, known to be non-negative.  No index is written
                // and the refinement is the whole content of the name,
                // so the name is what survives; only a family that says
                // nothing its base does not collapses to the base.
                let kept = if name == base {
                    base.to_string()
                } else {
                    name.clone()
                };
                return self.finish_arrow_type(Ty::Name(kept));
            }
            // The *family* is kept, not the base it refines.  `intGte(0)`
            // and `int(0)` are the same machine word and different
            // claims — "at least nought" against "is nought" — and
            // collapsing them here told the checker that every bounded
            // integer equals its own bound.  Emission maps the family
            // back to its base, which is the stage that may forget.
            let atom = Ty::Index(Box::new(Ty::Name(name.clone())), idx);
            return self.finish_arrow_type(atom);
        }
        // A proposition is indexed, not applied: `FACT(0, 1)` is about
        // two numbers, and reading them as type arguments loses both.
        if self.props.contains(&name) {
            let idx = self.parse_index_terms();
            if !idx.is_empty() {
                return self.finish_arrow_type(Ty::Index(Box::new(Ty::Name(name)), idx));
            }
            return self.finish_arrow_type(Ty::Name(name));
        }
        // How many of the arguments about to be read are *types*.  For a
        // family this compiler canonicalises — `array(a, n)`,
        // `list(a, n)` — the rest are static indices, and reading them as
        // types is how `array(int, n+1)` fails to parse and `array(int,
        // n)` loses the `n` it was written with.
        let type_arity = crate::prelude::canonical_type(&name).map(|(_, k)| k);
        let atom = if self.at(&TokenKind::LParen) {
            self.advance();
            let mut args = Vec::new();
            let mut sizes: Vec<SExp> = Vec::new();
            loop {
                if type_arity.is_some_and(|k| args.len() >= k) {
                    // Past the type arguments: what remains measures the
                    // value rather than describing it.
                    match self.parse_expr(0).ok().as_ref().and_then(sexp_of_expr) {
                        Some(term) => sizes.push(term),
                        None => break,
                    }
                } else if let Some(ty) = self.parse_type_argument()? {
                    args.push(ty);
                }
                if self.at(&TokenKind::Comma) {
                    self.advance();
                } else {
                    break;
                }
            }
            self.expect(&TokenKind::RParen, "expected `)` after the type arguments")?;
            // `INV(t)` / `OUT(t)` mark a parameter invariant or output-only
            // for the ATS type checker.  They decorate a type without
            // changing it, so — like `&` and `!` — they are transparent.
            if is_variance_annotation(&name) && args.len() == 1 {
                args.into_iter().next().expect("one argument")
            } else if let Some(expanded) = crate::prelude::expand_type_alias(&name, &args) {
                expanded
            } else if self.typedef_families.contains_key(&name) {
                // A parameterized alias means its body with the
                // arguments substituted in.  Expanding here, as the name
                // is read, spares every later stage an alias table.
                self.apply_type_head(name, args)
            } else if let Some((canonical, arity)) = crate::prelude::canonical_type(&name) {
                // `list(t, n)` and `List0(t)` name one type; the length is
                // static, so only the first `arity` arguments describe
                // what the value *is*.
                let mut args = args;
                args.truncate(arity);
                let base = if args.is_empty() {
                    Ty::Name(canonical.into())
                } else {
                    Ty::App(canonical.into(), args)
                };
                // The length is kept *around* that type rather than
                // inside it, so what the value is stays exactly what it
                // was: `erased()` gives back the same type as before, and
                // no later stage can tell the difference.
                if sizes.is_empty() {
                    base
                } else {
                    Ty::Index(Box::new(base), sizes)
                }
            } else if args.is_empty() {
                // A name applied to nothing but index terms is just the
                // name: `int(n)` is an `int`, `intGte(0)` a bounded one.
                Ty::Name(name)
            } else {
                Ty::App(name, args)
            }
        } else {
            Ty::Name(name)
        };
        // A name bound as a type variable is that variable, whatever an
        // alias of the same name says elsewhere.
        let atom = match &atom {
            Ty::Name(n) if !self.type_vars.iter().any(|v| v == n) => {
                self.typedefs.get(n).cloned().unwrap_or(atom)
            }
            _ => atom,
        };
        // `int n`, `size_t i`, `string n` — a type applied to *static*
        // index terms.  The indices refine the type for the ATS type
        // checker; they carry no runtime content, so the base type is
        // kept and the indices are dropped.
        //
        // `bintree a` is different, and the difference is the scope: `a`
        // is a type variable of the enclosing template or datatype, so
        // the juxtaposition is an application, and keeping it is what
        // lets inference later read the element type off the parameter.
        //
        // A word that could begin the *next* declaration is not an index:
        // in `extern fun f (x: a): a extern fun g ...` the return type is
        // `a`, and swallowing the `extern` after it would glue the two
        // declarations together.
        //
        // Some formers take a *type* there whatever the name is:
        // `stream N2` is `stream(N2)`, and reading `N2` as an index
        // would throw the element type away.  Those are known by name,
        // because knowing them is exactly what a type checker's sort
        // information would otherwise supply.
        let head_wants_a_type = match &atom {
            Ty::Name(n) | Ty::App(n, _) => crate::prelude::takes_a_type_argument(n),
            _ => false,
        };
        let mut ty_args: Vec<Ty> = Vec::new();
        loop {
            match &self.peek().kind {
                TokenKind::IntLit(_) => {}
                TokenKind::Ident(w) if !starts_a_declaration(w) => {
                    if self.type_vars.iter().any(|v| v == w)
                        || (head_wants_a_type && ty_args.is_empty())
                    {
                        let w = w.clone();
                        self.advance();
                        // An alias means what it was declared to mean,
                        // unless a type variable of that name is in
                        // scope, which shadows it.
                        let bound = self.type_vars.iter().any(|v| *v == w);
                        ty_args.push(if bound {
                            Ty::Name(w)
                        } else {
                            self.typedefs.get(&w).cloned().unwrap_or(Ty::Name(w))
                        });
                        continue;
                    }
                }
                _ => break,
            }
            self.advance();
        }
        // Juxtaposition applies the type to the type arguments: `bintree
        // a` is `bintree(a)`.  When the head was already applied
        // (`list(int) a`), the arguments extend it.
        let atom = if ty_args.is_empty() {
            atom
        } else {
            match atom {
                Ty::Name(n) => self.apply_type_head(n, ty_args),
                Ty::App(n, mut args) => {
                    args.extend(ty_args);
                    self.apply_type_head(n, args)
                }
                other => other,
            }
        };
        self.finish_arrow_type(atom)
    }

    /// A type name applied to arguments, with a parameterized alias
    /// expanded.
    ///
    /// `ordmod a` and `ordmod (a)` are the same type written two ways,
    /// so the expansion has to happen for both — and the juxtaposed
    /// spelling arrives here rather than through the parenthesized path.

    pub(crate) fn apply_type_head(&self, name: String, args: Vec<Ty>) -> Ty {
        if let Some((params, body)) = self.typedef_families.get(&name) {
            if params.len() == args.len() {
                let subst: HashMap<String, Ty> =
                    params.iter().cloned().zip(args.into_iter()).collect();
                return substitute_type(body, &subst);
            }
            return Ty::App(name, args);
        }
        Ty::App(name, args)
    }

    /// One argument of a type application.
    ///
    /// ATS writes types and *static index terms* in the same argument
    /// list: `list(int, n)` carries an element type and a length,
    /// `intGte(0)` a lower bound, `int(fact(n))` an arithmetic term.  An
    /// index describes no runtime value, so when an argument does not
    /// parse as a type it is consumed and contributes nothing — which is
    /// exactly the treatment the rest of the static language gets.

    pub(crate) fn parse_type_argument(&mut self) -> Result<Option<Ty>, CompileError> {
        let save = self.pos;
        if let Ok(ty) = self.parse_type() {
            // A type it may be, but only if the whole argument was eaten.
            if self.at(&TokenKind::Comma) || self.at(&TokenKind::RParen) {
                return Ok(Some(ty));
            }
        }
        self.pos = save;
        self.skip_type_argument();
        Ok(None)
    }

    /// Consume one argument of a type application without interpreting it.

    pub(crate) fn skip_type_argument(&mut self) {
        let mut depth = 0i32;
        loop {
            match &self.peek().kind {
                TokenKind::Eof => return,
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen if depth == 0 => return,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
                TokenKind::Comma if depth == 0 => return,
                _ => {}
            }
            let before = self.pos;
            self.advance();
            if self.pos == before {
                return;
            }
        }
    }

    /// A parenthesized type: `()`, `(t)`, `(t, u) -> v`, or a tuple.

    pub(crate) fn parse_paren_type(&mut self) -> Result<Ty, CompileError> {
        self.advance();
        if self.at(&TokenKind::RParen) {
            self.advance();
            if self.eat_arrow() {
                let ret = self.parse_type()?;
                return Ok(Ty::Fun(vec![], Box::new(ret)));
            }
            return Ok(Ty::Name("void".into()));
        }
        let mut items = vec![self.parse_type()?];
        while self.at(&TokenKind::Comma) {
            self.advance();
            items.push(self.parse_type()?);
        }
        // `(PROOF | t)` — a value of type `t` that carries a proof about
        // itself.  The proof is erased before anything runs, so `t` is
        // what the value *is* — but the proposition is kept, because it
        // is where the interesting index usually lives.
        let mut proof = None;
        if self.at(&TokenKind::Pipe) {
            self.advance();
            proof = items.pop();
            items = vec![self.parse_type()?];
            while self.at(&TokenKind::Comma) {
                self.advance();
                items.push(self.parse_type()?);
            }
        }
        self.expect(&TokenKind::RParen, "expected `)` after the type list")?;
        if let (Some(proof), 1) = (proof, items.len()) {
            let value = items.pop().expect("checked");
            return self.finish_arrow_type(Ty::Proof(Box::new(proof), Box::new(value)));
        }
        if self.eat_arrow() {
            let ret = self.parse_type()?;
            Ok(Ty::Fun(items, Box::new(ret)))
        } else if items.len() == 1 {
            Ok(items.into_iter().next().expect("one item"))
        } else {
            Ok(Ty::Tuple(items))
        }
    }

    /// The static terms indexing a type: `(n, m)` after the name, or the
    /// juxtaposed form `int n` that ATS also allows.
    ///
    /// A term outside the fragment this compiler reads is dropped rather
    /// than refused: an index nobody can interpret is a fact nobody can
    /// check, which is a loss of precision, not a parse failure.

    pub(crate) fn parse_index_terms(&mut self) -> Vec<SExp> {
        let mut idx = Vec::new();
        if self.at(&TokenKind::LParen) {
            self.advance();
            if !self.at(&TokenKind::RParen) {
                loop {
                    match self.parse_expr(0) {
                        Ok(e) => idx.extend(sexp_of_expr(&e)),
                        Err(_) => break,
                    }
                    if self.at(&TokenKind::Comma) {
                        self.advance();
                    } else {
                        break;
                    }
                }
            }
            if self.at(&TokenKind::RParen) {
                self.advance();
            }
            return idx;
        }
        // `int n` — the same thing without parentheses.  Only a single
        // atom may follow, and a word that could begin the next
        // declaration is not an index but the start of one.
        loop {
            match self.peek().kind.clone() {
                TokenKind::IntLit(n) => {
                    self.advance();
                    idx.push(SExp::IntLit(n));
                }
                TokenKind::Ident(w) if !starts_a_declaration(&w) => {
                    self.advance();
                    idx.push(SExp::Var(w));
                }
                _ => break,
            }
        }
        idx
    }

    /// Consume an arrow, whatever effects it carries, and report whether
    /// there was one.
    ///
    /// ATS writes a function type's effects on the arrow itself:
    /// `-<cloref1>` is a closure, `-<fun1>` a plain function,
    /// `-<lin,prf>` a linear proof function.  What may call it and what
    /// it may do are questions for the type checker and change nothing
    /// about the machine code, so the effects are read and dropped —
    /// but the *arrow* has to be recognised, or the type after it reads
    /// as a subtraction.

    pub(crate) fn finish_arrow_type(&mut self, atom: Ty) -> Result<Ty, CompileError> {
        if self.eat_arrow() {
            let ret = self.parse_type()?;
            Ok(Ty::Fun(vec![atom], Box::new(ret)))
        } else {
            Ok(atom)
        }
    }

    // --- expressions -----------------------------------------------
}
