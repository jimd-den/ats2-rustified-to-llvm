use super::context::*;
use super::decode::*;
use super::patterns::*;
use super::types::*;
use ats2_domain::ast::*;
use ats2_domain::errors::CompileError;
use ats2_domain::statics::*;
use ats2_domain::tokens::*;
use std::collections::{HashMap, HashSet};


impl<'a> ParseCtx<'a> {
    pub(crate) fn parse_expr(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
        let mut lhs = self.parse_prefix(min_bp)?;
        loop {
            // `x :: xs` — cons.  It is an ordinary constructor wearing
            // infix clothes, so it is folded straight into the call the
            // prefix spelling would have produced.  Right-associative,
            // because a list grows at its head.
            if self.at(&TokenKind::ColonColon) && CONS_BP >= min_bp {
                self.advance();
                let rhs = self.parse_expr(CONS_BP)?;
                let cons = self.cons_name.clone();
                lhs = Expr::Call(Box::new(Expr::Var(cons)), vec![lhs, rhs]);
                continue;
            }
            let Some((op, lbp, rbp)) = self.current_binop() else {
                break;
            };
            if lbp < min_bp {
                break;
            }
            self.advance();
            let rhs = self.parse_expr(rbp)?;
            lhs = Expr::BinOp(op, Box::new(lhs), Box::new(rhs));
        }
        // `e : t` — an ascription.  It says what `e` should be, which is
        // a *claim*, and there is a checker to tell now: `(if n >= 0
        // then n else 0): intGte(0)` is how a program turns an integer
        // nobody can bound into one that is bounded, and it is the only
        // line in the file that says so.
        if self.at(&TokenKind::Colon) && min_bp == 0 {
            self.advance();
            let ascribed = self.parse_type()?;
            lhs = Expr::Ascribe(Box::new(lhs), ascribed);
        }
        // `x := e`, and the compound `x :=+ e` which means `x := x + e`.
        // Assignment binds loosest of all, so it is matched after the
        // operator loop has taken everything it wants.
        if self.at(&TokenKind::ColonEq) {
            self.advance();
            // `a :=: b` — swap.  The lexer reads it as `:=` then `:`.
            //
            // Desugared here into "read one, write the other, write
            // back", which is what a swap is.  The two places are named
            // twice each; in ATS a place is an address computation, so
            // naming one twice costs an extra index but changes nothing.
            if self.at(&TokenKind::Colon) {
                self.advance();
                let rhs = self.parse_expr(0)?;
                self.gensym += 1;
                let tmp = format!("swap${}", self.gensym);
                return Ok(Expr::Let(
                    vec![
                        LetBind {
                            opened: Vec::new(),
                            proof: false,
                            name: Some(tmp.clone()),
                            ty: None,
                            value: lhs.clone(),
                            mutable: false,
                        },
                        LetBind {
                            opened: Vec::new(),
                            proof: false,
                            name: None,
                            ty: None,
                            value: Expr::Store(Box::new(lhs), Box::new(rhs.clone())),
                            mutable: false,
                        },
                        LetBind {
                            opened: Vec::new(),
                            proof: false,
                            name: None,
                            ty: None,
                            value: Expr::Store(Box::new(rhs), Box::new(Expr::Var(tmp))),
                            mutable: false,
                        },
                    ],
                    Box::new(Expr::Unit),
                ));
            }
            // A projection is a place too, so `xx.0 := e` is a store
            // into that slot rather than a rebinding of a name.
            if matches!(
                lhs,
                Expr::Proj(..) | Expr::Index(..) | Expr::Deref(..) | Expr::Field(..)
            ) {
                let compound = self.compound_assign_op();
                if compound.is_some() {
                    self.advance();
                }
                let rhs = self.parse_expr(0)?;
                let value = match compound {
                    Some(op) => Expr::BinOp(op, Box::new(lhs.clone()), Box::new(rhs)),
                    None => rhs,
                };
                return Ok(Expr::Store(Box::new(lhs), Box::new(value)));
            }
            let Expr::Var(target) = lhs else {
                return Err(self.error_here("only a `var` cell or a tuple slot can be assigned to"));
            };
            let compound = self.compound_assign_op();
            if compound.is_some() {
                self.advance();
            }
            let rhs = self.parse_expr(0)?;
            let value = match compound {
                Some(op) => Expr::BinOp(op, Box::new(Expr::Var(target.clone())), Box::new(rhs)),
                None => rhs,
            };
            return Ok(Expr::Assign(target, Box::new(value)));
        }
        // `e where { decls }` — the same scope a `let` opens, written
        // after the expression that uses it instead of before.
        if matches!(&self.peek().kind, TokenKind::Ident(w) if w == "where") {
            self.advance();
            self.expect(&TokenKind::LBrace, "expected `{` after `where`")?;
            let (binds, funs, pending) = self.parse_local_decls_and_funs()?;
            self.expect(
                &TokenKind::RBrace,
                "expected `}` to close the `where` block",
            )?;
            let inner = if binds.is_empty() {
                lhs
            } else {
                Expr::Let(binds, Box::new(lhs))
            };
            let inner = match pending {
                Some((pattern, value)) => must_match(value, pattern, inner),
                None => inner,
            };
            lhs = wrap_funs(funs, inner);
        }
        Ok(lhs)
    }

    /// The operator of a compound assignment (`:=+`, `:=-`, `:=*`,
    /// `:=/`), if the cursor is sitting on one.

    pub(crate) fn compound_assign_op(&self) -> Option<BinOp> {
        match self.peek().kind {
            TokenKind::Plus => Some(BinOp::Add),
            TokenKind::Minus => Some(BinOp::Sub),
            TokenKind::Star => Some(BinOp::Mul),
            TokenKind::Slash => Some(BinOp::Div),
            _ => None,
        }
    }

    /// A prefix expression plus any chained call applications.

    pub(crate) fn parse_prefix(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
        let mut expr = match self.peek().kind {
            TokenKind::Tilde | TokenKind::Minus => {
                self.advance();
                let operand = self.parse_expr(UNARY_BP)?;
                Expr::UnaryNeg(Box::new(operand))
            }
            // `!p` — read through a pointer.  The postfix loop below then
            // applies to the value read, so `!p.[i]` indexes the array
            // the pointer leads to rather than the pointer.
            TokenKind::Bang => {
                self.advance();
                let operand = self.parse_primary(min_bp)?;
                Expr::Deref(Box::new(operand))
            }
            _ => self.parse_primary(min_bp)?,
        };
        // Application and indexing are both postfix and bind equally
        // tightly, so they are taken in one loop: `f(x)[0](y)` works.
        loop {
            if self.at(&TokenKind::LParen) {
                self.advance();
                let mut args = Vec::new();
                if !self.at(&TokenKind::RParen) {
                    loop {
                        args.push(self.parse_expr(0)?);
                        // `f (pf | x, y)` — everything before the bar is
                        // proof, and proof does not survive to run time.
                        if self.at(&TokenKind::Pipe) {
                            self.advance();
                            args.clear();
                            continue;
                        }
                        if self.at(&TokenKind::Comma) {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                }
                self.expect(&TokenKind::RParen, "expected `)` after the arguments")?;
                expr = Expr::Call(Box::new(expr), args);
            } else if self.at(&TokenKind::Dot)
                && matches!(
                    self.tokens.get(self.pos + 1).map(|t| &t.kind),
                    Some(TokenKind::IntLit(_))
                )
            {
                // `xs.0` — a tuple projection.  The lexer only glues a
                // dot into a number when digits came *before* it, so the
                // slot arrives here as its own integer token.
                self.advance();
                let TokenKind::IntLit(n) = self.peek().kind.clone() else {
                    unreachable!()
                };
                self.advance();
                expr = Expr::Proj(Box::new(expr), n as usize);
            } else if self.at(&TokenKind::Dot)
                && self
                    .tokens
                    .get(self.pos + 1)
                    .is_some_and(|t| t.kind == TokenKind::LBracket)
            {
                // `A.[i]` or `A.[]` — ATS's array subscript / cell dereference.
                self.advance();
                self.advance();
                if self.at(&TokenKind::RBracket) {
                    self.advance();
                    expr = Expr::Index(Box::new(expr), Box::new(Expr::IntLit(0)));
                } else {
                    let index = self.parse_expr(0)?;
                    self.expect(&TokenKind::RBracket, "expected `]` after the index")?;
                    expr = Expr::Index(Box::new(expr), Box::new(index));
                }
            } else if self.at(&TokenKind::Dot)
                && matches!(
                    self.tokens.get(self.pos + 1).map(|t| &t.kind),
                    Some(TokenKind::Ident(_))
                )
            {
                // `r.cmp` is a *field*; `str.tail()` is dot notation,
                // which in ATS is application with the receiver first
                // (`tail(str)`).  The two are the same syntax, and only
                // the type of what is left of the dot separates them —
                // so the choice is left to the emitter, which has it.
                // Any arguments are picked up by the `(` case on the
                // next turn of this loop, exactly as for any other
                // callee.
                self.advance();
                let TokenKind::Ident(field) = self.peek().kind.clone() else {
                    unreachable!()
                };
                self.advance();
                expr = Expr::Field(Box::new(expr), field);
            } else if self.at(&TokenKind::Arrow)
                && matches!(
                    self.tokens.get(self.pos + 1).map(|t| &t.kind),
                    Some(TokenKind::Ident(_))
                )
            {
                // `p->f` — a field reached *through* a pointer, ATS's
                // shorthand for `(!p).f`.  The pointer is read and the
                // field taken in one step: nothing reads the pointer alone.
                self.advance();
                let TokenKind::Ident(field) = self.peek().kind.clone() else {
                    unreachable!()
                };
                self.advance();
                expr = Expr::Field(Box::new(Expr::Deref(Box::new(expr))), field);
            } else if self.at(&TokenKind::LBracket) {
                self.advance();
                if self.at(&TokenKind::RBracket) {
                    self.advance();
                    expr = Expr::Index(Box::new(expr), Box::new(Expr::IntLit(0)));
                } else {
                    let index = self.parse_expr(0)?;
                    self.expect(&TokenKind::RBracket, "expected `]` after the index")?;
                    expr = Expr::Index(Box::new(expr), Box::new(index));
                }
            } else if matches!(expr, Expr::Var(_) | Expr::Inst(..)) && self.at(&TokenKind::LBrace) {
                // `f{a}(x)` or `f{a,b}(x)` — static template argument application.
                self.advance(); // `{`
                let mut depth = 1;
                while depth > 0 && !self.at(&TokenKind::Eof) {
                    if self.at(&TokenKind::LBrace) {
                        depth += 1;
                    } else if self.at(&TokenKind::RBrace) {
                        depth -= 1;
                    }
                    self.advance();
                }
            } else if matches!(expr, Expr::Var(_) | Expr::Inst(..))
                && self.starts_a_juxtaposed_argument()
            {
                // `succ i`, `pred n`, `free bt1` — application written
                // without parentheses, which ATS allows and the prelude
                // uses constantly.
                //
                // Only a *name* may be applied this way, and only to a
                // single atom.  The restriction is what keeps the
                // ambiguity manageable: two expressions never sit side
                // by side in ATS without a separator, but relaxing
                // either half would make `f (x)` and `f\n(x)` differ, or
                // let a declaration's first word be eaten as an
                // argument.
                let arg = self.parse_primary(min_bp)?;
                expr = Expr::Call(Box::new(expr), vec![arg]);
            } else {
                break;
            }
        }
        Ok(expr)
    }

    /// Whether the token here can only be an argument applied to the
    /// name just read.
    ///
    /// Deliberately narrow: a word that could begin a declaration is not
    /// an argument, and neither is anything that needs its own
    /// operator-precedence parse.

    pub(crate) fn starts_a_juxtaposed_argument(&self) -> bool {
        match &self.peek().kind {
            TokenKind::Ident(w) => !starts_a_declaration(w),
            TokenKind::IntLit(_) | TokenKind::CharLit(_) | TokenKind::StrLit(_) => true,
            // `setmod_make_order<int> '{ cmp= ... }` — a record is an
            // argument like any other, and one written this way is how
            // ATS passes a module.
            TokenKind::RecordOpen => true,
            // `f ,(x)` — a macro splice is an argument like any other,
            // but only inside a macro body, and only when a `(` follows.
            // A comma with anything else after it is separating two
            // arguments, and reading it as a splice would swallow the
            // separator and then fail on what came next.
            TokenKind::Comma if self.macro_depth > 0 => self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|t| t.kind == TokenKind::LParen),
            _ => false,
        }
    }


    pub(crate) fn parse_primary(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
        match self.peek().kind.clone() {
            TokenKind::IntLit(n) => {
                self.advance();
                Ok(Expr::IntLit(n))
            }
            TokenKind::CharLit(b) => {
                self.advance();
                Ok(Expr::CharLit(b))
            }
            TokenKind::FloatLit(v) => {
                self.advance();
                Ok(Expr::FloatLit(v))
            }
            TokenKind::True => {
                self.advance();
                Ok(Expr::BoolLit(true))
            }
            TokenKind::False => {
                self.advance();
                Ok(Expr::BoolLit(false))
            }
            TokenKind::StrLit(raw) => {
                let span = self.peek().span;
                self.advance();
                Ok(Expr::StrLit(decode_string(&raw, span)?))
            }
            // `,(e)` — a macro splice.  The comma is the marker ATS's
            // macro language prefixes an interpolated expression with;
            // here the expression is already an ordinary one, so the
            // comma is read and dropped.  It only has this meaning
            // inside a macro body — everywhere else a comma separates.
            TokenKind::Comma if self.macro_depth > 0 => {
                self.advance();
                self.expect(&TokenKind::LParen, "expected `(` after the splice comma")?;
                let e = self.parse_expr(0)?;
                self.expect(
                    &TokenKind::RParen,
                    "expected `)` after the spliced expression",
                )?;
                Ok(e)
            }
            // `$UN.cast(x)`, `$STDLIB.drand48()` — a name qualified by
            // the `staload` alias it came through.  The lexer reads
            // `$UN` as one name, so the qualifier is a whole token here.
            // Which file a name was declared in matters to ATS's
            // namespacing and to nothing else, so it is dropped and the
            // name stands on its own.
            TokenKind::Ident(q)
                if q.starts_with('$')
                    && self
                        .tokens
                        .get(self.pos + 1)
                        .is_some_and(|t| t.kind == TokenKind::Dot)
                    && matches!(
                        self.tokens.get(self.pos + 2).map(|t| &t.kind),
                        Some(TokenKind::Ident(_))
                    ) =>
            {
                self.advance();
                self.advance();
                self.parse_primary(min_bp)
            }
            // `$extval(T, "c_fn", args...)` / `$extfcall(T, "c_fn", ...)`
            // — a value or call written in C's terms.  The first argument
            // is a *type* ATS sees, the second the C spelling, the rest
            // ordinary arguments.  It cannot ride the ordinary-call path:
            // a type in argument position would be read as a variable and
            // the emitter would go looking for a function nobody declared.
            TokenKind::Ident(name) if name == "$extval" || name == "$extfcall" => {
                let via_ptr = name == "$extfcall";
                self.advance(); // the name
                self.expect(&TokenKind::LParen, "expected `(` after the external name")?;
                let ty = self.parse_type()?;
                self.expect(&TokenKind::Comma, "expected `,` after the external type")?;
                let span = self.peek().span;
                let TokenKind::StrLit(raw) = self.peek().kind.clone() else {
                    return Err(self.error_here("expected the C name as a string literal"));
                };
                self.advance();
                let name = decode_string(&raw, span)?;
                let mut args = Vec::new();
                if self.at(&TokenKind::Comma) {
                    self.advance();
                    loop {
                        args.push(self.parse_expr(0)?);
                        if self.at(&TokenKind::Comma) {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                }
                self.expect(&TokenKind::RParen, "expected `)` after the external call")?;
                Ok(Expr::ExtVal {
                    ty,
                    name,
                    args,
                    via_ptr,
                })
            }
            TokenKind::Ident(name) if self.macros.contains_key(&name) => {
                self.advance();
                Ok(self.macros[&name].clone())
            }
            TokenKind::Ident(name) if self.macro_funs.contains_key(&name) => {
                // `size (bt)`, or `free bt` for a one-parameter macro —
                // a parameterized macro used.  The arguments are read
                // here and spliced into the body for the parameters, so
                // what the rest of the parser sees is the expansion,
                // never the macro.
                let paren = self
                    .tokens
                    .get(self.pos + 1)
                    .is_some_and(|t| t.kind == TokenKind::LParen);
                let juxta = {
                    let params_len = self.macro_funs[&name].0.len();
                    let next = self.tokens.get(self.pos + 1).map(|t| &t.kind);
                    params_len == 1
                        && match next {
                            Some(TokenKind::Ident(w)) => !starts_a_declaration(w),
                            Some(
                                TokenKind::IntLit(_)
                                | TokenKind::CharLit(_)
                                | TokenKind::StrLit(_)
                                | TokenKind::LParen,
                            ) => true,
                            _ => false,
                        }
                };
                if !paren && !juxta {
                    // The name alone is not a use of the macro; treat it
                    // as an ordinary variable and let the caller say.
                    self.advance();
                    Ok(Expr::Var(name))
                } else {
                    self.advance(); // the name
                    let args = if paren {
                        self.advance(); // `(`
                        let mut args = Vec::new();
                        if !self.at(&TokenKind::RParen) {
                            loop {
                                args.push(self.parse_expr(0)?);
                                if self.at(&TokenKind::Comma) {
                                    self.advance();
                                } else {
                                    break;
                                }
                            }
                        }
                        self.expect(&TokenKind::RParen, "expected `)` after the macro arguments")?;
                        args
                    } else {
                        vec![self.parse_primary(min_bp)?]
                    };
                    let (params, body) = &self.macro_funs[&name];
                    Ok(splice_macro_args(body, params, &args))
                }
            }
            TokenKind::Ident(name) if matches!(name.as_str(), "llam" | "fix" | "fix@") => {
                self.parse_lam()
            }
            // `begin e1; e2 end` — ATS's word for a parenthesized
            // sequence.  It is not a keyword in the lexer because it is
            // an ordinary name everywhere else, so it is recognised here.
            TokenKind::Ident(name) if name == "begin" => {
                self.advance();
                let mut items = Vec::new();
                while !self.at(&TokenKind::End) && !self.at(&TokenKind::Eof) {
                    items.push(self.parse_expr(0)?);
                    if self.at(&TokenKind::Semicolon) {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::End, "expected `end` to close `begin`")?;
                Ok(sequence(items))
            }
            // `$list{int}(1, 2, 3)` — list-literal syntax.  It is
            // nothing but the conses it stands for, so it is desugared
            // here: everything downstream then sees an ordinary list,
            // and inference can read the element type off it.
            TokenKind::Ident(name)
                if matches!(
                    name.as_str(),
                    "$list" | "$lst" | "$list_vt" | "$listlst" | "$arrpsz"
                ) =>
            {
                self.advance();
                let _element = self.parse_template_arguments()?;
                self.expect(&TokenKind::LParen, "expected `(` after a list literal")?;
                let mut items = Vec::new();
                if !self.at(&TokenKind::RParen) {
                    loop {
                        items.push(self.parse_expr(0)?);
                        if self.at(&TokenKind::Comma) {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                }
                self.expect(&TokenKind::RParen, "expected `)` after the list elements")?;
                // `$list{int}(...)` names the element type, and nothing
                // else in the desugared form would: a list literal often
                // stands where no annotation reaches it, and then the
                // braces are the only thing that says which instance of
                // the datatype is being built.
                let ctor = |n: &str| match &_element {
                    Some(args) if !args.is_empty() => Expr::Inst(n.into(), args.clone()),
                    _ => Expr::Var(n.into()),
                };
                let mut list = Expr::Call(Box::new(ctor("list0_nil")), Vec::new());
                for item in items.into_iter().rev() {
                    list = Expr::Call(Box::new(ctor("list0_cons")), vec![item, list]);
                }
                Ok(list)
            }
            // `$delay(e)` / `$ldelay(e, cleanup)` — a suspended
            // computation.  Suspending is exactly what a nullary lambda
            // does, so the body is wrapped in one here and the emitter
            // is left with the one thing a lambda cannot express: the
            // cell that remembers the answer.
            //
            // `$ldelay`'s second argument says how to free the stream if
            // it is dropped unforced.  The arena frees everything at
            // once, so it is read and dropped.
            // `$raise SomeExn(x)` — throw the exception value it names.
            TokenKind::Ident(name) if name == "$raise" => {
                self.advance();
                let exn = self.parse_prefix(min_bp)?;
                Ok(Expr::Raise(Box::new(exn)))
            }
            TokenKind::Ident(name) if name == "$delay" || name == "$ldelay" => {
                self.advance();
                self.expect(&TokenKind::LParen, "expected `(` after `$delay`")?;
                let body = self.parse_expr(0)?;
                while self.at(&TokenKind::Comma) {
                    self.advance();
                    let _cleanup = self.parse_expr(0)?;
                }
                self.expect(
                    &TokenKind::RParen,
                    "expected `)` after the delayed expression",
                )?;
                Ok(Expr::Call(
                    Box::new(Expr::Var("$delay".into())),
                    vec![Expr::Lam(Vec::new(), None, Box::new(body))],
                ))
            }
            // `try e with | p => h` — `try` is an identifier (not a
            // keyword), so it must be caught before the general
            // identifier arm reads it as a function call.
            TokenKind::Ident(w) if w == "try" => self.parse_try(min_bp),
            TokenKind::Ident(name) => {
                self.advance();
                // `addr@ x`, `view@ (x)` — the `@` belongs to the name,
                // but `@` is an operator elsewhere, so the lexer cannot
                // know that and the pieces are rejoined here.
                let name = if self.at(&TokenKind::At) {
                    self.advance();
                    format!("{name}@")
                } else {
                    name
                };
                // `#define cons stream_vt_cons` — the name is standing
                // for another one, and it must stand for it here just as
                // it does in a pattern.
                let name = self.renames.get(&name).cloned().unwrap_or(name);
                // `fold@ x`, `free@ x` — the two view primitives that
                // *do* something rather than name something.  What they
                // do is rearrange the proofs describing a value, which
                // exist only for the type checker; the value is
                // untouched.  So each reads its operand and evaluates to
                // unit.
                if name == "fold@" || name == "free@" {
                    let _operand = self.parse_primary(min_bp)?;
                    return Ok(Expr::Unit);
                }
                // `f<int>(x)` names the instance wanted.  The types are
                // kept — monomorphisation needs them — while `f{...}(x)`
                // supplies *static* arguments, which are erased.
                let (ty_args, at) = self.parse_instantiation()?;
                if let Some(ty_args) = ty_args {
                    // The group read as types, so that is what it is
                    // called here.  `{n}` is ambiguous — a type argument
                    // and an index argument look identical — and only the
                    // callee's quantifiers can say which was meant, so
                    // the checker re-reads a type argument as an index
                    // when the signature it is calling wants one.
                    return Ok(Expr::Inst(name, ty_args));
                }
                // `{n, 0}`, `{n+1}` — a group no reading as types
                // survives.  It can only be static, and it is kept,
                // because `fact_ind{n}()` and `fact_ind{m}()` are the
                // same code and different claims.
                if !at.is_empty() {
                    return Ok(Expr::StaticInst(Box::new(Expr::Var(name)), at));
                }
                if self.at(&TokenKind::Bang) {
                    self.advance();
                    self.expect(&TokenKind::LParen, "expected `(` after the macro name")?;
                    let mut args = Vec::new();
                    if !self.at(&TokenKind::RParen) {
                        loop {
                            args.push(self.parse_expr(0)?);
                            if self.at(&TokenKind::Comma) {
                                self.advance();
                            } else {
                                break;
                            }
                        }
                    }
                    self.expect(&TokenKind::RParen, "expected `)` after the macro arguments")?;
                    Ok(Expr::MacroCall(format!("{name}!"), args))
                } else {
                    Ok(Expr::Var(name))
                }
            }
            TokenKind::LParen => {
                self.advance();
                if self.at(&TokenKind::RParen) {
                    self.advance();
                    return Ok(Expr::Unit);
                }
                let mut items = vec![self.parse_expr(0)?];
                // `(pf | v)` — a value returned together with a proof
                // about it.  The proof is erased before anything runs;
                // it is kept because it is what determines the
                // existential the function promised.
                let mut proof = None;
                if self.at(&TokenKind::Pipe) {
                    self.advance();
                    proof = items.pop();
                    items = vec![self.parse_expr(0)?];
                }
                if let (Some(proof), true) = (&proof, self.at(&TokenKind::RParen)) {
                    let value = items.pop().expect("a value half");
                    self.advance();
                    return Ok(Expr::ProofPair(Box::new(proof.clone()), Box::new(value)));
                }
                // `(a, b)` is a tuple: the comma builds a value.
                if self.at(&TokenKind::Comma) {
                    while self.at(&TokenKind::Comma) {
                        self.advance();
                        items.push(self.parse_expr(0)?);
                    }
                    self.expect(&TokenKind::RParen, "expected `)` after the tuple")?;
                    return Ok(Expr::TupleLit(items));
                }
                // `(a; b; c)` — a sequence.  Each element but the last is
                // run for its effect only, which is exactly a discard
                // binding, so the whole thing folds into nested `let`s
                // rather than earning an AST node of its own.
                while self.at(&TokenKind::Semicolon) {
                    self.advance();
                    items.push(self.parse_expr(0)?);
                }
                self.expect(
                    &TokenKind::RParen,
                    "expected `)` after the parenthesized expression",
                )?;
                let mut it = items.into_iter().rev();
                let mut expr = it.next().expect("at least one element");
                for earlier in it {
                    expr = Expr::Let(
                        vec![LetBind {
                            opened: Vec::new(),
                            proof: false,
                            name: None,
                            ty: None,
                            value: earlier,
                            mutable: false,
                        }],
                        Box::new(expr),
                    );
                }
                Ok(expr)
            }
            TokenKind::Underscore => {
                self.advance();
                Ok(Expr::Wildcard)
            }
            // `@(a, b)` — the unboxed tuple.  The subset gives boxed and
            // unboxed tuples one representation, so they parse alike.
            TokenKind::At
                if self
                    .tokens
                    .get(self.pos + 1)
                    .is_some_and(|t| t.kind == TokenKind::LParen) =>
            {
                self.advance();
                self.parse_primary(min_bp)
            }
            // `'{ x= 1, y= 2 }` — a record value.
            TokenKind::RecordOpen => {
                self.advance();
                let mut fields = Vec::new();
                while let TokenKind::Ident(name) = self.peek().kind.clone() {
                    self.advance();
                    self.expect(&TokenKind::Eq, "expected `=` after the field name")?;
                    fields.push((name, self.parse_expr(0)?));
                    if self.at(&TokenKind::Comma) {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RBrace, "expected `}` after the record fields")?;
                Ok(Expr::RecordLit(fields))
            }
            TokenKind::If => self.parse_if(min_bp),
            TokenKind::Let => self.parse_let(min_bp),
            TokenKind::LBrace => self.parse_block(min_bp),
            TokenKind::Case => self.parse_case(),
            TokenKind::While => self.parse_while(),
            TokenKind::For => self.parse_for(),
            TokenKind::Lam => self.parse_lam(),
            _ => Err(self.error_here("expected an expression")),
        }
    }


    pub(crate) fn parse_if(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
        self.advance(); // `if`
        let cond = self.parse_expr(0)?;
        self.expect(&TokenKind::Then, "expected `then` after the condition")?;
        let then_e = self.parse_expr(min_bp)?;
        // `if c then e` with no `else` is a *statement*: the missing arm
        // is unit, and the whole form has type void.
        let else_e = if self.at(&TokenKind::Else) {
            self.advance();
            self.parse_expr(min_bp)?
        } else {
            Expr::Unit
        };
        Ok(Expr::IfThenElse(
            Box::new(cond),
            Box::new(then_e),
            Box::new(else_e),
        ))
    }


    pub(crate) fn parse_let(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
        self.advance(); // `let`
        self.parse_let_rest(min_bp)
    }

    /// The declarations and body of a `let ... in ... end`, once the
    /// keyword has been consumed.
    ///
    /// A pattern binding ends the declaration run and scopes over
    /// everything that follows — the rest of the run, the `in` body, the
    /// `end` — so the remainder is parsed as a nested let and wrapped in
    /// a match with no fallback: the source says the pattern holds, and
    /// a program where it does not is wrong and says so by leaving.

    pub(crate) fn parse_let_rest(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
        let (binds, funs, pending) = self.parse_local_decls_and_funs()?;
        let inner = match pending {
            Some((pattern, value)) => {
                let rest = self.parse_let_rest(min_bp)?;
                must_match(value, pattern, rest)
            }
            None => {
                self.expect(&TokenKind::In, "expected `in` after the bindings")?;
                // `in e1; e2 end` — the body may be a sequence, the
                // same way a parenthesized one may be.  The semicolon
                // separates *expressions* here, which is why it is read
                // by the body and not by the declaration run.
                let mut items = Vec::new();
                while !self.at(&TokenKind::End) && !self.at(&TokenKind::Eof) {
                    items.push(self.parse_expr(min_bp)?);
                    if self.at(&TokenKind::Semicolon) {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::End, "expected `end` after the let body")?;
                // `let ... in end` — idiomatic ATS for "the bindings
                // *were* the point".  The body is the unit value.
                sequence(items)
            }
        };
        let inner = if binds.is_empty() {
            inner
        } else {
            Expr::Let(binds, Box::new(inner))
        };
        Ok(wrap_funs(funs, inner))
    }

    /// `{ binds... final-expr }` — desugars to a `let` expression.

    pub(crate) fn parse_block(&mut self, _min_bp: u8) -> Result<Expr, CompileError> {
        self.advance(); // `{`
        self.parse_block_rest()
    }

    /// As `parse_let_rest`, for a brace block: the terminator is `}`
    /// and the body needs no `in`.

    pub(crate) fn parse_block_rest(&mut self) -> Result<Expr, CompileError> {
        let (binds, funs, pending) = self.parse_local_decls_and_funs()?;
        let inner = match pending {
            Some((pattern, value)) => {
                let rest = self.parse_block_rest()?;
                must_match(value, pattern, rest)
            }
            None => {
                let body = if self.at(&TokenKind::RBrace) {
                    Expr::Unit
                } else {
                    self.parse_expr(0)?
                };
                self.expect(&TokenKind::RBrace, "expected `}` after the block")?;
                body
            }
        };
        let inner = if binds.is_empty() {
            inner
        } else {
            Expr::Let(binds, Box::new(inner))
        };
        Ok(wrap_funs(funs, inner))
    }

    /// The declaration run that opens a `let` or a `{ ... }` block.
    ///
    /// Only `val` produces a binding we can lower.  The rest — proof
    /// values, local `#define`s, fixities — are static-language
    /// bookkeeping, and a local `#define` is exactly a `val`, so it is
    /// desugared into one.
    /// As `parse_local_decls`, but also returning the nested `fun`
    /// definitions the run contained.

    pub(crate) fn parse_local_decls_and_funs(
        &mut self,
    ) -> Result<(Vec<LetBind>, Vec<FunDef>, Option<(Pattern, Expr)>), CompileError> {
        let mut binds = Vec::new();
        let mut funs = Vec::new();
        loop {
            // `fun` (and the `and` clauses of a recursive group) that
            // carry a body are a *definition* and join the group.  One
            // with no body is a *declaration* — the shape a `where`
            // clause's signatures take — and a declaration has no place
            // among recursive definitions, so it is read and set aside
            // rather than forced in.
            if self.at_fun_def_keyword()
                || (matches!(&self.peek().kind, TokenKind::Ident(w) if w == "and")
                    && !funs.is_empty())
            {
                match self.parse_fun_def()? {
                    Def::Fun(f) => funs.push(f),
                    Def::Extern(_) => {}
                    // Anything else cannot come from a function
                    // definition, so it is not a shape this run can hold.
                    _ => {
                        return Err(self
                            .error_here("expected a function definition in the recursive group"));
                    }
                }
                continue;
            }
            let before = self.pos;
            let (more, pending) = self.parse_local_decl_run()?;
            binds.extend(more);
            if let Some(p) = pending {
                return Ok((binds, funs, Some(p)));
            }
            if self.pos == before {
                return Ok((binds, funs, None));
            }
        }
    }


    pub(crate) fn parse_local_decl_run(
        &mut self,
    ) -> Result<(Vec<LetBind>, Option<(Pattern, Expr)>), CompileError> {
        let mut binds = Vec::new();
        loop {
            match self.peek().kind.clone() {
                TokenKind::Val | TokenKind::Var => {
                    let mutable = self.at(&TokenKind::Var);
                    self.advance(); // `val` / `var`
                    match self.parse_val_bind(mutable)? {
                        BindKind::Simple(b) => binds.push(b),
                        // A pattern binding scopes over everything that
                        // follows it, so the run ends here and the caller
                        // wraps its remainder in the match.
                        BindKind::Pattern(p, v) => {
                            // A `;` here separates declarations, not
                            // expressions; the match scopes over
                            // everything past it either way.
                            if self.at(&TokenKind::Semicolon) {
                                self.advance();
                            }
                            return Ok((binds, Some((p, v))));
                        }
                    }
                    // `val a = e1 and b = e2` — one declaration, several
                    // bindings.  ATS binds them simultaneously; lowering
                    // them in order agrees except when a right-hand side
                    // reads a name the same declaration rebinds.
                    while matches!(&self.peek().kind, TokenKind::Ident(w) if w == "and") {
                        self.advance();
                        match self.parse_val_bind(mutable)? {
                            BindKind::Simple(b) => binds.push(b),
                            BindKind::Pattern(p, v) => return Ok((binds, Some((p, v)))),
                        }
                    }
                }
                // `#define N 10` inside a body: a name for a value, which
                // is what a `val` is.
                TokenKind::Hash => {
                    let save = self.pos;
                    let mut defs = Vec::new();
                    self.parse_hash_directive(&mut defs)?;
                    if self.pos == save {
                        return Ok((binds, None));
                    }
                    for d in defs {
                        if let Def::Const(c) = d {
                            binds.push(LetBind {
                                opened: Vec::new(),
                                proof: false,
                                name: Some(c.name),
                                ty: None,
                                value: c.value,
                                mutable: false,
                            });
                        }
                    }
                }
                // `implement f$hole<t> (...) = ...` inside a body: a
                // *template hole*, filled where the caller can see what
                // to fill it with.  The definition belongs to the
                // program, so it joins the top-level declarations.
                TokenKind::Implement => {
                    let save = self.pos;
                    match self.parse_implement_def() {
                        Ok(def) => self.pending.push(def),
                        Err(_) => {
                            self.pos = save;
                            self.skip_local_directive();
                        }
                    }
                }
                TokenKind::Ident(w) if w == "typedef" || w == "vtypedef" => {
                    if !self.parse_typedef() {
                        self.skip_local_directive();
                    }
                }
                // `local d1 in d2 end` inside a body.  The two runs
                // differ in *visibility*, and visibility is settled by
                // the time a body is being lowered — nothing after the
                // `end` can name what the private run bound, because
                // nothing after the `end` was parsed with it in scope.
                // So both runs contribute their bindings, in order.
                TokenKind::Local => {
                    self.advance();
                    let (private, pending) = self.parse_local_decl_run()?;
                    binds.extend(private);
                    if let Some(p) = pending {
                        return Ok((binds, Some(p)));
                    }
                    self.expect(&TokenKind::In, "expected `in` in the `local` block")?;
                    let (public, pending) = self.parse_local_decl_run()?;
                    binds.extend(public);
                    if let Some(p) = pending {
                        return Ok((binds, Some(p)));
                    }
                    self.expect(&TokenKind::End, "expected `end` to close the `local` block")?;
                }
                TokenKind::Ident(w) if w == "macdef" => self.parse_macdef(),
                TokenKind::Ident(w) if w == "overload" => {
                    // A local `overload` still applies to the whole
                    // program: the emitter keeps one table.
                    if let Some(def) = self.parse_overload() {
                        self.pending.push(def);
                    }
                }
                // `prval pf = ...` — a proof, which the checker must see
                // and the emitter must not.  Skipping it threw away the
                // only line establishing the claim the body then relies
                // on; emitting it would call a function never built.
                TokenKind::Ident(w) if w == "prval" || w == "prvar" => {
                    match self.parse_proof_binding() {
                        Some(bind) => binds.push(bind),
                        None => self.skip_local_directive(),
                    }
                }
                TokenKind::Ident(w) if is_skippable_directive(&w) => self.skip_local_directive(),
                _ => return Ok((binds, None)),
            }
            if self.at(&TokenKind::Semicolon) {
                self.advance();
            }
        }
    }

    /// One `val`/`var` binding: either a simple name or a pattern.
    ///
    /// A simple name lowers to a `LetBind` as always.  A pattern —
    /// `val- 55 = x`, `val cons(n, ns) = xs` — is a *match* the source
    /// insists must succeed, so it is reported to the caller, which
    /// wraps everything that follows in a `case` with no fallback.

    pub(crate) fn skip_local_directive(&mut self) {
        self.advance();
        let mut depth = 0i32;
        loop {
            match &self.peek().kind {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket => depth -= 1,
                TokenKind::RBrace if depth > 0 => depth -= 1,
                _ if depth > 0 => {}
                TokenKind::Eof | TokenKind::Val | TokenKind::Var | TokenKind::In
                | TokenKind::End | TokenKind::RBrace | TokenKind::Hash
                // A nested `fun` ends the skipped form too.  Running
                // past one swallows a whole definition, and the error
                // then surfaces deep inside it, nowhere near the
                // declaration that actually was not understood.
                | TokenKind::Fun | TokenKind::Fn | TokenKind::Implement => return,
                TokenKind::Ident(w) if is_skippable_directive(w) => return,
                _ => {}
            }
            let before = self.pos;
            self.advance();
            if self.pos == before {
                return; // parked on the final Eof
            }
        }
    }

    /// One binding, with the leading `val`/`var` keyword already eaten.
    ///
    /// The keyword is the caller's because a declaration may carry more
    /// than one binding — `val a = 1 and b = 2` — and every binding in
    /// the run shares the first keyword's mutability.
    /// `case e of | p1 => e1 | p2 => e2`.
    ///
    /// The leading `|` is optional and the arms are separated by it.  An
    /// arm's body runs to the next `|` that starts an arm, which is why
    /// the body is parsed at the loosest precedence and then stops
    /// naturally: nothing in the expression grammar consumes a bare `|`.
    /// `try e with | p1 => h1 | p2 => h2` — evaluate the body; if it
    /// raises an exception that matches a handler's pattern, run that
    /// handler's body instead.

    pub(crate) fn parse_try(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
        self.advance(); // `try`
        let body = self.parse_expr(0)?;
        self.expect(&TokenKind::With, "expected `with` after the try body")?;
        let mut handlers = Vec::new();
        loop {
            // The leading `|` of the first handler is decoration.
            if self.at(&TokenKind::Pipe) {
                self.advance();
            }
            let pattern = self.parse_pattern()?;
            self.expect(
                &TokenKind::FatArrow,
                "expected `=>` after the handler pattern",
            )?;
            let handler = self.parse_expr(0)?;
            handlers.push((pattern, handler));
            if !self.at(&TokenKind::Pipe) {
                break;
            }
        }
        Ok(Expr::Try(Box::new(body), handlers))
    }

    /// `$raise e` — raise `e` as the current exception.

    pub(crate) fn parse_raise(&mut self) -> Result<Expr, CompileError> {
        self.advance(); // `$raise`
        let value = self.parse_expr(UNARY_BP)?;
        Ok(Expr::Raise(Box::new(value)))
    }


    pub(crate) fn parse_case(&mut self) -> Result<Expr, CompileError> {
        self.advance(); // `case` (the `+`/`-` marker is part of the keyword)
        let scrutinee = self.parse_expr(0)?;
        self.expect(&TokenKind::Of, "expected `of` after the scrutinee")?;
        if self.at(&TokenKind::Pipe) {
            self.advance();
        }
        let mut raw_arms: Vec<(Pattern, Option<Expr>, Expr)> = Vec::new();
        loop {
            let pattern = self.parse_pattern()?;
            let guard = if self.at(&TokenKind::When) {
                self.advance();
                Some(self.parse_expr(0)?)
            } else {
                None
            };
            self.expect(&TokenKind::FatArrow, "expected `=>` after the pattern")?;
            let body = self.parse_expr(0)?;
            raw_arms.push((pattern, guard, body));
            if self.at(&TokenKind::Pipe) {
                self.advance();
            } else {
                break;
            }
        }
        let arms = raw_arms
            .into_iter()
            .map(|(pat, guard, body)| {
                let body = match guard {
                    Some(g) => Expr::IfThenElse(Box::new(g), Box::new(body), Box::new(Expr::Unit)),
                    None => body,
                };
                (pat, body)
            })
            .collect();
        Ok(Expr::Case(Box::new(scrutinee), arms))
    }

    /// One pattern, including any infix `::` that follows it.
    ///
    /// Cons is right-associative — `x :: y :: rest` peels one element at
    /// a time — so the tail is parsed by recursing rather than by
    /// looping.

    pub(crate) fn parse_while(&mut self) -> Result<Expr, CompileError> {
        self.advance(); // `while`
                        // `while*` introduces loop invariants for the type checker.
        self.skip_static_annotations();
        self.expect(&TokenKind::LParen, "expected `(` after `while`")?;
        let cond = self.parse_expr(0)?;
        self.expect(&TokenKind::RParen, "expected `)` after the loop condition")?;
        let body = self.parse_expr(0)?;
        Ok(Expr::While(Box::new(cond), Box::new(body)))
    }

    /// `for (init; cond; step) body` — the C-shaped loop.

    pub(crate) fn parse_for(&mut self) -> Result<Expr, CompileError> {
        self.advance(); // `for`
        self.skip_static_annotations();
        self.expect(&TokenKind::LParen, "expected `(` after `for`")?;
        let init = self.parse_expr(0)?;
        self.expect(
            &TokenKind::Semicolon,
            "expected `;` after the loop initializer",
        )?;
        let cond = self.parse_expr(0)?;
        self.expect(
            &TokenKind::Semicolon,
            "expected `;` after the loop condition",
        )?;
        let step = self.parse_expr(0)?;
        self.expect(&TokenKind::RParen, "expected `)` after the loop step")?;
        let body = self.parse_expr(0)?;
        Ok(Expr::For(
            Box::new(init),
            Box::new(cond),
            Box::new(step),
            Box::new(body),
        ))
    }

    /// `lam (x: int): int => e`, or with an arrow annotation
    /// `lam (x: int): int =<cloptr1> e`.
    ///
    /// The annotation says how the closure is allocated — heap, linear,
    /// reference-counted — which the arena settles for us, so it is read
    /// and dropped.

    pub(crate) fn parse_lam(&mut self) -> Result<Expr, CompileError> {
        self.advance(); // `lam` / `llam`
                        // `lam x => e`: a single parameter may drop its parentheses, and
                        // an annotation is optional throughout — a lambda always sits in
                        // a context that says what it is, so inference can finish the job.
        let params = if self.at(&TokenKind::LParen) {
            self.parse_params_maybe_untyped(true)?
        } else {
            let mut params = Vec::new();
            while let TokenKind::Ident(name) = self.peek().kind.clone() {
                self.advance();
                params.push(Param {
                    borrowed: false,
                    name,
                    ty: Ty::Name("_".into()),
                });
            }
            params
        };
        let ret = if self.at(&TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };
        if self.at(&TokenKind::Eq)
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|t| t.kind == TokenKind::Lt)
        {
            self.advance(); // `=`
            while !self.at(&TokenKind::Eof) && !self.at(&TokenKind::Gt) {
                self.advance();
            }
            self.advance(); // `>`
        } else {
            self.expect(
                &TokenKind::FatArrow,
                "expected `=>` after the lambda parameters",
            )?;
        }
        let body = self.parse_expr(0)?;
        Ok(Expr::Lam(params, ret, Box::new(body)))
    }

    // --- operator table ---------------------------------------------

    /// The binary operator at the cursor, with its (left, right) binding
    /// powers.  All operators are left-associative (`rbp = lbp + 1`).

    pub(crate) fn current_binop(&self) -> Option<(BinOp, u8, u8)> {
        let (op, lbp) = match self.peek().kind {
            TokenKind::Orelse => (BinOp::Orelse, 1),
            TokenKind::Andalso => (BinOp::Andalso, 3),
            TokenKind::Eq => (BinOp::Eq, 5),
            TokenKind::Ne => (BinOp::Ne, 5),
            TokenKind::Lt => (BinOp::Lt, 5),
            TokenKind::Le => (BinOp::Le, 5),
            TokenKind::Gt => (BinOp::Gt, 5),
            TokenKind::Ge => (BinOp::Ge, 5),
            TokenKind::Plus => (BinOp::Add, 7),
            TokenKind::Minus => (BinOp::Sub, 7),
            TokenKind::Star => (BinOp::Mul, 9),
            TokenKind::Slash => (BinOp::Div, 9),
            TokenKind::Mod => (BinOp::Mod, 9),
            // `%` is ATS's modulo, as in `x % 3`; the same token opens an
            // inline-C block only when followed by `{`.
            TokenKind::Percent => (BinOp::Mod, 9),
            _ => return None,
        };
        Some((op, lbp, lbp + 1))
    }
}

/// Fold a run of expressions evaluated in order into one expression.
///
/// All but the last are run for their effect, which is exactly a discard
/// binding, so a sequence needs no AST node of its own.  An empty run is
/// unit — `begin end` and `()` say the same thing.
pub(crate) fn sequence(items: Vec<Expr>) -> Expr {
    let mut it = items.into_iter().rev();
    let Some(mut expr) = it.next() else {
        return Expr::Unit;
    };
    for earlier in it {
        expr = Expr::Let(
            vec![LetBind {
                opened: Vec::new(),
                proof: false,
                name: None,
                ty: None,
                value: earlier,
                mutable: false,
            }],
            Box::new(expr),
        );
    }
    expr
}


pub(crate) const UNARY_BP: u8 = 10;
