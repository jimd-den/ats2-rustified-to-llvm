use super::context::*;
use super::decode::*;
use super::expr::*;
use super::patterns::*;
use super::types::*;
use ats2_domain::ast::*;
use ats2_domain::errors::CompileError;
use ats2_domain::statics::*;
use ats2_domain::tokens::*;
use std::collections::{HashMap, HashSet};

fn lower_top_pattern(pat: Pattern, target: Expr, out: &mut Vec<Def>, gensym: &mut usize) {
    match pat {
        Pattern::Var(name) => {
            out.push(Def::Val(ValDef {
                name,
                ty: None,
                value: target,
            }));
        }
        Pattern::Tuple(items) => {
            for (idx, item) in items.into_iter().enumerate() {
                let sub = Expr::Field(Box::new(target.clone()), format!("{idx}"));
                lower_top_pattern(item, sub, out, gensym);
            }
        }
        Pattern::Wildcard | Pattern::Int(_) | Pattern::Char(_) | Pattern::Bool(_) | Pattern::Str(_) => {}
        _ => {
            *gensym += 1;
            let stmt_name = format!("{TOPLEVEL_STATEMENT}{}", gensym);
            let exit = Expr::Call(Box::new(Expr::Var("exit".into())), vec![Expr::IntLit(1)]);
            let case_expr = Expr::Case(
                Box::new(target),
                vec![(pat, Expr::Unit), (Pattern::Wildcard, exit)],
            );
            out.push(Def::Val(ValDef {
                name: stmt_name,
                ty: None,
                value: case_expr,
            }));
        }
    }
}

impl<'a> ParseCtx<'a> {
    pub(crate) fn parse_program(&mut self) -> Result<Program, Vec<CompileError>> {
        self.precollect_type_aliases();
        let mut defs = Vec::new();
        while !self.at(&TokenKind::Eof) {
            self.parse_toplevel(&mut defs).map_err(|e| vec![e])?;
        }
        Ok(self.finish_program(defs))
    }


    pub(crate) fn parse_available_program(&mut self) -> Program {
        self.precollect_type_aliases();
        let mut defs = Vec::new();
        while !self.at(&TokenKind::Eof) {
            let start = self.pos;
            if self.parse_toplevel(&mut defs).is_err() {
                self.recover_after_toplevel_error(start);
            }
        }
        self.finish_program(defs)
    }

    /// Resume dependency parsing at the next source-level line.
    ///
    /// A failed top-level reader may have consumed tokens from the following
    /// declaration while trying to complete the unsupported one. Recovery
    /// therefore starts from the declaration's original position, not from
    /// the parser's current cursor. Root parsing never calls this: a source
    /// being compiled remains strict, while dependencies expose every usable
    /// declaration they contain.

    pub(crate) fn recover_after_toplevel_error(&mut self, failed_at: usize) {
        let failed_line = self.tokens[failed_at].span.start.line;
        self.pos = (failed_at + 1..self.tokens.len())
            .find(|&i| {
                let start = self.tokens[i].span.start;
                start.line > failed_line && start.column == 1
            })
            .unwrap_or(self.tokens.len() - 1);
    }


    pub(crate) fn finish_program(&mut self, mut defs: Vec<Def>) -> Program {
        // Declarations found inside bodies join the program's own.
        defs.extend(std::mem::take(&mut self.pending));
        Program::new(defs)
            .asking_for(std::mem::take(&mut self.staloads))
            .including(std::mem::take(&mut self.includes))
    }

    /// Find every type alias in the file before parsing any of it.
    ///
    /// `abstype set (a) = ptr` hides a type and `assume set (a) = ...`
    /// says what it really is — and the assumption may sit far below the
    /// uses it decides.  In `ordset.dats` it is inside a `local` near
    /// the end of the file, while the record type that mentions `set`
    /// is near the top.  A single left-to-right pass cannot see it in
    /// time, so the aliases are gathered first, and the assumption wins
    /// over the declaration by arriving later in the same sweep.
    ///
    /// Nothing else is read here: any position that does not parse as an
    /// alias is stepped over and left for the real parse.

    pub(crate) fn precollect_type_aliases(&mut self) {
        let save = self.pos;
        self.pos = 0;
        while !self.at(&TokenKind::Eof) {
            let opens_an_alias = matches!(
                &self.tokens[self.pos].kind,
                TokenKind::Ident(w)
                    // Only the *abstract* forms are gathered early.  A
                    // plain `typedef` means what it means from where it
                    // is written, and a local one inside a template
                    // mentions that template's type variables — hoisting
                    // it would take those out of the only scope that
                    // gives them a meaning.
                    if matches!(w.as_str(), "abstype" | "absvtype" | "abst0ype" | "abstbox" | "abstflat" | "abstract" | "assume")
            ) || self.at_at_joined_abstract();
            let before = self.pos;
            if opens_an_alias {
                // The `abst @ ype` form arrives with its keyword cut
                // into three tokens, and is read by the reader that
                // rejoins them; the single-word forms share the ordinary
                // `typedef` reader.
                let ok = if self.at_at_joined_abstract() {
                    self.parse_at_joined_abstract()
                } else {
                    self.parse_typedef()
                };
                if !ok {
                    // `abstype point` with no `= t` — an *opaque*
                    // abstract type.  Its representation is hidden, so it
                    // is registered as the unnamed boxed type, which the
                    // emitter lowers to a pointer.
                    if !self.parse_abstract_opaque() {
                        self.advance();
                    }
                }
            } else {
                self.advance();
            }
            if self.pos == before {
                break;
            }
        }
        self.pos = save;
    }

    /// One top-level form.  Unlike `parse_def` this appends *zero or more*
    /// definitions, because ATS has forms that carry no runtime content
    /// (`staload`, `#include`, `typedef`) and forms that carry several
    /// (`local ... in ... end`).

    pub(crate) fn parse_toplevel(&mut self, out: &mut Vec<Def>) -> Result<(), CompileError> {
        match self.peek().kind.clone() {
            TokenKind::Semicolon => {
                self.advance();
                Ok(())
            }
            // `#include`, `#define`, `#print`, ...
            TokenKind::Hash => self.parse_hash_directive(out),
            TokenKind::Local => self.parse_local(out),
            // `val name = expr` outside any body: a value the whole
            // program shares.
            // `typedef T = t`.  One this parser cannot model falls
            // through to the directive skipper, which is where every
            // other static-language declaration goes.
            // `vtypedef` names a *linear* type.  Linearity is a
            // question for a type checker, and the naming works exactly
            // as `typedef`'s does, so the two share a path.
            TokenKind::Ident(w) if w == "where" => self.parse_where_type_alias(),
            TokenKind::Ident(w) if w == "prval" || w == "prvar" || w.starts_with("val-") || w.starts_with("val+") || w.starts_with("prval-") || w.starts_with("prval+") => {
                self.advance();
                if let Ok(bind) = self.parse_val_bind(false) {
                    match bind {
                        BindKind::Simple(bind) => {
                            let name = bind.name.unwrap_or_else(|| {
                                self.gensym += 1;
                                format!("{TOPLEVEL_STATEMENT}{}", self.gensym)
                            });
                            out.push(Def::Val(ValDef {
                                name,
                                ty: bind.ty,
                                value: bind.value,
                            }));
                        }
                        BindKind::Pattern(pat, expr) => {
                            self.gensym += 1;
                            let tmp_name = format!("__ats2_tmp_{}", self.gensym);
                            out.push(Def::Val(ValDef {
                                name: tmp_name.clone(),
                                ty: None,
                                value: expr,
                            }));
                            lower_top_pattern(pat, Expr::Var(tmp_name), out, &mut self.gensym);
                        }
                    }
                } else {
                    self.skip_directive();
                }
                Ok(())
            }
            TokenKind::Ident(w) if w == "extvar" || w == "extcode" || w == "sif" => {
                self.skip_directive();
                Ok(())
            }
            TokenKind::Ident(w) if w == "typedef" || w == "vtypedef" => {
                if !self.parse_typedef() {
                    self.skip_directive();
                }
                Ok(())
            }
            // `datavtype` — a datatype whose values are linear: each
            // must be consumed exactly once.  The views that make them
            // so are erased before emission, so it parses exactly as
            // `datatype` does — but *that* it is one is recorded, since
            // nothing about the bits says so and the declaration is the
            TokenKind::Ident(w) if w == "datavtype" => {
                self.advance(); // `datavtype`
                out.push(self.parse_datatype_body(true)?);
                Ok(())
            }
            TokenKind::Val => {
                self.advance(); // `val`
                let rec_form = matches!(&self.peek().kind, TokenKind::Ident(w) if w == "rec");
                if rec_form {
                    self.advance(); // `rec`
                }
                loop {
                    match self.parse_val_bind(false)? {
                        BindKind::Simple(bind) => {
                            let name = bind.name.unwrap_or_else(|| {
                                self.gensym += 1;
                                format!("{TOPLEVEL_STATEMENT}{}", self.gensym)
                            });
                            out.push(Def::Val(ValDef {
                                name,
                                ty: bind.ty,
                                value: bind.value,
                            }));
                        }
                        BindKind::Pattern(pat, expr) => {
                            self.gensym += 1;
                            let tmp_name = format!("__ats2_tmp_{}", self.gensym);
                            out.push(Def::Val(ValDef {
                                name: tmp_name.clone(),
                                ty: None,
                                value: expr,
                            }));
                            lower_top_pattern(pat, Expr::Var(tmp_name), out, &mut self.gensym);
                        }
                    }
                    if rec_form && matches!(&self.peek().kind, TokenKind::Ident(w) if w == "and") {
                        self.advance();
                    } else {
                        break;
                    }
                }
                Ok(())
            }
            TokenKind::Var => {
                self.advance(); // `var`
                let BindKind::Simple(bind) = self.parse_val_bind(true)? else {
                    return Err(
                        self.error_here("a pattern binding is not supported at the top level")
                    );
                };
                if let Some(name) = bind.name {
                    let value = Expr::Call(Box::new(Expr::Var("ref".into())), vec![bind.value]);
                    let ty = bind.ty.map(|t| Ty::App("ref".into(), vec![t]));
                    out.push(Def::Val(ValDef { name, ty, value }));
                }
                Ok(())
            }
            // subset does not model, so a declaration that does not parse
            // goes back to being skipped rather than becoming an error.
            // `static fun f (...): t = "sta#f"` declares a function the
            // rest of the file implements — the same job `extern fun`
            // does, with a different word for a distinction (which
            // compilation unit owns the symbol) that does not survive to
            // a single-module compiler.
            // `praxi f {n:pos} (): [P] void` — an axiom.  Its *result
            // type* is the claim it establishes, so a proof language
            // that skipped it would skip the only statement in the file
            // that said anything.  `prfun` is the same shape with a
            // proof term behind it rather than a fiat.
            // `dataprop FACT (int,int) = | {n:pos}{r:int} FACTind (n, n*r)
            // of FACT(n-1, r)` — an inductive proposition.  Each
            // constructor is a function from the proofs it consumes to a
            // proof of its own indices, which is all a constructor of a
            // proposition is; saying it that way needs no machinery a
            // function does not already have, and makes every proof term
            // an ordinary call the checker already knows how to read.
            TokenKind::Ident(name) if name == "dataprop" || name == "dataview" => {
                let save = self.pos;
                match self.parse_dataprop(name == "dataview") {
                    Some(decls) => out.extend(decls.into_iter().map(Def::Extern)),
                    None => {
                        self.pos = save;
                        self.skip_directive();
                    }
                }
                Ok(())
            }
            TokenKind::Ident(name) if name == "praxi" || name == "prfun" || name == "prfn" => {
                let save = self.pos;
                if let Ok(decl) = self.parse_extern_decl() {
                    out.push(Def::Extern(decl));
                    return Ok(());
                }
                // A `prfun` with a derivation behind it is not a
                // declaration that failed to parse — it is a definition,
                // and the `=` the declaration form choked on is the one
                // that introduces the proof term.  Reading it as a
                // definition is what keeps the difference between a
                // proof and an axiom: the checker gets a body to hold
                // against the proposition, rather than a promise.
                self.pos = save;
                if let Ok(def) = self.parse_fun_def() {
                    out.push(def);
                    return Ok(());
                }
                self.pos = save;
                self.skip_directive();
                Ok(())
            }
            // `castfn f {l:addr} (x: ptr l): ptr l` is a function
            // declaration whose implementation is trusted to change or
            // preserve a representation. The trust affects its body, not
            // its dependent signature: callers still need the parameter and
            // result indices, so it follows the ordinary declaration path.
            TokenKind::Ident(name) if name == "castfn" => {
                let save = self.pos;
                if let Ok(decl) = self.parse_extern_decl() {
                    out.push(Def::Extern(decl));
                } else {
                    self.pos = save;
                    self.skip_directive();
                }
                Ok(())
            }
            TokenKind::Ident(name) if name == "extern" || name == "static" => {
                let save = self.pos;
                self.advance();
                if self.at_proof_keyword()
                    || matches!(self.peek().kind, TokenKind::Fun | TokenKind::Fn)
                {
                    if let Ok(decl) = self.parse_extern_decl() {
                        out.push(Def::Extern(decl));
                        return Ok(());
                    }
                }
                if self.at(&TokenKind::Val) {
                    if let Ok(decl) = self.parse_extern_val_decl() {
                        out.push(Def::Extern(decl));
                        return Ok(());
                    }
                }
                // The declaration did not parse, so it goes back to being
                // ignored.  Skipping must step over the `fun` it owns,
                // or the scan would stop on it and try to read the
                // declaration as a definition.
                self.pos = save;
                self.advance(); // `extern`
                if self.at_proof_keyword()
                    || matches!(self.peek().kind, TokenKind::Fun | TokenKind::Fn)
                {
                    self.advance();
                }
                self.skip_directive();
                Ok(())
            }
            // `%{ ... %}` — C the program brought with it.  Nothing here
            // reads it; it is carried through to the toolchain, which
            // speaks C.
            TokenKind::InlineC(text) => {
                let text = text.clone();
                self.advance();
                out.push(Def::InlineC(text));
                Ok(())
            }
            TokenKind::Ident(name) if name == "macdef" => {
                self.parse_macdef();
                Ok(())
            }
            TokenKind::Ident(name) if name == "overload" => {
                if let Some(def) = self.parse_overload() {
                    out.push(def);
                }
                Ok(())
            }
            // `staload` and `dynload` are still skipped as text — but
            // what they *named* is written down first.  Every other
            // directive on that list speaks to a part of ATS this
            // compiler does not implement; these two speak to where the
            // rest of the program is, which is a question it can answer.
            TokenKind::RBrace => {
                self.advance();
                Ok(())
            }
            TokenKind::Ident(name) if name == "staload" || name == "dynload" => {
                let mut at = self.pos + 1;
                let mut alias = None;
                if let Some(TokenKind::Ident(a)) = self.tokens.get(at).map(|t| &t.kind) {
                    if a != "_" {
                        alias = Some(a.clone());
                    }
                    at += 1;
                    if matches!(self.tokens.get(at).map(|t| &t.kind), Some(TokenKind::Eq)) {
                        at += 1;
                    }
                }
                if matches!(self.tokens.get(at).map(|t| &t.kind), Some(TokenKind::LBrace)) {
                    self.pos = at + 1;
                    while !self.at(&TokenKind::RBrace) && !self.at(&TokenKind::Eof) {
                        self.parse_toplevel(out)?;
                    }
                    if self.at(&TokenKind::RBrace) {
                        self.advance();
                    }
                    return Ok(());
                }
                if let Some(s) = self.read_staload(name == "dynload") {
                    self.staloads.push(s);
                }
                self.skip_directive();
                Ok(())
            }
            // know the constructors, so they are kept.
            TokenKind::Ident(w) if w == "exception" => {
                out.extend(self.parse_exception());
                Ok(())
            }
            TokenKind::Ident(name) if is_skippable_directive(&name) => {
                self.skip_directive();
                Ok(())
            }
            // `fun f ... and g ...` — a mutually recursive group.  Each
            // clause is an ordinary function; the keyword only tells the
            // type checker to consider them together.
            // `fun f ... and g ...` — a mutually recursive group.  The
            // keyword only tells the type checker to consider the clauses
            // together, so each one is parsed as an ordinary function.
            // `parse_fun_def` consumes the leading keyword itself, which
            // is `and` here rather than `fun`.
            TokenKind::Ident(name) if name == "and" => {
                out.push(self.parse_fun_def()?);
                Ok(())
            }
            // `abst @ ype` — the abstract linear type form, cut at the
            // `@` by the lexer.  It is a declaration of a type name; the
            // name was already gathered by the pre-pass, so the
            // declaration itself is skipped like the other abstract
            // forms, not mistaken for a definition.
            TokenKind::Ident(_) if self.at_at_joined_abstract() => {
                self.skip_directive();
                Ok(())
            }
            // `datatype a = ... and b = ...` — a group of datatypes that
            // may refer to one another.  Each clause is a datatype; the
            // `and` is the mutual-recursion link, not a function's.
            TokenKind::Datatype => {
                // The first clause carries the `datatype` keyword; each
                // later clause is just `and name (...) = ...`, with no
                // repeated keyword.
                out.push(self.parse_datatype_def()?);
                while self.at_ident("and") {
                    self.advance(); // `and`
                    out.push(self.parse_datatype_body(false)?);
                }
                Ok(())
            }
            _ => {
                out.push(self.parse_def()?);
                Ok(())
            }
        }
    }

    /// `local <defs> in <defs> end` — a scope.  Since the subset has no
    /// notion of visibility, both halves simply contribute their defs.

    pub(crate) fn parse_local(&mut self, out: &mut Vec<Def>) -> Result<(), CompileError> {
        self.advance(); // `local`
        while !self.at(&TokenKind::In) && !self.at(&TokenKind::Eof) {
            self.parse_toplevel(out)?;
        }
        self.expect(&TokenKind::In, "expected `in` in the `local` block")?;
        while !self.at(&TokenKind::End) && !self.at(&TokenKind::Eof) {
            self.parse_toplevel(out)?;
        }
        self.expect(&TokenKind::End, "expected `end` to close the `local` block")?;
        Ok(())
    }

    /// A `#`-directive.  `#define NAME value` becomes a constant; the
    /// rest (`#include`, `#print`, `#assert`, ...) direct the *ATS*
    /// compiler's own machinery and have nothing to say to this one.

    pub(crate) fn parse_hash_directive(&mut self, out: &mut Vec<Def>) -> Result<(), CompileError> {
        self.advance(); // `#`
        let directive_line = self.peek().span.start.line;
        let word = match self.peek().kind.clone() {
            TokenKind::Ident(w) => w,
            _ => {
                self.skip_directive();
                return Ok(());
            }
        };
        self.advance();
        // These conditional-compilation controls have no arguments.
        // Sending `#endif` through the generic directive skipper consumes the
        // first token after it; when that token is `fun`, the parser silently
        // loses the declaration. The opening controls are deliberately not
        // handled here: ATS permits their condition on the following line.
        if matches!(word.as_str(), "else" | "endif") {
            while !self.at(&TokenKind::Eof) && self.peek().span.start.line == directive_line {
                self.advance();
            }
            return Ok(());
        }
        // `#staload` / `#dynload` — the pseudocode spellings of the two
        // directives that name another unit.  What they name is a
        // dependency every bit as much as the unpragmatic form's is, so
        // it is written down here; the rest of the line is still skipped.
        if word == "staload" || word == "dynload" {
            if let Some(s) = self.read_staload_after_keyword(word == "dynload") {
                self.staloads.push(s);
            }
            self.skip_directive();
            return Ok(());
        }
        if word == "include" {
            if let TokenKind::StrLit(path) = self.peek().kind.clone() {
                self.includes.push(Include { path });
                self.advance();
            } else {
                self.skip_directive();
            }
            return Ok(());
        }
        if word != "define" {
            self.skip_directive();
            return Ok(());
        }
        // `#define :: stream_vt_cons` — the operator is being pointed at
        // a different constructor.  It names no value, so it produces no
        // definition; it retunes the parser instead.
        if self.at(&TokenKind::ColonColon) {
            self.advance();
            if let TokenKind::Ident(ctor) = self.peek().kind.clone() {
                self.cons_name = ctor;
                self.advance();
            } else {
                self.skip_directive();
            }
            return Ok(());
        }
        let Some(name) = (match self.peek().kind.clone() {
            TokenKind::Ident(n) => Some(n),
            _ => None,
        }) else {
            self.skip_directive();
            return Ok(());
        };
        self.advance();
        // `#define list0_pair(x1, x2) body` — a *parameterised* macro.
        // Its parameters and body are read at each use, which this
        // compiler does not expand; the whole macro is skipped as one
        // unit so it stops cleanly rather than leaking its body as
        // declarations.
        if self.at(&TokenKind::LParen) {
            self.skip_directive();
            return Ok(());
        }
        // `#define cons stream_vt_cons` — one *name* for another.  It is
        // not a constant: the name has to mean the constructor in
        // patterns as well as in expressions, and a constant reaches
        // only the expression side.
        if let TokenKind::Ident(target) = self.peek().kind.clone() {
            if self.directive_ends_after_one_token() {
                self.advance();
                let target = self.renames.get(&target).cloned().unwrap_or(target);
                self.renames.insert(name, target);
                return Ok(());
            }
        }
        // A `#define` with a value we can express becomes a constant; one
        // with a value we cannot (a C fragment, a type) is dropped rather
        // than made into a parse error, because it may never be used.
        let save = self.pos;
        match self.parse_expr(0) {
            Ok(value) => out.push(Def::Const(ConstDef { name, value })),
            Err(_) => {
                self.pos = save;
                self.skip_directive();
            }
        }
        Ok(())
    }

    /// Read what a `staload` names, without consuming any of it.
    ///
    /// The four spellings differ only in what sits between the keyword
    /// and the path — nothing, `H =`, or `_ =` — so this looks past
    /// exactly that and takes the string.  `(*anon*)`, which the corpus
    /// writes after the `_`, is a comment and is gone by now.
    ///
    /// `None` when there is no string to find.  That is not an error:
    /// `staload` has spellings this compiler has never met, and the
    /// established answer to one of those is to skip the line, not to
    /// refuse the file.

    pub(crate) fn read_staload(&self, dynamic: bool) -> Option<Staload> {
        let mut at = self.pos + 1;
        let mut alias = None;
        let mut anonymous = false;
        // `H =` or `_ =`, if either is there.
        if matches!(self.nth(at + 1), Some(TokenKind::Eq)) {
            alias = match self.nth(at) {
                Some(TokenKind::Ident(name)) => Some(name.clone()),
                // `_` names nothing, which is the whole point of it.
                Some(TokenKind::Underscore) => {
                    anonymous = true;
                    None
                }
                _ => return None,
            };
            at += 2;
        }
        match self.nth(at) {
            Some(TokenKind::StrLit(path)) => Some(Staload {
                path: path.clone(),
                alias,
                kind: load_kind(path, dynamic, anonymous),
            }),
            _ => None,
        }
    }

    /// Read a `staload` that follows a `#staload`/`#dynload` keyword, with
    /// the cursor already past that keyword (the `#` consumed it the way
    /// any hash directive is read).  Identical in shape to `read_staload`,
    /// which sits on the keyword itself; the only difference is the
    /// offset of the first token that can begin the path or alias.
    ///
    /// `#staload H = "path"` / `#staload "path"` / `#dynload "path"`.

    pub(crate) fn read_staload_after_keyword(&self, dynamic: bool) -> Option<Staload> {
        let mut at = self.pos;
        let mut alias = None;
        let mut anonymous = false;
        if matches!(self.nth(at + 1), Some(TokenKind::Eq)) {
            alias = match self.nth(at) {
                Some(TokenKind::Ident(name)) => Some(name.clone()),
                Some(TokenKind::Underscore) => {
                    anonymous = true;
                    None
                }
                _ => return None,
            };
            at += 2;
        }
        match self.nth(at) {
            Some(TokenKind::StrLit(path)) => Some(Staload {
                path: path.clone(),
                alias,
                kind: load_kind(path, dynamic, anonymous),
            }),
            _ => None,
        }
    }

    /// The kind of the token `n` places along, if the file is that long.

    pub(crate) fn parse_def(&mut self) -> Result<Def, CompileError> {
        if self.at_fun_def_keyword() {
            return self.parse_fun_def();
        }
        match self.peek().kind {
            TokenKind::Datatype => self.parse_datatype_def(),
            TokenKind::Implement => self.parse_implement_def(),
            _ => Err(self.error_here("expected a definition")),
        }
    }

    // --- definitions -----------------------------------------------


    pub(crate) fn parse_datatype_def(&mut self) -> Result<Def, CompileError> {
        self.advance(); // `datatype`
        self.parse_datatype_body(false)
    }

    /// Everything after the `datatype`/`datavtype` keyword.  The type
    /// parameters stay in scope while the constructors are read, so a
    /// field written `bintree a` applies the datatype to `a`.

    pub(crate) fn parse_datatype_body(&mut self, linear: bool) -> Result<Def, CompileError> {
        let name = self.expect_ident("expected a datatype name")?;
        self.datatypes.insert(name.clone());
        let (ty_params, type_arity) = self.parse_optional_type_params()?;
        let scope = self.push_type_vars(&ty_params);
        let def = (|| {
            self.expect(&TokenKind::Eq, "expected `=` after the datatype name")?;
            // The bar before the first constructor is decoration.
            if self.at(&TokenKind::Pipe) {
                self.advance();
            }
            let mut ctors = vec![self.parse_ctor(&name, type_arity)?];
            while self.at(&TokenKind::Pipe) {
                self.advance();
                ctors.push(self.parse_ctor(&name, type_arity)?);
            }
            Ok(Def::Datatype(DatatypeDef {
                name,
                ty_params,
                ctors,
                linear,
            }))
        })();
        self.pop_type_vars(scope);
        def
    }

    /// Bring `names` into scope as type variables, returning the depth
    /// to restore afterwards.

    pub(crate) fn parse_optional_type_params(&mut self) -> Result<(Vec<String>, usize), CompileError> {
        if !self.at(&TokenKind::LParen) {
            return Ok((vec![], 0));
        }
        self.advance();
        let mut params = Vec::new();
        let mut type_arity = 0;
        loop {
            let name = self.expect_ident("expected a datatype parameter")?;
            if self.at(&TokenKind::Colon) {
                self.advance();
                let sort = self
                    .parse_sort_name()
                    .map(|name| Sort::from_name(&name))
                    .unwrap_or_else(|| Sort::Named("_".into()));
                if sort == Sort::Type {
                    params.push(name);
                    type_arity += 1;
                }
                while !self.at(&TokenKind::Comma)
                    && !self.at(&TokenKind::RParen)
                    && !self.at(&TokenKind::Eof)
                {
                    self.advance();
                }
            } else {
                // `datatype list(a:t@ype, int)` — a bare known sort is an
                // unnamed static parameter position. A bare unknown name is
                // the traditional shorthand for a type parameter.
                match Sort::from_name(&name) {
                    Sort::Int | Sort::Nat | Sort::Pos | Sort::Bool | Sort::Addr => {}
                    _ => {
                        params.push(name);
                        type_arity += 1;
                    }
                }
            }
            if self.at(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&TokenKind::RParen, "expected `)` after the type parameters")?;
        Ok((params, type_arity))
    }

    /// One constructor of a datatype.
    ///
    /// ATS writes the fields after `of`: `Cons of (int, list)`, or
    /// `Some of int` when there is exactly one, or `Nil of ()` when there
    /// are none.  The `of`-less spelling `Cons(int, list)` is accepted as
    /// well, since the subset used it before and both read clearly.

    pub(crate) fn parse_ctor(
        &mut self,
        datatype: &str,
        type_arity: usize,
    ) -> Result<Ctor, CompileError> {
        // `| {n:nat} btnode (a, n) of (int(n), a)` — an indexed
        // constructor declares its index variables in braces before its
        // name. It survives because its guard and its result indices are
        // what a pattern match contributes to dependent checking.
        let universals = self.parse_quantifiers();
        let name = self.expect_ident("expected a constructor name")?;
        self.skip_static_annotations();
        // `C (i1, i2) of (fields)` — the parens before `of` are the
        // constructor's *static indices*, not its value fields.  They are
        // read ahead of `of`, and when `of` follows, they are dropped and
        // only the fields are kept.
        if self.at(&TokenKind::LParen) {
            let save = self.pos;
            let result = self.parse_ctor_result(datatype, type_arity)?;
            if self.at(&TokenKind::Of) {
                self.advance();
                return self.parse_ctor_fields(name, universals, Some(result));
            }
            self.pos = save;
        }
        if self.at(&TokenKind::Of) {
            self.advance();
        }
        self.parse_ctor_fields(name, universals, None)
    }

    /// The datatype instance between a constructor's name and `of`.
    ///
    /// In `list_cons(a, n+1)`, the first argument is a runtime type
    /// parameter and the second is a static result index. The enclosing
    /// datatype declaration says where that boundary lies.

    pub(crate) fn parse_ctor_result(
        &mut self,
        datatype: &str,
        type_arity: usize,
    ) -> Result<Ty, CompileError> {
        self.expect(&TokenKind::LParen, "expected `(` before constructor indices")?;
        let mut position = 0;
        let mut type_args = Vec::new();
        let mut indices = Vec::new();
        while !self.at(&TokenKind::RParen) && !self.at(&TokenKind::Eof) {
            if position < type_arity {
                if let Some(ty) = self.parse_type_argument()? {
                    type_args.push(ty);
                }
            } else {
                let term = self
                    .parse_expr(0)
                    .ok()
                    .as_ref()
                    .and_then(sexp_of_expr)
                    .ok_or_else(|| self.error_here("expected a constructor result index"))?;
                indices.push(term);
            }
            position += 1;
            if self.at(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(
            &TokenKind::RParen,
            "expected `)` after the constructor result",
        )?;
        let base = if type_args.is_empty() {
            Ty::Name(datatype.into())
        } else {
            Ty::App(datatype.into(), type_args)
        };
        Ok(if indices.is_empty() {
            base
        } else {
            Ty::Index(Box::new(base), indices)
        })
    }

    /// The value fields of a constructor, whether written `C of (a, b)`,
    /// `C of a`, the of-less `C(a, b)`, or `C of ()`.

    pub(crate) fn parse_ctor_fields(
        &mut self,
        name: String,
        universals: Vec<Quant>,
        result: Option<Ty>,
    ) -> Result<Ctor, CompileError> {
        let fields = if self.at(&TokenKind::LParen) {
            self.advance();
            // `of ()` — no fields at all.
            if self.at(&TokenKind::RParen) {
                self.advance();
                return Ok(Ctor {
                    name,
                    universals,
                    result,
                    fields: vec![],
                });
            }
            let mut fields = vec![self.parse_type()?];
            while self.at(&TokenKind::Comma) {
                self.advance();
                fields.push(self.parse_type()?);
            }
            self.expect(
                &TokenKind::RParen,
                "expected `)` after the constructor fields",
            )?;
            fields
        } else if self.starts_a_type() {
            // `Some of int` — a single field needs no parentheses.
            vec![self.parse_type()?]
        } else {
            vec![]
        };
        Ok(Ctor {
            name,
            universals,
            result,
            fields,
        })
    }

    /// Whether a type could begin at the cursor.
    ///
    /// Used where a type is optional: after `of`, the next token is either
    /// the field's type or the `|` that starts the next constructor.

    pub(crate) fn parse_fun_def(&mut self) -> Result<Def, CompileError> {
        // `prfun f (): P = <derivation>` is a `fun` in every respect the
        // parser cares about; what differs is who reads the result.
        let proof = self.at_proof_keyword();
        self.advance(); // `fun` / `fn` / `praxi` / `prfun`
                        // `fun{a:t@ype} f (...)` — the template parameters precede the
                        // name.  They are the *sorts* a template abstracts over, so
                        // unlike the other static annotations they are kept.
        let mut ty_params = self.parse_template_params();
        let name = self.expect_ident("expected a function name")?;
        // `{n:nat}` / `{a:t@ype}` — the dependent half of the signature,
        // and `.<n>.` — the half that says it terminates.
        let (universals, metric) = self.parse_quantifiers_and_metric();
        for (name, _) in universals
            .iter()
            .flat_map(|quantifier| &quantifier.vars)
            .filter(|(_, sort)| *sort == Sort::Type)
        {
            if !ty_params.contains(name) {
                ty_params.push(name.clone());
            }
        }
        // The template's parameters are in scope for its own signature
        // and body, so `bintree a` in either place applies `bintree`.
        let scope = self.push_type_vars(&ty_params);
        // `fun abs_int0 : int -<fun> int = "mac#%"` — the colon form,
        // common in `.sats` headers.  The whole signature is one curried
        // type written after the name; there is no parameter list to
        // flatten, so it is always a declaration.
        if self.at(&TokenKind::Colon) {
            self.advance();
            self.skip_effect_annotation();
            let existentials = self.parse_existentials();
            let whole = self.parse_type()?;
            self.skip_static_annotations();
            let (sig_params, ret) = Self::split_curried(whole);
            // `fun f : T = lam (x, y) => b` — a *definition* written in
            // the colon form: it carries a body, and when that body is a
            // lambda the lambda's parameters are the function's.  A
            // `= "mac#..."` binding is a declaration instead.
            if self.at(&TokenKind::Eq) && !self.is_string_binding() {
                self.advance(); // `=`
                let body = self.parse_expr(0)?;
                let (params, body) = match body {
                    Expr::Lam(ps, _ty, inner) => (ps, *inner),
                    other => (sig_params, other),
                };
                self.pop_type_vars(scope);
                return Ok(Def::Fun(FunDef {
                    ty_params,
                    universals,
                    existentials,
                    metric,
                    name,
                    params,
                    ret,
                    body,
                    proof,
                }));
            }
            let decl = self.finish_fun_decl(
                proof,
                ty_params,
                universals,
                existentials,
                name,
                sig_params,
                ret,
            )?;
            self.pop_type_vars(scope);
            return Ok(Def::Extern(decl));
        }
        let (params, ambiguous_bare_types) = self.parse_params_with_unknown_bare_types()?;
        // A missing return type is written as `_`: some functions leave it
        // out when the body says what it is, as `fun f (m: int) = lam ...`
        // does.
        let mut existentials = Vec::new();
        let ret = if self.at(&TokenKind::Colon) {
            self.advance();
            self.skip_effect_annotation();
            // `: [r:int] t` — what the caller may assume about the result.
            existentials = self.parse_existentials();
            let ty = self.parse_type()?;
            self.skip_static_annotations();
            ty
        } else if self.at(&TokenKind::Eq) {
            Ty::Name("_".into())
        } else {
            return Err(self.error_here("expected `:` and a return type after the parameters"));
        };
        // A `.sats` signature ends with no `=`, or with `= "mac#..."` /
        // `= "sta#..."` / `= "ext#..."` — an *external binding* naming
        // where the implementation lives, not a body.  Both are
        // declarations; the body lives in a `.dats` somewhere else.
        if !self.at(&TokenKind::Eq) || self.at_external_binding() {
            let decl = self.finish_fun_decl(
                proof,
                ty_params,
                universals,
                existentials,
                name,
                params,
                ret,
            )?;
            self.pop_type_vars(scope);
            return Ok(Def::Extern(decl));
        }
        if let Some(name) = ambiguous_bare_types.first() {
            return Err(self.error_here(format!("parameter `{name}` needs a type annotation")));
        }
        self.expect(&TokenKind::Eq, "expected `=` before the function body")?;
        let body = self.parse_expr(0)?;
        self.pop_type_vars(scope);
        Ok(Def::Fun(FunDef {
            ty_params,
            universals,
            existentials,
            metric,
            name,
            params,
            ret,
            body,
            proof,
        }))
    }

    /// Whether the cursor sits on a `= "mac#..."` / `= "sta#..."` /
    /// `= "ext#..."` — an external-name binding rather than a body.
    ///
    /// These are the strings ATS uses to say *where* the implementation
    /// lives (`"mac#name"` is a macro of `name`, `"ext#name"` a C symbol,
    /// `"sta#name"` a static one), as opposed to an expression.  They are
    /// the whole of what distinguishes a `.sats` signature that happens
    /// to carry a binding from a definition whose body is a string.
    /// Whether the cursor sits on `= "..."` — a declaration's string
    /// binding (an external name), as opposed to a real body.

    pub(crate) fn finish_fun_decl(
        &mut self,
        proof: bool,
        ty_params: Vec<String>,
        universals: Vec<Quant>,
        existentials: Vec<Quant>,
        name: String,
        params: Vec<Param>,
        ret: Ty,
    ) -> Result<FunDecl, CompileError> {
        if self.at(&TokenKind::Eq) {
            self.advance();
            if matches!(self.peek().kind, TokenKind::StrLit(_)) {
                self.advance();
            } else {
                return Err(self.error_here("expected an external name after `=`"));
            }
        }
        Ok(FunDecl {
            linear: false,
            proof,
            name,
            ty_params,
            universals,
            existentials,
            params,
            ret,
        })
    }

    /// The body of an `extern fun` declaration: everything a `fun` has
    /// except the `= body`.
    /// `dataprop P (s1, s2) = | {q} C (i1, i2) of (arg, ...) | ...`
    ///
    /// Returns one declaration per constructor, or `None` when the shape
    /// is one this parser does not model — in which case the whole
    /// declaration goes back to being skipped, costing its own proofs
    /// and not the file.

    pub(crate) fn parse_dataprop(&mut self, linear: bool) -> Option<Vec<FunDecl>> {
        self.advance(); // `dataprop` / `dataview`
        let TokenKind::Ident(prop) = self.peek().kind.clone() else {
            return None;
        };
        self.advance();
        self.props.insert(prop.clone());
        // `(int, int)` — the sorts it is indexed by.  How many there are
        // is all that matters here; what they are is checked by ATS.
        if self.at(&TokenKind::LParen) {
            self.skip_balanced(&TokenKind::LParen, &TokenKind::RParen);
        }
        if !self.at(&TokenKind::Eq) {
            return None;
        }
        self.advance();
        let mut out = Vec::new();
        loop {
            if self.at(&TokenKind::Pipe) {
                self.advance();
            }
            let universals = self.parse_quantifiers();
            let TokenKind::Ident(name) = self.peek().kind.clone() else {
                return None;
            };
            self.advance();
            // `(n, n*r)` — the indices *this* constructor's proof has.
            let indices = self.parse_index_terms();
            let ret = if indices.is_empty() {
                Ty::Name(prop.clone())
            } else {
                Ty::Index(Box::new(Ty::Name(prop.clone())), indices)
            };
            // `of FACT(n-1, r)` — the proofs it consumes.
            let mut params = Vec::new();
            if self.at(&TokenKind::Of) {
                self.advance();
                for (i, ty) in self.parse_constructor_fields()?.into_iter().enumerate() {
                    params.push(Param {
                        name: format!("pf{i}"),
                        ty,
                        borrowed: false,
                    });
                }
            }
            out.push(FunDecl {
                // A `dataview`'s proofs are *resources*: permission to
                // touch something, which could not be permission at all
                // if it could be used twice.
                linear,
                // A constructor of a proposition builds a proof, and a
                // proof is not a value.
                proof: true,
                name,
                ty_params: Vec::new(),
                universals,
                existentials: Vec::new(),
                params,
                ret,
            });
            if !self.at(&TokenKind::Pipe) {
                break;
            }
        }
        (!out.is_empty()).then_some(out)
    }

    /// The `of (a, b)` — or `of a` — that follows a constructor.
    ///
    /// `of ()` consumes nothing, which is how a base case is written.

    pub(crate) fn parse_constructor_fields(&mut self) -> Option<Vec<Ty>> {
        if !self.at(&TokenKind::LParen) {
            return self.parse_type().ok().map(|t| vec![t]);
        }
        self.advance();
        let mut out = Vec::new();
        if self.at(&TokenKind::RParen) {
            self.advance();
            return Some(out);
        }
        loop {
            out.push(self.parse_type().ok()?);
            if self.at(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        self.at(&TokenKind::RParen).then(|| {
            self.advance();
            out
        })
    }

    /// Whether the next token is one of the proof-language spellings of
    /// `fun`.  They declare the same thing — a name, its quantifiers,
    /// its parameters and its result — and differ only in that nothing
    /// they describe survives to run time.

    pub(crate) fn parse_extern_decl(&mut self) -> Result<FunDecl, CompileError> {
        // `praxi`/`prfun` declare a proof: the checker reads it, the
        // emitter never sees it.
        let proof = self.at_proof_keyword();
        self.advance(); // `fun` / `fn` / `praxi` / `prfun`
        let mut ty_params = self.parse_template_params();
        let name = self.expect_ident("expected a function name")?;
        // `{n:nat}` — a declaration's quantifiers say exactly what a
        // definition's do, and skipping them here left the corpus's
        // `extern fun`s promising nothing at all.
        let universals = self.parse_quantifiers();
        for (name, _) in universals
            .iter()
            .flat_map(|quantifier| &quantifier.vars)
            .filter(|(_, sort)| *sort == Sort::Type)
        {
            if !ty_params.contains(name) {
                ty_params.push(name.clone());
            }
        }
        // As with a `fun`, the template's parameters are in scope for
        // the signature being declared.
        let scope = self.push_type_vars(&ty_params);
        let (params, ret, existentials) = if self.at(&TokenKind::Colon) {
            // `extern fun fact : int -> int = "mac#fact"` — no
            // parenthesised parameter list; the whole signature is the
            // curried type after the colon, which is split back into a
            // parameter list and a return type.
            self.advance();
            self.skip_effect_annotation();
            let existentials = self.parse_existentials();
            let whole = self.parse_type()?;
            self.skip_static_annotations();
            let (params, ret) = Self::split_curried(whole);
            (params, ret, existentials)
        } else {
            let params = self.parse_params()?;
            if !self.at(&TokenKind::Colon) {
                return Err(self.error_here("expected `:` and a return type"));
            }
            self.advance();
            self.skip_effect_annotation();
            let existentials = self.parse_existentials();
            let ret = self.parse_type()?;
            self.skip_static_annotations();
            (params, ret, existentials)
        };
        // `= "ext#name"` binds the declaration to a C symbol; the subset
        // has no foreign-function interface, so the binding is dropped
        // and the signature kept.
        if self.at(&TokenKind::Eq) {
            self.advance();
            if matches!(self.peek().kind, TokenKind::StrLit(_)) {
                self.advance();
            } else {
                return Err(self.error_here("expected a foreign name after `=`"));
            }
        }
        self.pop_type_vars(scope);
        Ok(FunDecl {
            linear: false,
            proof,
            name,
            ty_params,
            universals,
            existentials,
            params,
            ret,
        })
    }

    /// `extern val f: (a, b) -> c` is ATS's value-level spelling of a
    /// function declaration. The implementation still uses
    /// `implement f (x, y) = ...`, so normalize it to the same `FunDecl`
    /// consumed by elaboration as `extern fun f (x: a, y: b): c`.

    pub(crate) fn parse_extern_val_decl(&mut self) -> Result<FunDecl, CompileError> {
        self.advance(); // `val`
        let name = self.expect_ident("expected an external value name")?;
        self.expect(
            &TokenKind::Colon,
            "expected `:` after the external value name",
        )?;
        self.skip_effect_annotation();
        let whole = self.parse_type()?;
        self.skip_static_annotations();
        let (params, ret) = Self::split_curried(whole);
        if params.is_empty() {
            return Err(self.error_here("external value is not a function"));
        }
        Ok(FunDecl {
            name,
            linear: false,
            proof: false,
            ty_params: Vec::new(),
            universals: Vec::new(),
            existentials: Vec::new(),
            params,
            ret,
        })
    }

    /// A curried function type, split back into a parameter list and a
    /// return type.
    ///
    /// `int -> int` declares one parameter of `int` returning `int`.  A
    /// colon-form signature (`fun abs_int0 : int -<fun> int`) writes the
    /// whole function as one type, and an `implement` that fills it in gives
    /// the parameter a name; the two have to agree on how many there are.

    pub(crate) fn split_curried(ty: Ty) -> (Vec<Param>, Ty) {
        let mut params = Vec::new();
        let mut cur = ty;
        loop {
            match cur {
                Ty::Fun(args, ret) => {
                    for a in args {
                        params.push(Param {
                            name: "_".into(),
                            ty: a,
                            borrowed: false,
                        });
                    }
                    cur = *ret;
                }
                other => return (params, other),
            }
        }
    }


    pub(crate) fn parse_implement_def(&mut self) -> Result<Def, CompileError> {
        self.advance(); // `implement`
                        // `implement(a) f<a> (x) = ...` — ATS lets a template's
                        // parameters be written in parentheses in front of the name as
                        // readily as in braces.  Nothing else can follow `implement`
                        // with a `(`, so the two spellings never compete.
        let mut ty_params = Vec::new();
        if self.at(&TokenKind::LParen) {
            self.advance();
            while let TokenKind::Ident(n) = self.peek().kind.clone() {
                self.advance();
                ty_params.push(n);
                if self.at(&TokenKind::Comma) {
                    self.advance();
                } else {
                    break;
                }
            }
            self.expect(
                &TokenKind::RParen,
                "expected `)` after the template parameters",
            )?;
        }
        ty_params.extend(self.parse_template_params());
        let name = self.parse_qualified_ident("expected a function name")?;
        // The implementation's own type parameters are in scope for the
        // instance it names, so `implement(res) f<res>` is the *generic*
        // implementation even where a `typedef res` is also in scope: a
        // binder shadows an outer name.
        let scope = self.push_type_vars(&ty_params);
        // `implement array_foreach$fwork<a><env> (x, e) = ...` — the
        // arguments say which instance is being filled in.  With one
        // instance per hole in practice, which one is not yet tracked;
        // the arguments are read so the parameter list can be found.
        let instance = self.parse_instance_arguments()?;
        self.pop_type_vars(scope);
        self.skip_static_annotations();
        // `implement x0 = e` — filling in an `extern val` with a value.
        // The `=` arriving where a parameter list would sit is the whole
        // of what separates a value from a function here.  With no
        // template and no instance to make it function-like, the body is
        // the value itself, and the implement is a top-level `val`.
        if self.at(&TokenKind::Eq) {
            self.advance(); // `=`
            let value = self.parse_expr(0)?;
            // `implement x0 = e` — filling in an `extern val` with a
            // value: no template, no instance, the body is the value.
            if ty_params.is_empty() && instance.is_empty() {
                return Ok(Def::Val(ValDef {
                    name,
                    ty: None,
                    value,
                }));
            }
            // `implement (a) fprint_val<list0(a)> = fprint_list0<a>` —
            // a template hole filled with a *function value* (a name and
            // its instance, no parameters here).  It is an implement
            // whose parameter list is empty.
            self.pop_type_vars(scope);
            return Ok(Def::Implement(ImplementDef {
                ty_params,
                instance,
                name,
                params: Vec::new(),
                ret: None,
                body: value,
            }));
        }
        // The implement's own parameters are in scope for its signature
        // and body, exactly as the declaration's were for it.
        let scope = self.push_type_vars(&ty_params);
        let params = self.parse_params_maybe_untyped(true)?;
        let ret = if self.at(&TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };
        self.expect(&TokenKind::Eq, "expected `=` before the implement body")?;
        let body = self.parse_expr(0)?;
        self.pop_type_vars(scope);
        Ok(Def::Implement(ImplementDef {
            ty_params,
            instance,
            name,
            params,
            ret,
            body,
        }))
    }

    /// Whether the token after the cursor starts something new rather
    /// than continuing the current directive.
    ///
    /// `#define cons stream_vt_cons` is one name for another;
    /// `#define f(x) g(x)` and `#define N M + 1` are not, and the
    /// difference is only visible in what follows the name.

    pub(crate) fn parse_qualified_ident(&mut self, what: &str) -> Result<String, CompileError> {
        let mut name = self.expect_ident(what)?;
        while self.at(&TokenKind::Dot)
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|t| matches!(t.kind, TokenKind::Ident(_)))
        {
            self.advance(); // `.`
            name = self.expect_ident(what)?;
        }
        Ok(name)
    }

    /// The `<...>` of `implement fprint_val<list0(int)> (out, xs) = ...`.
    ///
    /// Only an angle group names an instance.  A brace group after the
    /// name is a *static* argument — `implement{a} f {n} (xs) = ...`
    /// quantifies over the index `n` and is still the generic
    /// implementation — so reading one as a type would file the body
    /// under an instance nobody ever asks for and leave the generic case
    /// with nothing.

    pub(crate) fn parse_instance_arguments(&mut self) -> Result<Vec<Ty>, CompileError> {
        while self.at(&TokenKind::LBrace) {
            let save = self.pos;
            self.read_static_group(save);
            self.skip_balanced(&TokenKind::LBrace, &TokenKind::RBrace);
        }
        Ok(self.parse_template_arguments()?.unwrap_or_default())
    }

    /// Read a `{a:t@ype}` / `{a,b:t0p}` / `{a}` template parameter list,
    /// if one is here.
    ///
    /// Only the *names* survive: the sort on the right of the colon
    /// (`t@ype`, `t0p`, `type`) constrains what may be substituted, which
    /// is a question for a type checker this compiler does not have.

    pub(crate) fn parse_template_params(&mut self) -> Vec<String> {
        let mut names = Vec::new();
        while self.at(&TokenKind::LBrace) {
            let save = self.pos;
            self.advance();
            let mut group = Vec::new();
            loop {
                match self.peek().kind.clone() {
                    TokenKind::Ident(n) => {
                        self.advance();
                        group.push(n);
                    }
                    _ => break,
                }
                if self.at(&TokenKind::Comma) {
                    self.advance();
                } else {
                    break;
                }
            }
            // `{n:nat}` quantifies over an *index*; `{a:t@ype}` over a
            // type, and only the latter is a template parameter.
            //
            // The sorts are told apart by listing the *index* ones: a type
            // sort is spelled `t@ype`, which the lexer cuts into three
            // tokens (`t`, `@`, `ype`), so matching those by name would be
            // brittle in a way matching `nat` and `int` is not.
            let mut is_type_sort = true;
            if self.at(&TokenKind::Colon) {
                self.advance();
                if let TokenKind::Ident(sort) = self.peek().kind.clone() {
                    is_type_sort = !is_index_sort(&sort);
                }
            }
            self.pos = save;
            self.skip_balanced(&TokenKind::LBrace, &TokenKind::RBrace);
            if is_type_sort {
                names.extend(group);
            }
        }
        names
    }

    /// Skip the static-language decorations that may sit between a
    /// function's name, its parameters, and its body: quantifiers
    /// (`{n:nat}`), existentials (`[r:int]`), and termination metrics
    /// (`.<n>.`).  They exist for the ATS type checker, which we are not.
    /// Read the `{...}` quantifiers and `.<...>.` metrics that stand
    /// between a function's name and its parameters.
    ///
    /// A quantifier this parser can model is *kept* — it is the half of
    /// the signature that says which arguments are legal.  One it cannot
    /// (a sort it does not know, a guard outside the shared fragment)
    /// falls back to being skipped, so an unmodelled form costs
    /// precision rather than the whole file.

    pub(crate) fn parse_typedef(&mut self) -> bool {
        // The leading keyword is the token we are sitting on (`typedef`,
        // or an abstract form like `abstype`).  It is consumed, and the
        // aliases that follow are read by the body reader.
        let save = self.pos;
        self.advance();
        if !self.parse_typedef_body() {
            self.pos = save;
            return false;
        }
        true
    }

    /// `where xs = List0(x)` following a datatype declaration.
    ///
    /// ATS scopes this alias over the declaration group. The flattened
    /// compiler namespace retains it as an ordinary type alias so subsequent
    /// signatures still see the intended type.

    pub(crate) fn parse_where_type_alias(&mut self) -> Result<(), CompileError> {
        self.advance(); // `where`
        let name = self.expect_ident("expected a type name after `where`")?;
        self.expect(&TokenKind::Eq, "expected `=` in the `where` type alias")?;
        let ty = self.parse_type()?;
        self.typedefs.insert(name, ty);
        Ok(())
    }

    /// `abstype point` with no `= t`.  An abstract type whose
    /// representation is not given is opaque: its values are boxed.  It
    /// is registered as the unnamed type, so the emitter lowers any use
    /// of it to a pointer rather than refusing an unknown name.

    pub(crate) fn parse_abstract_opaque(&mut self) -> bool {
        let save = self.pos;
        let joined = self.at_at_joined_abstract();
        let abstract_word = !joined
            && matches!(
                &self.tokens[self.pos].kind,
                TokenKind::Ident(w)
                    if matches!(
                        w.as_str(),
                        "abstype" | "absvtype" | "abst0ype" | "abstbox" | "abstflat" | "abstract"
                    )
            );
        if !joined && !abstract_word {
            return false;
        }
        if joined {
            // `abst @ ype` — the abstract keyword cut at the `@`.
            self.advance();
            self.advance();
            self.advance();
        } else {
            self.advance(); // the abstract keyword
        }
        let Some(TokenKind::Ident(name)) = self.tokens.get(self.pos).map(|t| t.kind.clone()) else {
            self.pos = save;
            return false;
        };
        self.advance();
        // `abstype point (a) = ...` — a parameterised family governed by
        // its `=`, not an opaque leaf.  A `(` here means there is more
        // to this declaration than a bare name; hand it back.
        if self.at(&TokenKind::LParen) {
            self.pos = save;
            return false;
        }
        // A concrete `= t` is the ordinary abstract alias, which the
        // `typedef` reader already took; arriving here with an `=` means
        // this branch was reached out of turn and should not claim it.
        if self.at(&TokenKind::Eq) {
            self.pos = save;
            return false;
        }
        self.typedefs.insert(name, Ty::Name("_".into()));
        true
    }

    /// The body of a `typedef`, once the keyword is consumed: one or more
    /// `name [params] = type` aliases joined by `and`.  Split out from
    /// `parse_typedef` so the abstract `abst @ ype` form, whose keyword
    /// the lexer cut into three tokens, can feed it the same shape a
    /// single-word keyword would.

    pub(crate) fn parse_typedef_body(&mut self) -> bool {
        let start = self.pos;
        // `typedef key = string and itm = symbol` chains several aliases;
        // the `and` is the chain, not a function's mutual-recursion word.
        loop {
            let Some(TokenKind::Ident(name)) = self.tokens.get(self.pos).map(|t| t.kind.clone())
            else {
                self.pos = start;
                return false;
            };
            self.advance();
            // `typedef pair (a:t@ype) = ...` — an alias for a *family* of
            // types.  The parameters are in scope for the body and are
            // substituted at each use, which is the whole of what a
            // parameterized alias means.
            let mut params = Vec::new();
            if self.at(&TokenKind::LParen) {
                self.advance();
                while let TokenKind::Ident(pp) = self.peek().kind.clone() {
                    self.advance();
                    params.push(pp);
                    if self.at(&TokenKind::Colon) {
                        self.advance();
                        if self.parse_sort_name().is_none() {
                            self.pos = start;
                            return false;
                        }
                    }
                    if self.at(&TokenKind::Comma) {
                        self.advance();
                    } else {
                        break;
                    }
                }
                if !self.at(&TokenKind::RParen) {
                    self.pos = start;
                    return false;
                }
                self.advance();
            }
            if !self.at(&TokenKind::Eq) {
                self.pos = start;
                return false;
            }
            self.advance();
            let scope = self.push_type_vars(&params);
            let parsed = self.parse_type();
            self.pop_type_vars(scope);
            match parsed {
                Ok(ty) if !params.is_empty() => {
                    self.typedef_families.insert(name, (params, ty));
                }
                Ok(ty) => {
                    self.typedefs.insert(name, ty);
                }
                Err(_) => {
                    self.pos = start;
                    return false;
                }
            }
            // `and itm = symbol` — the next alias in the chain.
            if matches!(&self.peek().kind, TokenKind::Ident(w) if w == "and") {
                self.advance();
                continue;
            }
            return true;
        }
    }

    /// Whether the cursor rests on `abst @ ype` — the abstract linear
    /// type form, which the lexer cuts apart at the `@` into three
    /// tokens.  Rejoining them reads like `abstype`, the boxed form;
    /// both are declarations of a type name, and the difference is one
    /// of representation the subset does not distinguish.
    /// The abstract-type forms written `abst@ype`, `absvt@ype`,
    /// `absviewt@ype` — the linear, view, and viewtype spellings, all
    /// cut at the `@` by the lexer into three tokens.

    pub(crate) fn at_at_joined_abstract(&self) -> bool {
        let is_prefix = matches!(
            &self.tokens[self.pos].kind,
            TokenKind::Ident(w) if is_abstract_atype_prefix(w)
        );
        if !is_prefix {
            return false;
        }
        if !matches!(
            self.tokens.get(self.pos + 1).map(|t| &t.kind),
            Some(TokenKind::At)
        ) {
            return false;
        }
        matches!(
            self.tokens.get(self.pos + 2).map(|t| &t.kind),
            Some(TokenKind::Ident(_))
        )
    }

    /// Read `abst @ ype name = type` as a type alias.  The three keyword
    /// tokens are consumed, and the body is read exactly as `abstype`'s
    /// would be.

    pub(crate) fn parse_at_joined_abstract(&mut self) -> bool {
        let save = self.pos;
        if !self.at_at_joined_abstract() {
            return false;
        }
        self.advance(); // prefix
        self.advance(); // `@`
        self.advance(); // `ype`
        if !self.parse_typedef_body() {
            self.pos = save;
            return false;
        }
        true
    }

    /// `macdef name = expr` — bind a name to an expression.
    ///
    /// Only the parameterless form is handled.  A macro *with* parameters
    /// takes antiquoted arguments (`macdef f (x) = g ,(x)`), which is a
    /// different mechanism; one that is not understood is skipped rather
    /// than half-expanded.

    pub(crate) fn parse_macdef(&mut self) {
        let save = self.pos;
        self.advance(); // `macdef`
        let Some(name) = (match self.peek().kind.clone() {
            TokenKind::Ident(n) => Some(n),
            _ => None,
        }) else {
            self.pos = save;
            self.skip_local_directive();
            return;
        };
        self.advance();
        // `macdef size (bt) = ...` — a macro with parameters.  The body
        // keeps them as ordinary variables; each use splices its
        // arguments in for them, which is the lexical substitution ATS's
        // own macro expander performs.
        let mut params = Vec::new();
        if self.at(&TokenKind::LParen) {
            self.advance();
            loop {
                match self.peek().kind.clone() {
                    TokenKind::Ident(n) => {
                        self.advance();
                        params.push(n);
                    }
                    _ => break,
                }
                if self.at(&TokenKind::Comma) {
                    self.advance();
                } else {
                    break;
                }
            }
            if !self.at(&TokenKind::RParen) {
                self.pos = save;
                self.skip_local_directive();
                return;
            }
            self.advance();
        }
        if !self.at(&TokenKind::Eq) {
            self.pos = save;
            self.skip_local_directive();
            return;
        }
        self.advance();
        self.macro_depth += 1;
        let parsed = self.parse_expr(0);
        self.macro_depth -= 1;
        match parsed {
            Ok(body) => {
                if params.is_empty() {
                    self.macros.insert(name, body);
                } else {
                    self.macro_funs.insert(name, (params, body));
                }
            }
            Err(_) => {
                self.pos = save;
                self.skip_local_directive();
            }
        }
    }

    /// `overload OP with FUNC` — a function to try when an operator's
    /// operands do not fit it.
    /// `exception X`, `exception X of t` or `exception X of (t1, t2)` —
    /// an exception constructor: a member of the built-in `exn` type,
    /// carrying the given payload (or none).  The fields may be
    /// parenthesized or not — ATS admits both — and one declaration may
    /// name several exceptions after the first: `exception A and B`
    /// declares two.

    pub(crate) fn parse_exception(&mut self) -> Vec<Def> {
        let save = self.pos;
        self.advance(); // `exception`
        let mut out = Vec::new();
        loop {
            let TokenKind::Ident(name) = self.peek().kind.clone() else {
                self.pos = save;
                return out;
            };
            self.advance();
            let mut fields = Vec::new();
            if self.at(&TokenKind::Of) {
                self.advance();
                if self.at(&TokenKind::LParen) {
                    self.advance();
                    if !self.at(&TokenKind::RParen) {
                        loop {
                            let Ok(ty) = self.parse_type() else {
                                self.pos = save;
                                return Vec::new();
                            };
                            fields.push(ty);
                            if self.at(&TokenKind::Comma) {
                                self.advance();
                            } else {
                                break;
                            }
                        }
                    }
                    if self
                        .expect(
                            &TokenKind::RParen,
                            "expected `)` after the exception fields",
                        )
                        .is_err()
                    {
                        return Vec::new();
                    }
                } else {
                    let Ok(ty) = self.parse_type() else {
                        self.pos = save;
                        return Vec::new();
                    };
                    fields.push(ty);
                }
            }
            out.push(Def::Exception(name, fields));
            if self.at_ident("and") {
                self.advance();
                continue;
            }
            return out;
        }
    }


    pub(crate) fn parse_overload(&mut self) -> Option<Def> {
        let save = self.pos;
        self.advance(); // `overload`
        let op = match self.peek().kind.clone() {
            TokenKind::Star => "*".to_string(),
            TokenKind::Slash => "/".to_string(),
            TokenKind::Plus => "+".to_string(),
            TokenKind::Minus => "-".to_string(),
            TokenKind::Lt => "<".to_string(),
            TokenKind::Gt => ">".to_string(),
            TokenKind::Le => "<=".to_string(),
            TokenKind::Ge => ">=".to_string(),
            TokenKind::Eq => "=".to_string(),
            TokenKind::Ne => "<>".to_string(),
            TokenKind::Ident(n) => n,
            TokenKind::LBracket => {
                self.advance();
                if self.at(&TokenKind::RBracket) {
                    self.advance();
                }
                self.skip_directive();
                return None;
            }
            _ => {
                self.pos = save;
                self.skip_directive();
                return None;
            }
        };
        self.advance();
        if !matches!(self.peek().kind, TokenKind::With)
            && !matches!(&self.peek().kind, TokenKind::Ident(w) if w == "with")
        {
            self.pos = save;
            self.skip_directive();
            return None;
        }
        self.advance();
        let TokenKind::Ident(func) = self.peek().kind.clone() else {
            self.pos = save;
            self.skip_directive();
            return None;
        };
        self.advance();
        // `overload * with list0_cross of 10` — the `of <n>` names a
        // precedence level for the overloaded operator.  It is only a
        // hint to the type checker's disambiguation, so it is read and
        // dropped.
        if self.at(&TokenKind::Of) {
            // `of 10` — the precedence level, a single number.
            self.advance();
            if matches!(self.peek().kind, TokenKind::IntLit(_)) {
                self.advance();
            }
        }
        Some(Def::Overload {
            op: op.to_string(),
            func,
        })
    }
}
