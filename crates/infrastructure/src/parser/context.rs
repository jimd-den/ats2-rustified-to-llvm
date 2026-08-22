use ats2_domain::ast::*;
use ats2_domain::errors::CompileError;
use ats2_domain::statics::*;
use ats2_domain::tokens::*;
use std::collections::{HashMap, HashSet};

pub(crate) fn is_skippable_directive(word: &str) -> bool {
    matches!(
        word,
        "staload"
            | "dynload"
            | "typedef"
            | "abstype"
            | "abstract"
            | "absvtype"
            | "abst0ype"
            | "abstbox"
            | "abstflat"
            | "sortdef"
            | "stadef"
            | "stacst"
            | "assume"
            | "overload"
            | "macdef"
            | "extern"
            | "static"
            | "praxi"
            | "prfun"
            | "prval"
            | "dataprop"
            | "dataview"
            | "datasort"
            | "propdef"
            | "viewdef"
            | "vtypedef"
            | "symintr"
            | "infix"
            | "infixl"
            | "infixr"
            | "prefix"
            | "postfix"
            | "nonfix"
            | "classdec"
            | "exception"
            | "primplmnt"
            | "primplement"
            | "abst@ype"
            | "absview"
            | "absviewtype"
            | "absprop"
            | "viewtypedef"
            | "viewtype"
            | "vtype"
            | "dataviewtype"
            | "symelim"
            | "symload"
            | "tkindef"
            | "sexpdef"
            | "vwtpdef"
            | "irregular"
            | "withprop"
            | "withtype"
            | "withview"
            | "withviewtype"
            | "withvtype"
            | "reassume"
    )
}

pub(crate) fn load_kind(path: &str, dynamic: bool, anonymous: bool) -> ats2_domain::ast::LoadKind {
    if dynamic {
        ats2_domain::ast::LoadKind::Dynamic
    } else if anonymous || !path.ends_with(".sats") {
        ats2_domain::ast::LoadKind::Implementation
    } else {
        ats2_domain::ast::LoadKind::Interface
    }
}

/// Whether a name is a variance annotation rather than a type former.
pub(crate) fn is_variance_annotation(name: &str) -> bool {
    matches!(name, "INV" | "OUT" | "INVAR")
}

/// Whether a bare word can begin a top-level declaration.
///
/// Most declaration keywords are lexed as keywords, but a few — `extern`,
/// `and`, `where` — stay ordinary identifiers, and those are the ones a
/// type could otherwise absorb as a static index.
pub(crate) fn starts_a_declaration(word: &str) -> bool {
    is_skippable_directive(word)
        || is_abstract_atype_prefix(word)
        || matches!(word, "and" | "where")
}

/// Whether `word` is the prefix of an abstract-type form written with an
/// `@`, like `abst@ype`, `absvt@ype`, `absviewt@ype`.  The lexer cuts the
/// `@` out, so the prefix arrives alone and has to be recognised for what
/// it begins.
pub(crate) fn is_abstract_atype_prefix(word: &str) -> bool {
    matches!(word, "abst" | "absvt" | "absviewt")
}

/// One `val`/`var` binding: a plain name, or a pattern the source
/// insists must match.
pub(crate) enum BindKind {
    Simple(LetBind),
    Pattern(Pattern, Expr),
}

/// `val pat = e` — the match the source insists must succeed.  A
/// non-match leaves through `exit`, because the pattern having failed
/// means the program's own guarantee about its data is broken.
pub(crate) fn must_match(value: Expr, pattern: Pattern, rest: Expr) -> Expr {
    let exit = Expr::Call(Box::new(Expr::Var("exit".into())), vec![Expr::IntLit(1)]);
    Expr::Case(
        Box::new(value),
        vec![(pattern, rest), (Pattern::Wildcard, exit)],
    )
}

/// Substitute each macro argument for its parameter throughout a macro
/// body — the splice `,(x)` performs at the use site.
///
/// The substitution is purely syntactic, which is the point: a macro
/// means whatever it meant where it was written, so an argument's
/// variables keep their call-site meaning and the body's keep theirs.
pub(crate) fn splice_macro_args(expr: &Expr, params: &[String], args: &[Expr]) -> Expr {
    use Expr as E;
    let sub = |e: &Expr| splice_macro_args(e, params, args);
    match expr {
        E::Var(n) => match params.iter().position(|p| p == n) {
            Some(i) => args.get(i).cloned().unwrap_or(E::Wildcard),
            None => expr.clone(),
        },
        // Static instantiation carries no dynamic content, so every
        // pass that rewrites *code* looks straight through it.
        E::StaticInst(inner, at) => E::StaticInst(Box::new(sub(inner)), at.clone()),
        E::ProofPair(p, v) => E::ProofPair(Box::new(sub(p)), Box::new(sub(v))),
        E::Ascribe(inner, ty) => E::Ascribe(Box::new(sub(inner)), ty.clone()),
        E::Wildcard
        | E::Unit
        | E::Uninit
        | E::IntLit(_)
        | E::CharLit(_)
        | E::FloatLit(_)
        | E::BoolLit(_)
        | E::StrLit(_)
        | E::Inst(..) => expr.clone(),
        E::UnaryNeg(e) => E::UnaryNeg(Box::new(sub(e))),
        E::BinOp(op, l, r) => E::BinOp(*op, Box::new(sub(l)), Box::new(sub(r))),
        E::TupleLit(items) => E::TupleLit(items.iter().map(sub).collect()),
        E::Call(c, items) => E::Call(Box::new(sub(c)), items.iter().map(sub).collect()),
        E::ExtVal {
            ty,
            name,
            args,
            via_ptr,
        } => E::ExtVal {
            ty: ty.clone(),
            name: name.clone(),
            args: args.iter().map(sub).collect(),
            via_ptr: *via_ptr,
        },
        E::Index(b, i) => E::Index(Box::new(sub(b)), Box::new(sub(i))),
        E::Store(p, v) => E::Store(Box::new(sub(p)), Box::new(sub(v))),
        E::Deref(e) => E::Deref(Box::new(sub(e))),
        E::Proj(e, i) => E::Proj(Box::new(sub(e)), *i),
        E::IfThenElse(c, t, e) => {
            E::IfThenElse(Box::new(sub(c)), Box::new(sub(t)), Box::new(sub(e)))
        }
        E::Let(binds, body) => E::Let(
            binds
                .iter()
                .map(|b| LetBind {
                    value: sub(&b.value),
                    ..b.clone()
                })
                .collect(),
            Box::new(sub(body)),
        ),
        E::Lam(ps, r, b) => E::Lam(ps.clone(), r.clone(), Box::new(sub(b))),
        E::Field(b, n) => E::Field(Box::new(sub(b)), n.clone()),
        E::RecordLit(fields) => {
            E::RecordLit(fields.iter().map(|(n, v)| (n.clone(), sub(v))).collect())
        }
        E::LetFun(funs, body) => E::LetFun(
            funs.iter()
                .map(|f| FunDef {
                    body: sub(&f.body),
                    ..f.clone()
                })
                .collect(),
            Box::new(sub(body)),
        ),
        // Assigning to a name is not a splice this subset ever sees —
        // the store keeps the name it was given.
        E::Assign(n, v) => E::Assign(n.clone(), Box::new(sub(v))),
        E::While(c, b) => E::While(Box::new(sub(c)), Box::new(sub(b))),
        E::For(i, c, s, b) => E::For(
            Box::new(sub(i)),
            Box::new(sub(c)),
            Box::new(sub(s)),
            Box::new(sub(b)),
        ),
        E::Case(scrut, arms) => E::Case(
            Box::new(sub(scrut)),
            arms.iter().map(|(p, b)| (p.clone(), sub(b))).collect(),
        ),
        E::Try(scrut, handlers) => E::Try(
            Box::new(sub(scrut)),
            handlers.iter().map(|(p, b)| (p.clone(), sub(b))).collect(),
        ),
        E::Raise(value) => E::Raise(Box::new(sub(value))),
        E::MacroCall(n, items) => E::MacroCall(n.clone(), items.iter().map(sub).collect()),
    }
}

/// Whether a sort names *index* terms rather than types.
///
/// `{n:nat}` quantifies over numbers the type checker reasons about;
/// `{a:t@ype}` over the types a template is instantiated at.  Only the
/// latter is a template parameter.
/// The types whose arguments are *static indices* rather than types.
///
/// ATS decides this from the type constructor's own declaration.  This
/// compiler has no static-language declarations to consult, so the
/// primitive families — which are the ones the corpus indexes — are
/// listed, and everything else is read as a type application.  The value
/// is the base type the family refines, so `natLt(n)` is an `int` that
/// happens to be known to sit below `n`.
pub(crate) fn indexed_base(name: &str) -> Option<&'static str> {
    if let Some(base) = crate::prelude::canonical_scalar_type(name) {
        return Some(base);
    }
    Some(match name {
        "int" | "intGt" | "intGte" | "intLt" | "intLte" | "intBtw" | "intBtwe" | "nat"
        | "natLt" | "natLte" | "natGt" | "natGte" | "pos" | "Nat" | "Pos" => "int",
        "uint" | "uintGt" | "uintGte" | "uintLt" | "uintLte" | "size_t" | "ssize_t" | "sizeGt"
        | "sizeGte" | "sizeLt" | "sizeLte" | "sizeBtw" | "sizeBtwe" => "int",
        "string" => "string",
        "bool" => "bool",
        "char" => "char",
        // `ptr(n)` — a pointer to `n` cells, and `ptr(l)` a pointer at
        // the address `l`.  Either way the argument measures the
        // pointer rather than describing it, and a pointer is a
        // pointer whatever it points at.
        "ptr" => "ptr",
        _ => return None,
    })
}

pub(crate) fn is_index_sort(sort: &str) -> bool {
    matches!(
        sort,
        "int" | "nat" | "pos" | "bool" | "addr" | "eff" | "cls" | "sta" | "size"
    )
}

/// Read a dynamic expression as a static term.
///
/// The two languages share a surface syntax for arithmetic and
/// comparison, so the dynamic expression parser reads `n > 0` and
/// `m*n+1` correctly already; what differs is what the result *means*.
/// Rather than duplicate a Pratt parser that would have to be kept in
/// step with the first one, the shared fragment is parsed once and
/// reinterpreted here.  A form with no static meaning yields `None`,
/// which the caller turns back into "skip this annotation".
pub(crate) fn sexp_of_expr(e: &Expr) -> Option<SExp> {
    Some(match e {
        Expr::IntLit(n) => SExp::IntLit(*n),
        Expr::BoolLit(b) => SExp::BoolLit(*b),
        Expr::Var(n) => SExp::Var(n.clone()),
        Expr::UnaryNeg(x) => SExp::App("~".into(), vec![sexp_of_expr(x)?]),
        Expr::BinOp(op, l, r) => SExp::App(
            static_op(*op)?.into(),
            vec![sexp_of_expr(l)?, sexp_of_expr(r)?],
        ),
        // `max(m, n)`, `min(m, n)` — a static function, applied.
        Expr::Call(f, args) => {
            let Expr::Var(name) = &**f else { return None };
            let args: Option<Vec<SExp>> = args.iter().map(sexp_of_expr).collect();
            SExp::App(name.clone(), args?)
        }
        _ => return None,
    })
}

/// Whether a static term states a *relation* rather than naming a value.
///
/// It is what separates `[fact(0) == 1]` — a claim — from `{n}` — an
/// argument.  Both are a bracketed term; only one of them may be
/// believed.
pub(crate) fn is_relation(e: &SExp) -> bool {
    matches!(
        e,
        SExp::App(op, args)
            if args.len() == 2
                && matches!(op.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||")
    )
}

/// The static language's spelling of a shared operator.
pub(crate) fn static_op(op: BinOp) -> Option<&'static str> {
    Some(match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Andalso => "&&",
        BinOp::Orelse => "||",
    })
}

/// The type of a parameter whose annotation the language itself supplies.
///
/// `main (argc, argv)` is the case that matters: its shape is fixed, so
/// ATS programs never write it out.
pub(crate) fn well_known_param_type(name: &str) -> Option<Ty> {
    match name {
        "argc" => Some(Ty::Name("int".into())),
        "argv" => Some(Ty::Name("argv".into())),
        _ => None,
    }
}

/// The value an uninitialized `var` of this type starts from.
pub(crate) fn zero_of(ty: &Ty) -> Option<Expr> {
    match ty {
        Ty::Name(n) => match n.as_str() {
            "int" => Some(Expr::IntLit(0)),
            "char" => Some(Expr::CharLit(0)),
            "double" | "float" => Some(Expr::FloatLit(crate::lexer::float_bits(0.0))),
            "bool" => Some(Expr::BoolLit(false)),
            "string" => Some(Expr::StrLit(String::new())),
            // Everything else — a datatype, a tuple, a template's type
            // variable — has a zero the *emitter* knows and the parser
            // does not, because it is a property of the representation
            // rather than of the syntax.  So the question is deferred
            // rather than answered wrongly.
            _ => Some(Expr::Uninit),
        },
        _ => Some(Expr::Uninit),
    }
}

/// Replace a parameterized alias's parameters throughout its body.
pub(crate) fn substitute_type(ty: &Ty, subst: &HashMap<String, Ty>) -> Ty {
    match ty {
        Ty::Name(n) => subst.get(n).cloned().unwrap_or_else(|| ty.clone()),
        Ty::App(n, args) => Ty::App(
            n.clone(),
            args.iter().map(|a| substitute_type(a, subst)).collect(),
        ),
        Ty::Tuple(items) => Ty::Tuple(items.iter().map(|i| substitute_type(i, subst)).collect()),
        Ty::Proof(p, v) => Ty::Proof(
            Box::new(substitute_type(p, subst)),
            Box::new(substitute_type(v, subst)),
        ),
        Ty::Record(fields) => Ty::Record(
            fields
                .iter()
                .map(|(n, t)| (n.clone(), substitute_type(t, subst)))
                .collect(),
        ),
        Ty::Fun(ps, r) => Ty::Fun(
            ps.iter().map(|p| substitute_type(p, subst)).collect(),
            Box::new(substitute_type(r, subst)),
        ),
        // A parameter stands for a type, never for a static index, so
        // the indices ride along untouched.
        Ty::Index(base, idx) => Ty::Index(Box::new(substitute_type(base, subst)), idx.clone()),
    }
}

/// The name prefix a top-level statement is filed under.
///
/// `val () = e` at the top level binds nothing and produces nothing; it
/// is there to be *run*.  A name is still the simplest way to carry it
/// through the pipeline, so it gets one no ATS source could collide
/// with, and the emitter recognises it and stores nothing.
pub const TOPLEVEL_STATEMENT: &str = "$stmt";

/// Wrap a body in its nested function definitions, if it has any.
pub(crate) fn wrap_funs(funs: Vec<FunDef>, body: Expr) -> Expr {
    if funs.is_empty() {
        body
    } else {
        Expr::LetFun(funs, Box::new(body))
    }
}

/// A fallback token used when the cursor runs past the end of a hand-made
/// stream (the lexer always terminates with `Eof`, so this is a guard).
pub(crate) const EOF_TOKEN: Token = Token {
    kind: TokenKind::Eof,
    span: Span {
        start: Pos {
            line: 0,
            column: 0,
            offset: 0,
        },
        end: Pos {
            line: 0,
            column: 0,
            offset: 0,
        },
    },
};

/// The parsing cursor: a position into a token slice plus the accumulated
/// defs.  `pos` never advances past the final `Eof`.
pub(crate) struct ParseCtx<'a> {
    pub(crate) tokens: &'a [Token],
    pub(crate) pos: usize,
    pub(crate) macros: HashMap<String, Expr>,
    pub(crate) typedefs: HashMap<String, Ty>,
    pub(crate) pending: Vec<Def>,
    pub(crate) staloads: Vec<Staload>,
    pub(crate) includes: Vec<Include>,
    pub(crate) gensym: usize,
    pub(crate) typedef_families: HashMap<String, (Vec<String>, Ty)>,
    pub(crate) props: HashSet<String>,
    pub(crate) datatypes: HashSet<String>,
    pub(crate) renames: HashMap<String, String>,
    pub(crate) cons_name: String,
    pub(crate) type_vars: Vec<String>,
    pub(crate) macro_funs: HashMap<String, (Vec<String>, Expr)>,
    pub(crate) macro_depth: usize,
}

impl<'a> ParseCtx<'a> {
    pub(crate) fn new(tokens: &'a [Token]) -> Self {
        Self {
            tokens,
            pos: 0,
            macros: HashMap::new(),
            typedefs: HashMap::new(),
            pending: Vec::new(),
            staloads: Vec::new(),
            includes: Vec::new(),
            gensym: 0,
            type_vars: Vec::new(),
            macro_funs: HashMap::new(),
            macro_depth: 0,
            cons_name: "cons".into(),
            renames: HashMap::new(),
            typedef_families: HashMap::new(),
            props: HashSet::new(),
            datatypes: HashSet::new(),
        }
    }

    // --- cursor primitives -----------------------------------------


    pub(crate) fn peek(&self) -> &Token {
        self.tokens.get(self.pos).unwrap_or(&EOF_TOKEN)
    }


    pub(crate) fn at_ident(&self, word: &str) -> bool {
        matches!(&self.peek().kind, TokenKind::Ident(w) if w == word)
    }


    pub(crate) fn at(&self, kind: &TokenKind) -> bool {
        self.peek().kind == *kind
    }


    pub(crate) fn advance(&mut self) {
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
    }


    pub(crate) fn expect(&mut self, kind: &TokenKind, what: &str) -> Result<(), CompileError> {
        if self.at(kind) {
            self.advance();
            Ok(())
        } else {
            Err(self.error_here(what))
        }
    }


    pub(crate) fn expect_ident(&mut self, what: &str) -> Result<String, CompileError> {
        match self.peek().kind.clone() {
            TokenKind::Ident(name) => {
                self.advance();
                Ok(name)
            }
            _ => Err(self.error_here(what)),
        }
    }


    pub(crate) fn error_here(&self, message: impl Into<String>) -> CompileError {
        CompileError::parse(self.peek().span, message)
    }

    // --- program level ---------------------------------------------


    pub(crate) fn nth(&self, n: usize) -> Option<&TokenKind> {
        self.tokens.get(n).map(|t| &t.kind)
    }

    /// Consume a form we do not model, stopping just before whatever looks
    /// like the start of the next top-level form.
    ///
    /// ATS terminates no declaration with punctuation, so there is no
    /// token that says "the `staload` ends here".  Scanning to the next
    /// definition keyword is the pragmatic rule, and it is safe precisely
    /// because those keywords cannot appear inside the forms being
    /// skipped.

    pub(crate) fn skip_directive(&mut self) {
        self.advance();
        loop {
            match &self.peek().kind {
                TokenKind::Eof
                | TokenKind::Fun
                | TokenKind::Fn
                | TokenKind::Implement
                | TokenKind::Datatype
                | TokenKind::Local
                | TokenKind::In
                | TokenKind::End
                // A top-level `val` or `var` begins a form too.  The
                // proof spellings — `prval`, `prvar`, `praxi` — are
                // ordinary identifiers to the lexer, so stopping here
                // does not stop on those.
                | TokenKind::Val
                | TokenKind::Var
                | TokenKind::Hash => return,
                TokenKind::Ident(w) if is_skippable_directive(w) => return,
                // `datavtype` begins a definition even though it is not
                // a keyword token, so the skip stops on it too.
                TokenKind::Ident(w) if w == "datavtype" => return,
                // `fnx`/`prfn`/`prfun` begin a definition even though they
                // are identifiers to the lexer, so skipping stops on them.
                _ if self.at_fun_def_keyword() => return,
                _ => {
                    let before = self.pos;
                    self.advance();
                    if self.pos == before {
                        return; // parked on the final Eof
                    }
                }
            }
        }
    }


    pub(crate) fn push_type_vars(&mut self, names: &[String]) -> usize {
        let depth = self.type_vars.len();
        self.type_vars.extend(names.iter().cloned());
        depth
    }


    pub(crate) fn pop_type_vars(&mut self, depth: usize) {
        self.type_vars.truncate(depth);
    }

    /// `(a, b)` or `(a:t@ype)` after a datatype name — optional.
    ///
    /// As with a template's parameters, only the names matter: the sort on
    /// the right of the colon constrains what may be substituted, which is
    /// a question for a type checker this compiler does not have.

    pub(crate) fn directive_ends_after_one_token(&self) -> bool {
        match self.tokens.get(self.pos + 1).map(|t| &t.kind) {
            None | Some(TokenKind::Eof) => true,
            Some(TokenKind::Ident(w)) => !matches!(w.as_str(), "and" | "where"),
            Some(k) => matches!(
                k,
                TokenKind::Hash
                    | TokenKind::Val
                    | TokenKind::Var
                    | TokenKind::Fun
                    | TokenKind::Fn
                    | TokenKind::Implement
                    | TokenKind::Datatype
                    | TokenKind::Local
                    | TokenKind::In
                    | TokenKind::End
            ),
        }
    }

    /// A name, with any module qualification stripped off.
    ///
    /// `$RG.randgen_val` names `randgen_val` in the module a `staload`
    /// bound to `$RG`.  This compiler links one program at a time and
    /// keeps one flat namespace, so the qualifier is read and dropped:
    /// what is left is the name the definition is known by.

    pub(crate) fn skip_balanced(&mut self, open: &TokenKind, close: &TokenKind) {
        let mut depth = 0usize;
        loop {
            if self.at(&TokenKind::Eof) {
                return;
            }
            if self.at(open) {
                depth += 1;
            } else if self.at(close) {
                depth -= 1;
                if depth == 0 {
                    self.advance();
                    return;
                }
            }
            self.advance();
        }
    }

    /// One or more parameter lists.  ATS lets a function be written
    /// curried — `fun f (a: int) (b: int): int` — but the subset has no
    /// partial application, so consecutive lists are flattened into one.
    /// Call sites are flattened to match.

    pub(crate) fn skip_effect_annotation(&mut self) {
        if self.at(&TokenKind::Lt) {
            self.skip_balanced(&TokenKind::Lt, &TokenKind::Gt);
        }
        // `:<>` — the empty effect set, which the lexer reads as one
        // not-equal token.
        if self.at(&TokenKind::Ne) {
            self.advance();
        }
    }

    /// A sort's name.  `t@ype` arrives as three tokens because `@` is an
    /// operator elsewhere, so the pieces are rejoined here.

    pub(crate) fn skip_static_annotations(&mut self) {
        loop {
            match self.peek().kind {
                TokenKind::LBrace => self.skip_balanced(&TokenKind::LBrace, &TokenKind::RBrace),
                TokenKind::LBracket => {
                    self.skip_balanced(&TokenKind::LBracket, &TokenKind::RBracket)
                }
                // `#[n:nat]` — an existential type, read and dropped the
                // way its bracket-alone form is.
                TokenKind::Hash
                    if self
                        .tokens
                        .get(self.pos + 1)
                        .is_some_and(|t| t.kind == TokenKind::LBracket) =>
                {
                    self.advance(); // `#`
                    self.skip_balanced(&TokenKind::LBracket, &TokenKind::RBracket);
                }
                // `.<>.` — an empty metric.  The lexer reads `<>` as the
                // not-equal token, so this arrives as three tokens and
                // has to be matched on its own.
                TokenKind::Dot
                    if self
                        .tokens
                        .get(self.pos + 1)
                        .is_some_and(|t| t.kind == TokenKind::Ne) =>
                {
                    self.advance();
                    self.advance();
                    if self.at(&TokenKind::Dot) {
                        self.advance();
                    }
                }
                // `.<...>.` — a metric proving the recursion terminates.
                TokenKind::Dot
                    if self
                        .tokens
                        .get(self.pos + 1)
                        .is_some_and(|t| t.kind == TokenKind::Lt) =>
                {
                    while !self.at(&TokenKind::Eof) && !self.at(&TokenKind::Gt) {
                        self.advance();
                    }
                    self.advance(); // `>`
                    if self.at(&TokenKind::Dot) {
                        self.advance();
                    }
                }
                _ => return,
            }
        }
    }

    /// Read the `<...>` type arguments that select a template instance,
    /// if they are here.  `{...}` static arguments are skipped either
    /// way: they carry index terms, which no instance depends on.
    ///
    /// `f<>` — the "work it out" spelling — yields an empty list, which
    /// is still an instantiation and still distinct from no `<...>` at
    /// all.
    /// Read one `{...}` group as *static* terms, leaving the position
    /// where it found it.
    ///
    /// A brace group has two readings — `{int}` names a type,
    /// `{n}` names an index — and which one is meant depends on the
    /// callee's quantifiers, which the parser has no access to.  So both
    /// are recorded and the checker, which does know, takes the one it
    /// can use.  Reading only types is what made every proof application
    /// in the corpus indistinguishable from a template instantiation.

    pub(crate) fn read_static_group(&mut self, at: usize) -> Option<Vec<SExp>> {
        // `{n:int}` carries a sort, which makes it a *binder* — a
        // quantifier written where an argument could have been.  The
        // colon is the whole difference, and the expression parser reads
        // straight past it, so it has to be looked for before parsing
        // rather than noticed afterwards.
        let mut i = at + 1;
        let mut depth = 0usize;
        while let Some(t) = self.tokens.get(i) {
            match t.kind {
                TokenKind::LBrace | TokenKind::LParen | TokenKind::LBracket => depth += 1,
                TokenKind::RParen | TokenKind::RBracket => depth = depth.saturating_sub(1),
                TokenKind::RBrace if depth == 0 => break,
                TokenKind::RBrace => depth -= 1,
                TokenKind::Colon if depth == 0 => return None,
                TokenKind::Eof => return None,
                _ => {}
            }
            i += 1;
        }
        let save = self.pos;
        self.pos = at;
        self.advance(); // `{`
        let mut read = Vec::new();
        loop {
            let Ok(e) = self.parse_expr(0) else { break };
            match sexp_of_expr(&e) {
                Some(term) => read.push(term),
                None => break,
            }
            if self.at(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        // Only a group read *to its closing brace* is static arguments.
        // `{n:int}` is a binder, and stopping halfway through one would
        // hand the checker an argument the source never supplied.
        let whole = self.at(&TokenKind::RBrace);
        self.pos = save;
        whole.then_some(read)
    }


    pub(crate) fn looks_like_template_args(&self) -> bool {
        let mut i = self.pos + 1;
        // `f<>(x)` — the "infer it" spelling, and a common one.
        if self.tokens.get(i).is_some_and(|t| t.kind == TokenKind::Gt) {
            return true;
        }
        // An argument may be a whole type — `f<int,tup(bool,char)>` — so
        // the scan has to step over a balanced parenthesis run rather
        // than give up at the first `(`.  A `>` inside one closes
        // nothing: only a `>` at depth zero ends the list.
        let mut depth = 0usize;
        while let Some(t) = self.tokens.get(i) {
            match &t.kind {
                TokenKind::LParen | TokenKind::LBracket => {
                    depth += 1;
                    i += 1;
                }
                TokenKind::RParen | TokenKind::RBracket if depth > 0 => {
                    depth -= 1;
                    i += 1;
                }
                _ if depth > 0 => {
                    // Inside a type argument anything may appear except
                    // the tokens that could only end the expression.
                    if matches!(t.kind, TokenKind::Eof) {
                        return false;
                    }
                    i += 1;
                }
                TokenKind::Gt => {
                    return self.tokens.get(i + 1).is_none_or(|n| match &n.kind {
                        TokenKind::LParen
                        // Another group of template arguments:
                        // `f<a><b>(x)`, or `f<a><>(x)` where `<>` is one
                        // token.
                        | TokenKind::Lt
                        | TokenKind::Ne
                        // `f<int> '{ ... }` — an instance applied to a
                        // record, with the parentheses dropped.
                        | TokenKind::RecordOpen
                        | TokenKind::In
                        | TokenKind::End
                        | TokenKind::RParen
                        | TokenKind::RBrace
                        | TokenKind::Comma
                        | TokenKind::Semicolon
                        | TokenKind::Pipe
                        | TokenKind::Val
                        | TokenKind::Var
                        | TokenKind::Fun
                        | TokenKind::Fn
                        | TokenKind::Implement
                        | TokenKind::Eq
                        | TokenKind::Hash
                        | TokenKind::Eof => true,
                        // A word that begins a declaration cannot be the
                        // right operand of a comparison, so a `>` in front
                        // of one closed a type argument list.
                        TokenKind::Ident(w) => starts_a_declaration(w),
                        _ => false,
                    });
                }
                TokenKind::Ident(_) | TokenKind::Comma => i += 1,
                _ => return false,
            }
        }
        false
    }

    /// Consume a bracketed run, honoring nesting.

    pub(crate) fn at_borrow_marker(&self) -> bool {
        matches!(self.peek().kind, TokenKind::Amp | TokenKind::Bang)
    }

    /// Whether `name` is a type this parser knows: a built-in, a type
    /// variable in scope, or a type alias it has gathered.  A parameter
    /// entry that is nothing but such a name is a bare type with no name,
    /// as a signature is allowed to write.

    pub(crate) fn is_known_type_name(&self, name: &str) -> bool {
        indexed_base(name).is_some()
            || crate::prelude::canonical_type(name).is_some()
            || self.type_vars.iter().any(|t| t == name)
            || self.typedefs.contains_key(name)
            || self.typedef_families.contains_key(name)
            || self.datatypes.contains(name)
    }


    pub(crate) fn eat_arrow(&mut self) -> bool {
        if self.at(&TokenKind::Arrow) {
            self.advance();
            return true;
        }
        let Some(next) = self.tokens.get(self.pos + 1).map(|t| t.kind.clone()) else {
            return false;
        };
        if !self.at(&TokenKind::Minus) {
            return false;
        }
        match next {
            TokenKind::Lt => {
                self.advance();
                self.skip_balanced(&TokenKind::Lt, &TokenKind::Gt);
                true
            }
            // `-<>` — no effects at all, which the lexer reads as one
            // not-equal token.
            TokenKind::Ne => {
                self.advance();
                self.advance();
                true
            }
            _ => false,
        }
    }

    /// Complete `name` or `name(args)` with an optional right-nested
    /// `-> ret` arrow.

    pub(crate) fn starts_a_type(&self) -> bool {
        matches!(
            self.peek().kind,
            TokenKind::Ident(_)
                | TokenKind::LParen
                | TokenKind::At
                | TokenKind::Amp
                | TokenKind::Bang
        )
    }


    pub(crate) fn is_string_binding(&self) -> bool {
        self.at(&TokenKind::Eq)
            && matches!(
                self.tokens.get(self.pos + 1).map(|t| &t.kind),
                Some(TokenKind::StrLit(_))
            )
    }


    pub(crate) fn at_external_binding(&self) -> bool {
        if !self.at(&TokenKind::Eq) {
            return false;
        }
        match self.tokens.get(self.pos + 1).map(|t| &t.kind) {
            Some(TokenKind::StrLit(s)) => {
                s.starts_with("mac#") || s.starts_with("sta#") || s.starts_with("ext#")
            }
            _ => false,
        }
    }

    /// Finish a `fun` read as a *declaration*: the signature is complete
    /// and there is no body.  An `= "..."` external binding is dropped
    /// and the signature kept, exactly as `extern fun`'s is.

    pub(crate) fn at_proof_keyword(&self) -> bool {
        matches!(
            &self.peek().kind,
            TokenKind::Ident(w) if w == "praxi" || w == "prfun" || w == "prfn"
        )
    }

    /// Whether the next token begins a function *definition* — one of the
    /// spellings ATS uses for a name with a body.  `fnx` is the
    /// named-recursive form; the proof spellings are recognised too, and
    /// `parse_fun_def` knows how to mark them.

    pub(crate) fn at_fun_def_keyword(&self) -> bool {
        matches!(self.peek().kind, TokenKind::Fun | TokenKind::Fn)
            || matches!(
                &self.peek().kind,
                TokenKind::Ident(w) if w == "fnx" || w == "prfn" || w == "prfun"
            )
    }

}
