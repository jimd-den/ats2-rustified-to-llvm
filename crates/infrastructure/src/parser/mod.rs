use ats2_domain::ast::{
    BinOp, ConstDef, Ctor, DatatypeDef, Def, Expr, FunDecl, FunDef, ImplementDef, Include, LetBind,
    Param, Pattern, Program, Staload, Ty, ValDef,
};
use ats2_domain::errors::CompileError;
use ats2_domain::statics::{Quant, SExp, Sort};
use std::collections::{HashMap, HashSet};

use ats2_domain::tokens::{Pos, Span, Token, TokenKind};

use crate::lexer::Lexer;

/// A stateless parser: `parse` turns source text straight into a program.
pub struct Parser;

impl Parser {
    /// Lex and parse `source`.  Returns the program or the first error
    /// encountered (fail-fast; collecting *all* parse errors is a later
    /// iteration).
    pub fn parse(source: &str) -> Result<Program, Vec<CompileError>> {
        let tokens = Lexer::lex(source)?;
        Self::parse_tokens(&tokens)
    }

    /// Parse a dependency while retaining complete declarations before the
    /// first unsupported top-level form.  Lexing remains strict because no
    /// trustworthy token prefix exists when tokenization itself fails.
    pub fn parse_dependency(source: &str) -> Result<Program, Vec<CompileError>> {
        let tokens = Lexer::lex(source)?;
        Self::parse_dependency_tokens(&tokens)
    }

    /// Parse a token stream (e.g. one produced by the lexer in tests).
    pub fn parse_tokens(tokens: &[Token]) -> Result<Program, Vec<CompileError>> {
        if tokens.is_empty() {
            let span = Span::new(Pos::new(1, 1, 0), Pos::new(1, 1, 0));
            return Err(vec![CompileError::parse(
                span,
                "empty token stream (missing EOF)",
            )]);
        }
        let mut ctx = ParseCtx::new(tokens);
        ctx.parse_program()
    }

    fn parse_dependency_tokens(tokens: &[Token]) -> Result<Program, Vec<CompileError>> {
        if tokens.is_empty() {
            let span = Span::new(Pos::new(1, 1, 0), Pos::new(1, 1, 0));
            return Err(vec![CompileError::parse(
                span,
                "empty token stream (missing EOF)",
            )]);
        }
        Ok(ParseCtx::new(tokens).parse_available_program())
    }
}

/// The top-level forms the subset knowingly ignores.
///
/// Each of them speaks to a part of ATS this compiler does not implement —
/// the module system (`staload`, `dynload`), the static language
/// (`stadef`, `sortdef`, `praxi`), the type checker (`typedef`, `assume`,
/// `overload`), or foreign declarations (`extern`).  Skipping them is what
/// lets a real ATS source file reach the parts we *do* implement.
fn is_skippable_directive(word: &str) -> bool {
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

fn load_kind(path: &str, dynamic: bool, anonymous: bool) -> ats2_domain::ast::LoadKind {
    if dynamic {
        ats2_domain::ast::LoadKind::Dynamic
    } else if anonymous || !path.ends_with(".sats") {
        ats2_domain::ast::LoadKind::Implementation
    } else {
        ats2_domain::ast::LoadKind::Interface
    }
}

/// Whether a name is a variance annotation rather than a type former.
fn is_variance_annotation(name: &str) -> bool {
    matches!(name, "INV" | "OUT" | "INVAR")
}

/// Whether a bare word can begin a top-level declaration.
///
/// Most declaration keywords are lexed as keywords, but a few — `extern`,
/// `and`, `where` — stay ordinary identifiers, and those are the ones a
/// type could otherwise absorb as a static index.
fn starts_a_declaration(word: &str) -> bool {
    is_skippable_directive(word)
        || is_abstract_atype_prefix(word)
        || matches!(word, "and" | "where")
}

/// Whether `word` is the prefix of an abstract-type form written with an
/// `@`, like `abst@ype`, `absvt@ype`, `absviewt@ype`.  The lexer cuts the
/// `@` out, so the prefix arrives alone and has to be recognised for what
/// it begins.
fn is_abstract_atype_prefix(word: &str) -> bool {
    matches!(word, "abst" | "absvt" | "absviewt")
}

/// One `val`/`var` binding: a plain name, or a pattern the source
/// insists must match.
enum BindKind {
    Simple(LetBind),
    Pattern(Pattern, Expr),
}

/// `val pat = e` — the match the source insists must succeed.  A
/// non-match leaves through `exit`, because the pattern having failed
/// means the program's own guarantee about its data is broken.
fn must_match(value: Expr, pattern: Pattern, rest: Expr) -> Expr {
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
fn splice_macro_args(expr: &Expr, params: &[String], args: &[Expr]) -> Expr {
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
fn indexed_base(name: &str) -> Option<&'static str> {
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

fn is_index_sort(sort: &str) -> bool {
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
fn sexp_of_expr(e: &Expr) -> Option<SExp> {
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
fn is_relation(e: &SExp) -> bool {
    matches!(
        e,
        SExp::App(op, args)
            if args.len() == 2
                && matches!(op.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||")
    )
}

/// The static language's spelling of a shared operator.
fn static_op(op: BinOp) -> Option<&'static str> {
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
fn well_known_param_type(name: &str) -> Option<Ty> {
    match name {
        "argc" => Some(Ty::Name("int".into())),
        "argv" => Some(Ty::Name("argv".into())),
        _ => None,
    }
}

/// The value an uninitialized `var` of this type starts from.
fn zero_of(ty: &Ty) -> Option<Expr> {
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
fn substitute_type(ty: &Ty, subst: &HashMap<String, Ty>) -> Ty {
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
fn wrap_funs(funs: Vec<FunDef>, body: Expr) -> Expr {
    if funs.is_empty() {
        body
    } else {
        Expr::LetFun(funs, Box::new(body))
    }
}

/// A fallback token used when the cursor runs past the end of a hand-made
/// stream (the lexer always terminates with `Eof`, so this is a guard).
const EOF_TOKEN: Token = Token {
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
struct ParseCtx<'a> {
    tokens: &'a [Token],
    pos: usize,
    /// `macdef` aliases in force: a name standing for an expression.
    ///
    /// A macro is *lexical* — it means whatever it meant where it was
    /// written — so expansion happens here, as the name is read, rather
    /// than in a later pass that would have to carry the scope along.
    macros: HashMap<String, Expr>,
    /// `typedef T = int` — a name for a type.
    ///
    /// Expanded as the name is read, for the same reason macros are: an
    /// alias means whatever it meant where it was written, and expanding
    /// here spares every later stage an alias table it would have to
    /// thread through.
    typedefs: HashMap<String, Ty>,
    /// Declarations found inside a body that belong to the program as a
    /// whole, such as an `overload` written in a `let`.
    pending: Vec<Def>,
    /// Every `staload` the file wrote, in source order.  They name the
    /// other units this one needs, and answering them is somebody
    /// else's job — the parser reads one file and has no filesystem.
    staloads: Vec<Staload>,
    /// Every `#include` this file wrote, in source order.
    includes: Vec<Include>,
    /// A counter for names the parser invents, so a desugaring can bind
    /// a temporary without any chance of shadowing the source's own.
    gensym: usize,
    /// `typedef pair (a:t@ype) = '{ ... }` — an alias taking arguments.
    ///
    /// Kept apart from `typedefs` because expanding one is a
    /// substitution rather than a lookup, and the arguments are only
    /// known at the use site.
    typedef_families: HashMap<String, (Vec<String>, Ty)>,
    /// The propositions a `dataprop` or `dataview` has declared.
    ///
    /// `FACT(0, 1)` and `list(int)` are the same shape on the page, and
    /// nothing but the declaration tells them apart.  Without it a
    /// proposition's arguments are read as *types* — and `0` is not one,
    /// so the indices the proof is about are dropped and every
    /// proposition collapses to the bare name `FACT`, which every
    /// derivation proves equally well.
    props: HashSet<String>,
    /// Runtime datatype names declared in this unit.
    ///
    /// A signature may write `(tree, int)` with types alone and no parameter
    /// names, so datatype declarations participate in the same name lookup as
    /// aliases and built-ins.
    datatypes: HashSet<String>,
    /// `#define cons stream_vt_cons` — one name standing for another.
    ///
    /// Distinct from `macros`, which maps a name to an *expression*: a
    /// rename also has to reach patterns, where an expression cannot go.
    /// A program working in a list-like type other than the prelude's
    /// points the short names at its own constructors this way, and the
    /// rename must hold on both sides of a `case` or the two halves
    /// disagree about what was built.
    renames: HashMap<String, String>,
    /// The constructor `::` stands for.  `cons` by default; a program
    /// that works in another list-like type says so with
    /// `#define :: stream_vt_cons`, and from there on the operator means
    /// that constructor instead.
    cons_name: String,
    /// The type variables in scope: a template's `{a:t@ype}` or a
    /// datatype's `(a)`.
    ///
    /// Their one job is to settle juxtaposition.  `bintree a` applies
    /// `bintree` to `a` because `a` is a type; `int n` indexes `int`
    /// because `n` is not.  Nothing in the syntax distinguishes the two —
    /// ATS writes types and indices in one static language — so the
    /// scope the name was declared in is the only witness there is.
    type_vars: Vec<String>,
    /// `macdef name (p1, p2) = body` — a macro with parameters.  The
    /// body is stored unexpanded with its parameters as ordinary
    /// variables, and expanded at the use site by splicing each argument
    /// in for the parameter it answers — the lexical semantics ATS's own
    /// macro expander gives it.
    macro_funs: HashMap<String, (Vec<String>, Expr)>,
    /// How many macro bodies are being read right now.  The splice comma
    /// — `f ,(x)` — is an argument *inside* a macro body and a separator
    /// everywhere else, and nothing in the tokens themselves tells the
    /// two apart.
    macro_depth: usize,
}

impl<'a> ParseCtx<'a> {
    fn new(tokens: &'a [Token]) -> Self {
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

    fn peek(&self) -> &Token {
        self.tokens.get(self.pos).unwrap_or(&EOF_TOKEN)
    }

    fn at_ident(&self, word: &str) -> bool {
        matches!(&self.peek().kind, TokenKind::Ident(w) if w == word)
    }

    fn at(&self, kind: &TokenKind) -> bool {
        self.peek().kind == *kind
    }

    fn advance(&mut self) {
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
    }

    fn expect(&mut self, kind: &TokenKind, what: &str) -> Result<(), CompileError> {
        if self.at(kind) {
            self.advance();
            Ok(())
        } else {
            Err(self.error_here(what))
        }
    }

    fn expect_ident(&mut self, what: &str) -> Result<String, CompileError> {
        match self.peek().kind.clone() {
            TokenKind::Ident(name) => {
                self.advance();
                Ok(name)
            }
            _ => Err(self.error_here(what)),
        }
    }

    fn error_here(&self, message: impl Into<String>) -> CompileError {
        CompileError::parse(self.peek().span, message)
    }

    // --- program level ---------------------------------------------

    fn parse_program(&mut self) -> Result<Program, Vec<CompileError>> {
        self.precollect_type_aliases();
        let mut defs = Vec::new();
        while !self.at(&TokenKind::Eof) {
            self.parse_toplevel(&mut defs).map_err(|e| vec![e])?;
        }
        Ok(self.finish_program(defs))
    }

    fn parse_available_program(&mut self) -> Program {
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
    fn recover_after_toplevel_error(&mut self, failed_at: usize) {
        let failed_line = self.tokens[failed_at].span.start.line;
        self.pos = (failed_at + 1..self.tokens.len())
            .find(|&i| {
                let start = self.tokens[i].span.start;
                start.line > failed_line && start.column == 1
            })
            .unwrap_or(self.tokens.len() - 1);
    }

    fn finish_program(&mut self, mut defs: Vec<Def>) -> Program {
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
    fn precollect_type_aliases(&mut self) {
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
    fn parse_toplevel(&mut self, out: &mut Vec<Def>) -> Result<(), CompileError> {
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
            // only place that can.
            TokenKind::Ident(w) if w == "datavtype" => {
                self.advance(); // `datavtype`
                                // `datavtype` — a datatype whose values are *resources*.
                out.push(self.parse_datatype_body(true)?);
                Ok(())
            }
            TokenKind::Val => {
                self.advance(); // `val`
                                // `val rec a = ... and b = ...` — a chain of bindings
                                // that may mention each other, which is how mutually
                                // recursive lazy values are written.  The recursion is
                                // in the *values*: each initializer runs in source
                                // order, and one that only *mentions* its siblings (as
                                // a `$delay` body does) needs nothing from them yet.
                let rec_form = matches!(&self.peek().kind, TokenKind::Ident(w) if w == "rec");
                if rec_form {
                    self.advance(); // `rec`
                }
                loop {
                    match self.parse_val_bind(false)? {
                        BindKind::Simple(bind) => {
                            // `val () = println! (...)` — a top-level
                            // *statement*.  It binds nothing, but it is
                            // the whole point of the line, so it is kept
                            // under a name no source can write and run
                            // for its effect alone.
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
                        // A pattern at the top level has no remainder to
                        // scope over, so it cannot be lowered here.
                        BindKind::Pattern(..) => {
                            return Err(self.error_here(
                                "a pattern binding is not supported at the top level",
                            ));
                        }
                    }
                    if rec_form && matches!(&self.peek().kind, TokenKind::Ident(w) if w == "and") {
                        self.advance(); // `and`
                    } else {
                        break;
                    }
                }
                Ok(())
            }
            // `var x: int = 0` outside any body — "statically
            // allocated", in ATS's words.
            //
            // A top-level `var` differs from a top-level `val` in
            // exactly one way: its storage has an address that outlives
            // every call, and code takes that address (`addr@ x`) and
            // writes through it.  A one-cell reference *is* that, so the
            // declaration becomes one, and `addr@` then has something
            // to return.
            TokenKind::Var => {
                self.advance(); // `var`
                let BindKind::Simple(bind) = self.parse_val_bind(true)? else {
                    return Err(
                        self.error_here("a pattern binding is not supported at the top level")
                    );
                };
                if let Some(name) = bind.name {
                    let value = Expr::Call(Box::new(Expr::Var("ref".into())), vec![bind.value]);
                    // An annotated `var x: int = e` is a `ref(int)`, so the
                    // annotation survives the rewrite instead of being
                    // thrown away and rediscovered from the initializer.
                    let ty = bind.ty.map(|t| Ty::App("ref".into(), vec![t]));
                    out.push(Def::Val(ValDef { name, ty, value }));
                }
                Ok(())
            }
            // `extern fun f (...): t` states a signature the definition
            // will fill in later.  Foreign declarations carry syntax the
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
            TokenKind::Ident(name) if name == "staload" || name == "dynload" => {
                if let Some(s) = self.read_staload(name == "dynload") {
                    self.staloads.push(s);
                }
                self.skip_directive();
                Ok(())
            }
            // `exception X of (t1, t2)` — a constructor of the built-in
            // `exn` type.  It is not skipped like the other static
            // declarations: a program that raises and catches needs to
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
    fn parse_local(&mut self, out: &mut Vec<Def>) -> Result<(), CompileError> {
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
    fn parse_hash_directive(&mut self, out: &mut Vec<Def>) -> Result<(), CompileError> {
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
    fn read_staload(&self, dynamic: bool) -> Option<Staload> {
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
    fn read_staload_after_keyword(&self, dynamic: bool) -> Option<Staload> {
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
    fn nth(&self, n: usize) -> Option<&TokenKind> {
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
    fn skip_directive(&mut self) {
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

    fn parse_def(&mut self) -> Result<Def, CompileError> {
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

    fn parse_datatype_def(&mut self) -> Result<Def, CompileError> {
        self.advance(); // `datatype`
        self.parse_datatype_body(false)
    }

    /// Everything after the `datatype`/`datavtype` keyword.  The type
    /// parameters stay in scope while the constructors are read, so a
    /// field written `bintree a` applies the datatype to `a`.
    fn parse_datatype_body(&mut self, linear: bool) -> Result<Def, CompileError> {
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
    fn push_type_vars(&mut self, names: &[String]) -> usize {
        let depth = self.type_vars.len();
        self.type_vars.extend(names.iter().cloned());
        depth
    }

    fn pop_type_vars(&mut self, depth: usize) {
        self.type_vars.truncate(depth);
    }

    /// `(a, b)` or `(a:t@ype)` after a datatype name — optional.
    ///
    /// As with a template's parameters, only the names matter: the sort on
    /// the right of the colon constrains what may be substituted, which is
    /// a question for a type checker this compiler does not have.
    fn parse_optional_type_params(&mut self) -> Result<(Vec<String>, usize), CompileError> {
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
    fn parse_ctor(
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
    fn parse_ctor_result(
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
    fn parse_ctor_fields(
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
    fn starts_a_type(&self) -> bool {
        matches!(
            self.peek().kind,
            TokenKind::Ident(_)
                | TokenKind::LParen
                | TokenKind::At
                | TokenKind::Amp
                | TokenKind::Bang
        )
    }

    fn parse_fun_def(&mut self) -> Result<Def, CompileError> {
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
    fn is_string_binding(&self) -> bool {
        self.at(&TokenKind::Eq)
            && matches!(
                self.tokens.get(self.pos + 1).map(|t| &t.kind),
                Some(TokenKind::StrLit(_))
            )
    }

    fn at_external_binding(&self) -> bool {
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
    fn finish_fun_decl(
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
    fn parse_dataprop(&mut self, linear: bool) -> Option<Vec<FunDecl>> {
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
    fn parse_constructor_fields(&mut self) -> Option<Vec<Ty>> {
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
    fn at_proof_keyword(&self) -> bool {
        matches!(
            &self.peek().kind,
            TokenKind::Ident(w) if w == "praxi" || w == "prfun" || w == "prfn"
        )
    }

    /// Whether the next token begins a function *definition* — one of the
    /// spellings ATS uses for a name with a body.  `fnx` is the
    /// named-recursive form; the proof spellings are recognised too, and
    /// `parse_fun_def` knows how to mark them.
    fn at_fun_def_keyword(&self) -> bool {
        matches!(self.peek().kind, TokenKind::Fun | TokenKind::Fn)
            || matches!(
                &self.peek().kind,
                TokenKind::Ident(w) if w == "fnx" || w == "prfn" || w == "prfun"
            )
    }

    fn parse_extern_decl(&mut self) -> Result<FunDecl, CompileError> {
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
    fn parse_extern_val_decl(&mut self) -> Result<FunDecl, CompileError> {
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
    fn split_curried(ty: Ty) -> (Vec<Param>, Ty) {
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

    fn parse_implement_def(&mut self) -> Result<Def, CompileError> {
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
    fn directive_ends_after_one_token(&self) -> bool {
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
    fn parse_qualified_ident(&mut self, what: &str) -> Result<String, CompileError> {
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
    fn parse_instance_arguments(&mut self) -> Result<Vec<Ty>, CompileError> {
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
    fn parse_template_params(&mut self) -> Vec<String> {
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
    fn parse_quantifiers(&mut self) -> Vec<Quant> {
        self.parse_quantifiers_and_metric().0
    }

    /// The same, keeping the `.<n>.` metric that may sit among them.
    ///
    /// Quantifier and metric interleave in real signatures — `{n:nat}
    /// .<n>.` and `.<n>. {n:nat}` are both written — so one routine reads
    /// the run rather than two taking turns and each stopping at the
    /// other.
    fn parse_quantifiers_and_metric(&mut self) -> (Vec<Quant>, Vec<SExp>) {
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
    fn parse_metric(&mut self) -> Option<Vec<SExp>> {
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
    fn parse_one_quantifier(&mut self, close: &TokenKind) -> Option<Quant> {
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
    fn parse_binder_group(&mut self, close: &TokenKind) -> Option<Quant> {
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
    fn skip_effect_annotation(&mut self) {
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
    fn parse_sort_name(&mut self) -> Option<String> {
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
    fn parse_existentials(&mut self) -> Vec<Quant> {
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

    fn skip_static_annotations(&mut self) {
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
    fn read_static_group(&mut self, at: usize) -> Option<Vec<SExp>> {
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

    fn parse_template_arguments(&mut self) -> Result<Option<Vec<Ty>>, CompileError> {
        Ok(self.parse_instantiation()?.0)
    }

    /// The same, keeping the *static* reading of the brace groups.
    ///
    /// Returned rather than stashed on the cursor because reading a
    /// static term parses an expression, which re-enters this routine —
    /// and shared state does not survive its own recursion.
    fn parse_instantiation(&mut self) -> Result<(Option<Vec<Ty>>, Vec<SExp>), CompileError> {
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
    fn skip_template_arguments(&mut self) {
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
    fn looks_like_template_args(&self) -> bool {
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
    fn skip_balanced(&mut self, open: &TokenKind, close: &TokenKind) {
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
    fn parse_params(&mut self) -> Result<Vec<Param>, CompileError> {
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
    fn parse_params_maybe_untyped(
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
    fn parse_params_with_unknown_bare_types(
        &mut self,
    ) -> Result<(Vec<Param>, Vec<String>), CompileError> {
        self.parse_params_with_policy(false, true)
    }

    fn parse_params_with_policy(
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
    fn at_borrow_marker(&self) -> bool {
        matches!(self.peek().kind, TokenKind::Amp | TokenKind::Bang)
    }

    /// Whether `name` is a type this parser knows: a built-in, a type
    /// variable in scope, or a type alias it has gathered.  A parameter
    /// entry that is nothing but such a name is a bare type with no name,
    /// as a signature is allowed to write.
    fn is_known_type_name(&self, name: &str) -> bool {
        indexed_base(name).is_some()
            || crate::prelude::canonical_type(name).is_some()
            || self.type_vars.iter().any(|t| t == name)
            || self.typedefs.contains_key(name)
            || self.typedef_families.contains_key(name)
            || self.datatypes.contains(name)
    }

    fn parse_one_param_list(
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
                // list one shape for everything downstream.
                let named = matches!(self.peek().kind, TokenKind::Ident(_))
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
                let mut name = self.expect_ident("expected a parameter name")?;
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
    fn parse_type(&mut self) -> Result<Ty, CompileError> {
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
    fn parse_named_type(&mut self) -> Result<Ty, CompileError> {
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
    fn apply_type_head(&self, name: String, args: Vec<Ty>) -> Ty {
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
    fn parse_type_argument(&mut self) -> Result<Option<Ty>, CompileError> {
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
    fn skip_type_argument(&mut self) {
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
    fn parse_paren_type(&mut self) -> Result<Ty, CompileError> {
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
    fn parse_index_terms(&mut self) -> Vec<SExp> {
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
    fn eat_arrow(&mut self) -> bool {
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
    fn finish_arrow_type(&mut self, atom: Ty) -> Result<Ty, CompileError> {
        if self.eat_arrow() {
            let ret = self.parse_type()?;
            Ok(Ty::Fun(vec![atom], Box::new(ret)))
        } else {
            Ok(atom)
        }
    }

    // --- expressions -----------------------------------------------

    /// Precedence-climbing expression parser.
    fn parse_expr(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
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
            // A pattern binding inside a `where` has no following body of
            // its own to scope over; the clause is not one this subset
            // needs, so the pattern is refused rather than guessed at.
            if pending.is_some() {
                return Err(
                    self.error_here("a pattern binding is not supported inside a `where` clause")
                );
            }
            lhs = wrap_funs(funs, inner);
        }
        Ok(lhs)
    }

    /// The operator of a compound assignment (`:=+`, `:=-`, `:=*`,
    /// `:=/`), if the cursor is sitting on one.
    fn compound_assign_op(&self) -> Option<BinOp> {
        match self.peek().kind {
            TokenKind::Plus => Some(BinOp::Add),
            TokenKind::Minus => Some(BinOp::Sub),
            TokenKind::Star => Some(BinOp::Mul),
            TokenKind::Slash => Some(BinOp::Div),
            _ => None,
        }
    }

    /// A prefix expression plus any chained call applications.
    fn parse_prefix(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
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
                // `A.[i]` — ATS's array subscript.  The dot is what tells
                // it apart from `xs[i]`, which indexes `argv`.
                self.advance();
                self.advance();
                let index = self.parse_expr(0)?;
                self.expect(&TokenKind::RBracket, "expected `]` after the index")?;
                expr = Expr::Index(Box::new(expr), Box::new(index));
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
                let index = self.parse_expr(0)?;
                self.expect(&TokenKind::RBracket, "expected `]` after the index")?;
                expr = Expr::Index(Box::new(expr), Box::new(index));
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
    fn starts_a_juxtaposed_argument(&self) -> bool {
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

    fn parse_primary(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
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

    fn parse_if(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
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

    fn parse_let(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
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
    fn parse_let_rest(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
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
    fn parse_block(&mut self, _min_bp: u8) -> Result<Expr, CompileError> {
        self.advance(); // `{`
        self.parse_block_rest()
    }

    /// As `parse_let_rest`, for a brace block: the terminator is `}`
    /// and the body needs no `in`.
    fn parse_block_rest(&mut self) -> Result<Expr, CompileError> {
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
    fn parse_local_decls_and_funs(
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

    fn parse_local_decl_run(
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
    fn parse_val_bind(&mut self, mutable: bool) -> Result<BindKind, CompileError> {
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
    fn finish_let_bind(
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
        })
    }

    /// `typedef T = t` — record the alias, and report whether it was one
    /// this parser understands.
    ///
    /// The parameterized form (`typedef m (a:t@ype) = ...`) and record
    /// types are not modelled, so a `typedef` that does not fit is left
    /// to the directive skipper rather than half-recorded.
    fn parse_typedef(&mut self) -> bool {
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
    fn parse_where_type_alias(&mut self) -> Result<(), CompileError> {
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
    fn parse_abstract_opaque(&mut self) -> bool {
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
    fn parse_typedef_body(&mut self) -> bool {
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
    fn at_at_joined_abstract(&self) -> bool {
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
    fn parse_at_joined_abstract(&mut self) -> bool {
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
    fn parse_macdef(&mut self) {
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
    fn parse_exception(&mut self) -> Vec<Def> {
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

    fn parse_overload(&mut self) -> Option<Def> {
        let save = self.pos;
        self.advance(); // `overload`
        let op = match self.peek().kind.clone() {
            TokenKind::Star => "*",
            TokenKind::Slash => "/",
            TokenKind::Plus => "+",
            TokenKind::Minus => "-",
            TokenKind::Lt => "<",
            TokenKind::Gt => ">",
            TokenKind::Le => "<=",
            TokenKind::Ge => ">=",
            TokenKind::Eq => "=",
            TokenKind::Ne => "<>",
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

    /// `prval pf = e`, `prval () = e`, `prval EQINT() = e` — a proof
    /// binding.
    ///
    /// Only the *name* on the left is read, and only when it is a plain
    /// one: a proof pattern destructures a proof, and this compiler
    /// tracks no proof values to destructure.  The expression on the
    /// right is what matters — it is the application of an axiom, and
    /// its result type is the claim that comes into scope.
    fn parse_proof_binding(&mut self) -> Option<LetBind> {
        let save = self.pos;
        self.advance(); // `prval` / `prvar`
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
                // — is stepped over to reach the `=`.
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
    fn skip_local_directive(&mut self) {
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
    fn parse_try(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
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
    fn parse_raise(&mut self) -> Result<Expr, CompileError> {
        self.advance(); // `$raise`
        let value = self.parse_expr(UNARY_BP)?;
        Ok(Expr::Raise(Box::new(value)))
    }

    fn parse_case(&mut self) -> Result<Expr, CompileError> {
        self.advance(); // `case` (the `+`/`-` marker is part of the keyword)
        let scrutinee = self.parse_expr(0)?;
        self.expect(&TokenKind::Of, "expected `of` after the scrutinee")?;
        if self.at(&TokenKind::Pipe) {
            self.advance();
        }
        let mut arms = Vec::new();
        loop {
            let pattern = self.parse_pattern()?;
            // `| p when guard => e` — a guard we cannot evaluate yet.
            if self.at(&TokenKind::When) {
                return Err(self.error_here("pattern guards (`when`) are not supported yet"));
            }
            self.expect(&TokenKind::FatArrow, "expected `=>` after the pattern")?;
            let body = self.parse_expr(0)?;
            arms.push((pattern, body));
            if self.at(&TokenKind::Pipe) {
                self.advance();
            } else {
                break;
            }
        }
        Ok(Expr::Case(Box::new(scrutinee), arms))
    }

    /// One pattern, including any infix `::` that follows it.
    ///
    /// Cons is right-associative — `x :: y :: rest` peels one element at
    /// a time — so the tail is parsed by recursing rather than by
    /// looping.
    fn parse_pattern(&mut self) -> Result<Pattern, CompileError> {
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
    fn starts_a_juxtaposed_pattern(&self) -> bool {
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
    fn parse_pattern_primary(&mut self) -> Result<Pattern, CompileError> {
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
                // comma loop and the bar are read together and whatever
                // preceded a bar is dropped.
                let mut items = Vec::new();
                loop {
                    items.push(self.parse_pattern()?);
                    if self.at(&TokenKind::Comma) {
                        self.advance();
                        continue;
                    }
                    if self.at(&TokenKind::Pipe) {
                        self.advance();
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

    /// `while (cond) body`.
    fn parse_while(&mut self) -> Result<Expr, CompileError> {
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
    fn parse_for(&mut self) -> Result<Expr, CompileError> {
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
    fn parse_lam(&mut self) -> Result<Expr, CompileError> {
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
    fn current_binop(&self) -> Option<(BinOp, u8, u8)> {
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
fn sequence(items: Vec<Expr>) -> Expr {
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

/// Unary operators bind tighter than every binary operator (10 > 9).
const UNARY_BP: u8 = 10;

/// `::` binds tighter than the comparisons but looser than arithmetic,
/// which is what ATS's own fixity declaration says.  It is
/// right-associative, so the same power is used on both sides.
const CONS_BP: u8 = 6;

/// Decode a raw string interior into its semantic value.  The lexer kept
/// the escapes verbatim; this is where `\n` becomes a real newline.
fn decode_string(raw: &str, span: Span) -> Result<String, CompileError> {
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
            'n' => out.push('\n'),
            't' => out.push('\t'),
            'r' => out.push('\r'),
            '0' => out.push('\0'),
            '\\' => out.push('\\'),
            '"' => out.push('"'),
            '\'' => out.push('\''),
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

#[cfg(test)]

#[cfg(test)]
mod tests;
