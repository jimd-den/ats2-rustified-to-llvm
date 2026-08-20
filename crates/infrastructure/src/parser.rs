use ats2_domain::statics::{Quant, SExp, Sort};
use ats2_domain::ast::{BinOp, ConstDef, Ctor, DatatypeDef, Def, Expr, FunDecl, FunDef, ImplementDef, LetBind, Param, Pattern, Program, Ty, ValDef};
use ats2_domain::errors::CompileError;
use std::collections::HashMap;

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

    /// Parse a token stream (e.g. one produced by the lexer in tests).
    pub fn parse_tokens(tokens: &[Token]) -> Result<Program, Vec<CompileError>> {
        if tokens.is_empty() {
            let span = Span::new(Pos::new(1, 1, 0), Pos::new(1, 1, 0));
            return Err(vec![CompileError::parse(span, "empty token stream (missing EOF)")]);
        }
        let mut ctx =
            ParseCtx { tokens, pos: 0, macros: HashMap::new(), typedefs: HashMap::new(), pending: Vec::new(), gensym: 0, type_vars: Vec::new(), macro_funs: HashMap::new(), macro_depth: 0, cons_name: "cons".into(), renames: HashMap::new(), typedef_families: HashMap::new() };
        ctx.parse_program()
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
        "staload" | "dynload" | "typedef" | "abstype" | "absvtype" | "abst0ype"
            | "abstbox" | "abstflat" | "sortdef" | "stadef" | "stacst" | "assume"
            | "overload" | "macdef" | "extern" | "static" | "praxi" | "prfun" | "prval"
            | "dataprop" | "dataview" | "datasort" | "propdef"
            | "viewdef" | "vtypedef" | "symintr" | "infix" | "infixl" | "infixr"
            | "prefix" | "postfix" | "nonfix" | "classdec" | "exception"
    )
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
    is_skippable_directive(word) || matches!(word, "and" | "where")
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
    Expr::Case(Box::new(value), vec![(pattern, rest), (Pattern::Wildcard, exit)])
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
        E::Wildcard | E::Unit | E::Uninit | E::IntLit(_) | E::CharLit(_) | E::FloatLit(_)
        | E::BoolLit(_) | E::StrLit(_) | E::Inst(..) => expr.clone(),
        E::UnaryNeg(e) => E::UnaryNeg(Box::new(sub(e))),
        E::BinOp(op, l, r) => E::BinOp(*op, Box::new(sub(l)), Box::new(sub(r))),
        E::TupleLit(items) => E::TupleLit(items.iter().map(sub).collect()),
        E::Call(c, items) => E::Call(Box::new(sub(c)), items.iter().map(sub).collect()),
        E::Index(b, i) => E::Index(Box::new(sub(b)), Box::new(sub(i))),
        E::Store(p, v) => E::Store(Box::new(sub(p)), Box::new(sub(v))),
        E::Deref(e) => E::Deref(Box::new(sub(e))),
        E::Proj(e, i) => E::Proj(Box::new(sub(e)), *i),
        E::IfThenElse(c, t, e) => E::IfThenElse(Box::new(sub(c)), Box::new(sub(t)), Box::new(sub(e))),
        E::Let(binds, body) => E::Let(
            binds
                .iter()
                .map(|b| LetBind { value: sub(&b.value), ..b.clone() })
                .collect(),
            Box::new(sub(body)),
        ),
        E::Lam(ps, r, b) => E::Lam(ps.clone(), r.clone(), Box::new(sub(b))),
        E::Field(b, n) => E::Field(Box::new(sub(b)), n.clone()),
        E::RecordLit(fields) => {
            E::RecordLit(fields.iter().map(|(n, v)| (n.clone(), sub(v))).collect())
        }
        E::LetFun(funs, body) => E::LetFun(
            funs.iter().map(|f| FunDef { body: sub(&f.body), ..f.clone() }).collect(),
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
    Some(match name {
        "int" | "intGt" | "intGte" | "intLt" | "intLte" | "intBtw" | "intBtwe" | "nat"
        | "natLt" | "natLte" | "natGt" | "natGte" | "pos" | "Nat" | "Pos" => "int",
        "uint" | "uintGt" | "uintGte" | "uintLt" | "uintLte" | "size_t" | "ssize_t"
        | "sizeGt" | "sizeGte" | "sizeLt" | "sizeLte" | "sizeBtw" | "sizeBtwe" => "int",
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
    matches!(sort, "int" | "nat" | "pos" | "bool" | "addr" | "eff" | "cls" | "sta" | "size")
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
        Expr::BinOp(op, l, r) => {
            SExp::App(static_op(*op)?.into(), vec![sexp_of_expr(l)?, sexp_of_expr(r)?])
        }
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
        Ty::App(n, args) => {
            Ty::App(n.clone(), args.iter().map(|a| substitute_type(a, subst)).collect())
        }
        Ty::Tuple(items) => Ty::Tuple(items.iter().map(|i| substitute_type(i, subst)).collect()),
        Ty::Proof(p, v) => Ty::Proof(
            Box::new(substitute_type(p, subst)),
            Box::new(substitute_type(v, subst)),
        ),
        Ty::Record(fields) => Ty::Record(
            fields.iter().map(|(n, t)| (n.clone(), substitute_type(t, subst))).collect(),
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
    if funs.is_empty() { body } else { Expr::LetFun(funs, Box::new(body)) }
}

/// A fallback token used when the cursor runs past the end of a hand-made
/// stream (the lexer always terminates with `Eof`, so this is a guard).
const EOF_TOKEN: Token = Token {
    kind: TokenKind::Eof,
    span: Span { start: Pos { line: 0, column: 0, offset: 0 }, end: Pos { line: 0, column: 0, offset: 0 } },
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
    /// A counter for names the parser invents, so a desugaring can bind
    /// a temporary without any chance of shadowing the source's own.
    gensym: usize,
    /// `typedef pair (a:t@ype) = '{ ... }` — an alias taking arguments.
    ///
    /// Kept apart from `typedefs` because expanding one is a
    /// substitution rather than a lookup, and the arguments are only
    /// known at the use site.
    typedef_families: HashMap<String, (Vec<String>, Ty)>,
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

impl ParseCtx<'_> {
    // --- cursor primitives -----------------------------------------

    fn peek(&self) -> &Token {
        self.tokens.get(self.pos).unwrap_or(&EOF_TOKEN)
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
            TokenKind::Ident(name) => { self.advance(); Ok(name) }
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
        // Declarations found inside bodies join the program's own.
        defs.extend(std::mem::take(&mut self.pending));
        Ok(Program::new(defs))
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
                &self.peek().kind,
                TokenKind::Ident(w)
                    // Only the *abstract* forms are gathered early.  A
                    // plain `typedef` means what it means from where it
                    // is written, and a local one inside a template
                    // mentions that template's type variables — hoisting
                    // it would take those out of the only scope that
                    // gives them a meaning.
                    if matches!(w.as_str(), "abstype" | "absvtype" | "abst0ype" | "abstbox" | "abstflat" | "assume")
            );
            let before = self.pos;
            if !opens_an_alias || !self.parse_typedef() {
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
                            out.push(Def::Val(ValDef { name, ty: bind.ty, value: bind.value }));
                        }
                        // A pattern at the top level has no remainder to
                        // scope over, so it cannot be lowered here.
                        BindKind::Pattern(..) => {
                            return Err(self.error_here("a pattern binding is not supported at the top level"))
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
                    return Err(self.error_here("a pattern binding is not supported at the top level"));
                };
                if let Some(name) = bind.name {
                    let value =
                        Expr::Call(Box::new(Expr::Var("ref".into())), vec![bind.value]);
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
            TokenKind::Ident(name) if name == "praxi" || name == "prfun" => {
                let save = self.pos;
                if let Ok(decl) = self.parse_extern_decl() {
                    out.push(Def::Extern(decl));
                    return Ok(());
                }
                self.pos = save;
                self.skip_directive();
                Ok(())
            }
            TokenKind::Ident(name) if name == "extern" || name == "static" => {
                let save = self.pos;
                self.advance();
                if self.at_proof_keyword() || matches!(self.peek().kind, TokenKind::Fun | TokenKind::Fn) {
                    if let Ok(decl) = self.parse_extern_decl() {
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
                if self.at_proof_keyword() || matches!(self.peek().kind, TokenKind::Fun | TokenKind::Fn) {
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
        let word = match self.peek().kind.clone() {
            TokenKind::Ident(w) => w,
            _ => { self.skip_directive(); return Ok(()); }
        };
        self.advance();
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
        match self.peek().kind {
            TokenKind::Datatype => self.parse_datatype_def(),
            TokenKind::Fun | TokenKind::Fn => self.parse_fun_def(),
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
        let ty_params = self.parse_optional_type_params()?;
        let scope = self.push_type_vars(&ty_params);
        let def = (|| {
            self.expect(&TokenKind::Eq, "expected `=` after the datatype name")?;
            // The bar before the first constructor is decoration.
            if self.at(&TokenKind::Pipe) {
                self.advance();
            }
            let mut ctors = vec![self.parse_ctor()?];
            while self.at(&TokenKind::Pipe) {
                self.advance();
                ctors.push(self.parse_ctor()?);
            }
            Ok(Def::Datatype(DatatypeDef { name, ty_params, ctors, linear }))
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
    fn parse_optional_type_params(&mut self) -> Result<Vec<String>, CompileError> {
        if !self.at(&TokenKind::LParen) {
            return Ok(vec![]);
        }
        self.advance();
        let mut params = Vec::new();
        loop {
            params.push(self.expect_ident("expected a type parameter")?);
            if self.at(&TokenKind::Colon) {
                // Consume the sort, whatever shape it has: `t@ype` alone
                // is three tokens.
                self.advance();
                while !self.at(&TokenKind::Comma) && !self.at(&TokenKind::RParen) && !self.at(&TokenKind::Eof) {
                    self.advance();
                }
            }
            if self.at(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&TokenKind::RParen, "expected `)` after the type parameters")?;
        Ok(params)
    }

    /// One constructor of a datatype.
    ///
    /// ATS writes the fields after `of`: `Cons of (int, list)`, or
    /// `Some of int` when there is exactly one, or `Nil of ()` when there
    /// are none.  The `of`-less spelling `Cons(int, list)` is accepted as
    /// well, since the subset used it before and both read clearly.
    fn parse_ctor(&mut self) -> Result<Ctor, CompileError> {
        let name = self.expect_ident("expected a constructor name")?;
        self.skip_static_annotations();
        if self.at(&TokenKind::Of) {
            self.advance();
        }
        let fields = if self.at(&TokenKind::LParen) {
            self.advance();
            // `of ()` — no fields at all.
            if self.at(&TokenKind::RParen) {
                self.advance();
                return Ok(Ctor { name, fields: vec![] });
            }
            let mut fields = vec![self.parse_type()?];
            while self.at(&TokenKind::Comma) {
                self.advance();
                fields.push(self.parse_type()?);
            }
            self.expect(&TokenKind::RParen, "expected `)` after the constructor fields")?;
            fields
        } else if self.starts_a_type() {
            // `Some of int` — a single field needs no parentheses.
            vec![self.parse_type()?]
        } else {
            vec![]
        };
        Ok(Ctor { name, fields })
    }

    /// Whether a type could begin at the cursor.
    ///
    /// Used where a type is optional: after `of`, the next token is either
    /// the field's type or the `|` that starts the next constructor.
    fn starts_a_type(&self) -> bool {
        matches!(
            self.peek().kind,
            TokenKind::Ident(_) | TokenKind::LParen | TokenKind::At | TokenKind::Amp | TokenKind::Bang
        )
    }

    fn parse_fun_def(&mut self) -> Result<Def, CompileError> {
        self.advance(); // `fun` / `fn`
        // `fun{a:t@ype} f (...)` — the template parameters precede the
        // name.  They are the *sorts* a template abstracts over, so
        // unlike the other static annotations they are kept.
        let ty_params = self.parse_template_params();
        let name = self.expect_ident("expected a function name")?;
        // `{n:nat}` / `{a:t@ype}` — the dependent half of the signature,
        // and `.<n>.` — the half that says it terminates.
        let (universals, metric) = self.parse_quantifiers_and_metric();
        // The template's parameters are in scope for its own signature
        // and body, so `bintree a` in either place applies `bintree`.
        let scope = self.push_type_vars(&ty_params);
        let params = self.parse_params()?;
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
        self.expect(&TokenKind::Eq, "expected `=` before the function body")?;
        let body = self.parse_expr(0)?;
        self.pop_type_vars(scope);
        Ok(Def::Fun(FunDef { ty_params, universals, existentials, metric, name, params, ret, body }))
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
        let TokenKind::Ident(prop) = self.peek().kind.clone() else { return None };
        self.advance();
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
            let TokenKind::Ident(name) = self.peek().kind.clone() else { return None };
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
                    params.push(Param { name: format!("pf{i}"), ty, borrowed: false });
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
        matches!(&self.peek().kind, TokenKind::Ident(w) if w == "praxi" || w == "prfun")
    }

    fn parse_extern_decl(&mut self) -> Result<FunDecl, CompileError> {
        // `praxi`/`prfun` declare a proof: the checker reads it, the
        // emitter never sees it.
        let proof = self.at_proof_keyword();
        self.advance(); // `fun` / `fn` / `praxi` / `prfun`
        let ty_params = self.parse_template_params();
        let name = self.expect_ident("expected a function name")?;
        // `{n:nat}` — a declaration's quantifiers say exactly what a
        // definition's do, and skipping them here left the corpus's
        // `extern fun`s promising nothing at all.
        let universals = self.parse_quantifiers();
        // As with a `fun`, the template's parameters are in scope for
        // the signature being declared.
        let scope = self.push_type_vars(&ty_params);
        let params = self.parse_params()?;
        if !self.at(&TokenKind::Colon) {
            return Err(self.error_here("expected `:` and a return type"));
        }
        self.advance();
        self.skip_effect_annotation();
        let existentials = self.parse_existentials();
        let ret = self.parse_type()?;
        self.skip_static_annotations();
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
        Ok(FunDecl { linear: false, proof, name, ty_params, universals, existentials, params, ret })
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
            self.expect(&TokenKind::RParen, "expected `)` after the template parameters")?;
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
        Ok(Def::Implement(ImplementDef { ty_params, instance, name, params, ret, body }))
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
            && self.tokens.get(self.pos + 1).is_some_and(|t| matches!(t.kind, TokenKind::Ident(_)))
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
                    let Ok(e) = self.parse_expr(ABOVE_COMPARISON) else { break };
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
                Some(Quant { vars: Vec::new(), guard: Some(claim) })
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
        let vars: Vec<(String, Sort)> =
            names.into_iter().map(|n| (n, Sort::from_name(&sort))).collect();
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
            conjuncts.into_iter().reduce(|a, b| SExp::App("&&".into(), vec![a, b]))
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
        let TokenKind::Ident(mut name) = self.peek().kind.clone() else { return None };
        self.advance();
        while self.at(&TokenKind::At) {
            self.advance();
            let TokenKind::Ident(rest) = self.peek().kind.clone() else { return None };
            self.advance();
            name = format!("{name}@{rest}");
        }
        Some(name)
    }

    /// `[r:int]` — the existential quantifier on a result type.
    fn parse_existentials(&mut self) -> Vec<Quant> {
        let mut out = Vec::new();
        while self.at(&TokenKind::LBracket) {
            let save = self.pos;
            match self.parse_one_quantifier(&TokenKind::RBracket) {
                Some(q) => out.push(q),
                None => {
                    self.pos = save;
                    self.skip_balanced(&TokenKind::LBracket, &TokenKind::RBracket);
                }
            }
        }
        out
    }

    fn skip_static_annotations(&mut self) {
        loop {
            match self.peek().kind {
                TokenKind::LBrace => self.skip_balanced(&TokenKind::LBrace, &TokenKind::RBrace),
                TokenKind::LBracket => self.skip_balanced(&TokenKind::LBracket, &TokenKind::RBracket),
                // `.<>.` — an empty metric.  The lexer reads `<>` as the
                // not-equal token, so this arrives as three tokens and
                // has to be matched on its own.
                TokenKind::Dot if self.tokens.get(self.pos + 1).is_some_and(|t| t.kind == TokenKind::Ne) => {
                    self.advance();
                    self.advance();
                    if self.at(&TokenKind::Dot) {
                        self.advance();
                    }
                }
                // `.<...>.` — a metric proving the recursion terminates.
                TokenKind::Dot if self.tokens.get(self.pos + 1).is_some_and(|t| t.kind == TokenKind::Lt) => {
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
            && self.tokens.get(self.pos + 1).is_some_and(|t| t.kind == TokenKind::LParen)
        {
            self.advance();
            return Ok((Some(Vec::new()), static_args));
        }
        if !(self.at(&TokenKind::Lt) && self.looks_like_template_args()) {
            // No angle group follows: the braces alone decide whether an
            // instance was named.
            return Ok((if saw_brace_group && every_group_typed { Some(brace_args) } else { None }, static_args));
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
                && self.tokens.get(self.pos + 1).is_some_and(|t| t.kind == TokenKind::LParen)
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
        while self.at(&TokenKind::LBrace) || (self.at(&TokenKind::Lt) && self.looks_like_template_args()) {
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
                        | TokenKind::Hash
                        | TokenKind::Eof => true,
                        // A word that begins a declaration cannot be the
                        // right operand of a comparison, so a `>` in front
                        // of one closed a type argument list.
                        TokenKind::Ident(w) => starts_a_declaration(w),
                        _ => false,
                    })
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
    fn parse_params_maybe_untyped(&mut self, allow_untyped: bool) -> Result<Vec<Param>, CompileError> {
        let mut all = self.parse_one_param_list(allow_untyped)?;
        while self.at(&TokenKind::LParen) {
            all.extend(self.parse_one_param_list(allow_untyped)?);
        }
        Ok(all)
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

    fn parse_one_param_list(&mut self, allow_untyped: bool) -> Result<Vec<Param>, CompileError> {
        self.expect(&TokenKind::LParen, "expected `(` to begin the parameter list")?;
        let mut params = Vec::new();
        if !self.at(&TokenKind::RParen) {
            loop {
                // `fun f (string, int): int` — a *declaration* may give
                // the types alone, because a signature has no body to
                // name them for.  A generated name keeps the parameter
                // list one shape for everything downstream.
                let named = matches!(self.peek().kind, TokenKind::Ident(_))
                    && self.tokens.get(self.pos + 1).is_some_and(|t| {
                        matches!(t.kind, TokenKind::Colon | TokenKind::Comma | TokenKind::RParen)
                    });
                if !named {
                    let borrowed = self.at_borrow_marker();
                    let ty = self.parse_type()?;
                    self.gensym += 1;
                    params.push(Param { borrowed, name: format!("arg${}", self.gensym), ty });
                    if self.at(&TokenKind::Comma) {
                        self.advance();
                        continue;
                    }
                    break;
                }
                let name = self.expect_ident("expected a parameter name")?;
                let mut borrowed = false;
                let ty = if self.at(&TokenKind::Colon) {
                    self.advance();
                    borrowed = self.at_borrow_marker();
                    self.parse_type()?
                } else if let Some(known) = well_known_param_type(&name) {
                    // `main`'s two parameters have types fixed by the
                    // language, so ATS lets them go unwritten.
                    known
                } else if allow_untyped {
                    Ty::Name("_".into())
                } else {
                    return Err(self.error_here(format!("parameter `{name}` needs a type annotation")));
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
        Ok(params)
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
                    if sizes.is_empty() { base } else { Ty::Index(Box::new(base), sizes) }
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
        if self.at(&TokenKind::Gt) && self.tokens.get(self.pos + 1).is_some_and(|t| t.kind == TokenKind::Gt) {
            self.advance();
            self.advance();
            let _after = self.parse_type()?;
        }
        Ok(inner)
    }

    /// `name` or `name(args)`, optionally followed by `-> rest`.
    fn parse_named_type(&mut self) -> Result<Ty, CompileError> {
        let mut name = self.expect_ident("expected a type name")?;
        // A bare alias with no arguments still names the canonical type.
        if let Some((canonical, _)) = crate::prelude::canonical_type(&name) {
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
                let kept = if name == base { base.to_string() } else { name.clone() };
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
                let base =
                    if args.is_empty() { Ty::Name(canonical.into()) } else { Ty::App(canonical.into(), args) };
                // The length is kept *around* that type rather than
                // inside it, so what the value is stays exactly what it
                // was: `erased()` gives back the same type as before, and
                // no later stage can tell the difference.
                if sizes.is_empty() { base } else { Ty::Index(Box::new(base), sizes) }
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

    /// A parenthesized type: `(t)`, `(t, u) -> v`, or a tuple (unsupported).
    fn parse_paren_type(&mut self) -> Result<Ty, CompileError> {
        self.advance();
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
        let Some(next) = self.tokens.get(self.pos + 1).map(|t| t.kind.clone()) else { return false };
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
            let Some((op, lbp, rbp)) = self.current_binop() else { break };
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
                        LetBind { opened: Vec::new(), proof: false, name: Some(tmp.clone()), ty: None, value: lhs.clone(), mutable: false },
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
            if matches!(lhs, Expr::Proj(..) | Expr::Index(..) | Expr::Deref(..)) {
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
            self.expect(&TokenKind::RBrace, "expected `}` to close the `where` block")?;
            let inner = if binds.is_empty() { lhs } else { Expr::Let(binds, Box::new(lhs)) };
            // A pattern binding inside a `where` has no following body of
            // its own to scope over; the clause is not one this subset
            // needs, so the pattern is refused rather than guessed at.
            if pending.is_some() {
                return Err(self.error_here("a pattern binding is not supported inside a `where` clause"));
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
                && matches!(self.tokens.get(self.pos + 1).map(|t| &t.kind), Some(TokenKind::IntLit(_)))
            {
                // `xs.0` — a tuple projection.  The lexer only glues a
                // dot into a number when digits came *before* it, so the
                // slot arrives here as its own integer token.
                self.advance();
                let TokenKind::IntLit(n) = self.peek().kind.clone() else { unreachable!() };
                self.advance();
                expr = Expr::Proj(Box::new(expr), n as usize);
            } else if self.at(&TokenKind::Dot)
                && self.tokens.get(self.pos + 1).is_some_and(|t| t.kind == TokenKind::LBracket)
            {
                // `A.[i]` — ATS's array subscript.  The dot is what tells
                // it apart from `xs[i]`, which indexes `argv`.
                self.advance();
                self.advance();
                let index = self.parse_expr(0)?;
                self.expect(&TokenKind::RBracket, "expected `]` after the index")?;
                expr = Expr::Index(Box::new(expr), Box::new(index));
            } else if self.at(&TokenKind::Dot)
                && matches!(self.tokens.get(self.pos + 1).map(|t| &t.kind), Some(TokenKind::Ident(_)))
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
                let TokenKind::Ident(field) = self.peek().kind.clone() else { unreachable!() };
                self.advance();
                expr = Expr::Field(Box::new(expr), field);
            } else if self.at(&TokenKind::LBracket) {
                self.advance();
                let index = self.parse_expr(0)?;
                self.expect(&TokenKind::RBracket, "expected `]` after the index")?;
                expr = Expr::Index(Box::new(expr), Box::new(index));
            } else if matches!(expr, Expr::Var(_) | Expr::Inst(..)) && self.starts_a_juxtaposed_argument() {
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
            TokenKind::Comma if self.macro_depth > 0 => {
                self.tokens.get(self.pos + 1).is_some_and(|t| t.kind == TokenKind::LParen)
            }
            _ => false,
        }
    }

    fn parse_primary(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
        match self.peek().kind.clone() {
            TokenKind::IntLit(n) => { self.advance(); Ok(Expr::IntLit(n)) }
            TokenKind::CharLit(b) => { self.advance(); Ok(Expr::CharLit(b)) }
            TokenKind::FloatLit(v) => { self.advance(); Ok(Expr::FloatLit(v)) }
            TokenKind::True => { self.advance(); Ok(Expr::BoolLit(true)) }
            TokenKind::False => { self.advance(); Ok(Expr::BoolLit(false)) }
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
                self.expect(&TokenKind::RParen, "expected `)` after the spliced expression")?;
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
                    && self.tokens.get(self.pos + 1).is_some_and(|t| t.kind == TokenKind::Dot)
                    && matches!(self.tokens.get(self.pos + 2).map(|t| &t.kind), Some(TokenKind::Ident(_))) =>
            {
                self.advance();
                self.advance();
                self.parse_primary(min_bp)
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
                if matches!(name.as_str(), "$list" | "$lst" | "$list_vt" | "$listlst" | "$arrpsz") =>
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
            // `$raise SomeExn` / `$raise SomeExn(x)` — throw.  There is
            // no `try` in the subset, so nothing can catch it; the name
            // is kept because it is the only thing that will tell anyone
            // what went wrong.
            TokenKind::Ident(name) if name == "$raise" => {
                self.advance();
                let exn = match self.peek().kind.clone() {
                    TokenKind::Ident(n) => {
                        let _thrown = self.parse_primary(min_bp)?;
                        n
                    }
                    _ => "exception".to_string(),
                };
                Ok(Expr::Call(
                    Box::new(Expr::Var("$raise".into())),
                    vec![Expr::StrLit(exn)],
                ))
            }
            TokenKind::Ident(name) if name == "$delay" || name == "$ldelay" => {
                self.advance();
                self.expect(&TokenKind::LParen, "expected `(` after `$delay`")?;
                let body = self.parse_expr(0)?;
                while self.at(&TokenKind::Comma) {
                    self.advance();
                    let _cleanup = self.parse_expr(0)?;
                }
                self.expect(&TokenKind::RParen, "expected `)` after the delayed expression")?;
                Ok(Expr::Call(
                    Box::new(Expr::Var("$delay".into())),
                    vec![Expr::Lam(Vec::new(), None, Box::new(body))],
                ))
            }
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
                self.expect(&TokenKind::RParen, "expected `)` after the parenthesized expression")?;
                let mut it = items.into_iter().rev();
                let mut expr = it.next().expect("at least one element");
                for earlier in it {
                    expr = Expr::Let(
                        vec![LetBind { opened: Vec::new(), proof: false, name: None, ty: None, value: earlier, mutable: false }],
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
            TokenKind::At if self.tokens.get(self.pos + 1).is_some_and(|t| t.kind == TokenKind::LParen) => {
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
        Ok(Expr::IfThenElse(Box::new(cond), Box::new(then_e), Box::new(else_e)))
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
        let inner = if binds.is_empty() { inner } else { Expr::Let(binds, Box::new(inner)) };
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
                let body = if self.at(&TokenKind::RBrace) { Expr::Unit } else { self.parse_expr(0)? };
                self.expect(&TokenKind::RBrace, "expected `}` after the block")?;
                body
            }
        };
        let inner = if binds.is_empty() { inner } else { Expr::Let(binds, Box::new(inner)) };
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
    fn parse_local_decls_and_funs(&mut self) -> Result<(Vec<LetBind>, Vec<FunDef>, Option<(Pattern, Expr)>), CompileError> {
        let mut binds = Vec::new();
        let mut funs = Vec::new();
        loop {
            if matches!(self.peek().kind, TokenKind::Fun | TokenKind::Fn) {
                let Def::Fun(f) = self.parse_fun_def()? else { unreachable!("parse_fun_def yields a Fun") };
                funs.push(f);
                continue;
            }
            // `and g (...) = ...` continues a mutually recursive group.
            if matches!(&self.peek().kind, TokenKind::Ident(w) if w == "and") && !funs.is_empty() {
                let Def::Fun(f) = self.parse_fun_def()? else { unreachable!("parse_fun_def yields a Fun") };
                funs.push(f);
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

    fn parse_local_decl_run(&mut self) -> Result<(Vec<LetBind>, Option<(Pattern, Expr)>), CompileError> {
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
                            binds.push(LetBind { opened: Vec::new(), proof: false, name: Some(c.name), ty: None, value: c.value, mutable: false });
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
        let opened: Vec<(String, Sort)> =
            self.parse_existentials().into_iter().flat_map(|q| q.vars).collect();
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
                return Ok(BindKind::Simple(self.finish_let_bind(&opened, Some(n), None, mutable)?));
            }
            if let Pattern::Tuple(items) = &pattern {
                if items.is_empty() {
                    return Ok(BindKind::Simple(self.finish_let_bind(&opened, None, None, mutable)?));
                }
                if items.len() == 1 {
                    if let Pattern::Var(n) = &items[0] {
                        let n = n.clone();
                        return Ok(BindKind::Simple(self.finish_let_bind(&opened, Some(n), None, mutable)?));
                    }
                }
            }
            if let Pattern::Wildcard = pattern {
                return Ok(BindKind::Simple(self.finish_let_bind(&opened, None, None, mutable)?));
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
        Ok(BindKind::Simple(self.finish_let_bind(&opened, name, None, mutable)?))
    }

    /// The `: type` and `= value` (or uninitialized zero) of a binding.
    fn finish_let_bind(&mut self, opened: &[(String, Sort)], name: Option<String>, _dummy: Option<()>, mutable: bool) -> Result<LetBind, CompileError> {
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
            zero_of(ty).ok_or_else(|| self.error_here("this type has no zero value to start from"))?
        } else {
            self.expect(&TokenKind::Eq, "expected `=` in the binding")?;
            self.parse_expr(0)?
        };
        Ok(LetBind { opened: opened.to_vec(), proof: false, name, ty, value, mutable })
    }

    /// `typedef T = t` — record the alias, and report whether it was one
    /// this parser understands.
    ///
    /// The parameterized form (`typedef m (a:t@ype) = ...`) and record
    /// types are not modelled, so a `typedef` that does not fit is left
    /// to the directive skipper rather than half-recorded.
    fn parse_typedef(&mut self) -> bool {
        let save = self.pos;
        self.advance(); // `typedef`
        let Some(TokenKind::Ident(name)) = self.tokens.get(self.pos).map(|t| t.kind.clone()) else {
            self.pos = save;
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
            while let TokenKind::Ident(p) = self.peek().kind.clone() {
                self.advance();
                params.push(p);
                if self.at(&TokenKind::Colon) {
                    self.advance();
                    if self.parse_sort_name().is_none() {
                        self.pos = save;
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
                self.pos = save;
                return false;
            }
            self.advance();
        }
        if !self.at(&TokenKind::Eq) {
            self.pos = save;
            return false;
        }
        self.advance();
        let scope = self.push_type_vars(&params);
        let parsed = self.parse_type();
        self.pop_type_vars(scope);
        match parsed {
            Ok(ty) if !params.is_empty() => {
                self.typedef_families.insert(name, (params, ty));
                true
            }
            Ok(ty) => {
                self.typedefs.insert(name, ty);
                true
            }
            Err(_) => {
                self.pos = save;
                false
            }
        }
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
        if !matches!(&self.peek().kind, TokenKind::Ident(w) if w == "with") {
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
        Some(Def::Overload { op: op.to_string(), func })
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
                if self.tokens.get(self.pos + 1).is_some_and(|t| t.kind == TokenKind::Eq) =>
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
            Ok(value) => Some(LetBind { opened: Vec::new(), proof: true, name, ty: None, value, mutable: false }),
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
                    self.expect(&TokenKind::RParen, "expected `)` after the constructor fields")?;
                    Ok(Pattern::Ctor(name, fields))
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
        self.expect(&TokenKind::Semicolon, "expected `;` after the loop initializer")?;
        let cond = self.parse_expr(0)?;
        self.expect(&TokenKind::Semicolon, "expected `;` after the loop condition")?;
        let step = self.parse_expr(0)?;
        self.expect(&TokenKind::RParen, "expected `)` after the loop step")?;
        let body = self.parse_expr(0)?;
        Ok(Expr::For(Box::new(init), Box::new(cond), Box::new(step), Box::new(body)))
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
                params.push(Param { borrowed: false, name, ty: Ty::Name("_".into()) });
            }
            params
        };
        let ret = if self.at(&TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };
        if self.at(&TokenKind::Eq) && self.tokens.get(self.pos + 1).is_some_and(|t| t.kind == TokenKind::Lt) {
            self.advance(); // `=`
            while !self.at(&TokenKind::Eof) && !self.at(&TokenKind::Gt) {
                self.advance();
            }
            self.advance(); // `>`
        } else {
            self.expect(&TokenKind::FatArrow, "expected `=>` after the lambda parameters")?;
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
    let Some(mut expr) = it.next() else { return Expr::Unit };
    for earlier in it {
        expr = Expr::Let(
            vec![LetBind { opened: Vec::new(), proof: false, name: None, ty: None, value: earlier, mutable: false }],
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
            other => return Err(CompileError::parse(span, format!("unknown escape sequence `\\{other}`"))),
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- helpers ----------------------------------------------------

    fn body_of(source: &str) -> Expr {
        let p = Parser::parse(source).expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!("expected a fun def") };
        f.body.clone()
    }

    fn impl_body(source: &str) -> Expr {
        let p = Parser::parse(source).expect("parse");
        let Def::Implement(i) = &p.defs()[0] else { panic!("expected an implement def") };
        i.body.clone()
    }

    fn expect_err(source: &str) -> CompileError {
        Parser::parse(source).expect_err("should fail").into_iter().next().expect("at least one error")
    }

    fn int(n: i64) -> Expr { Expr::IntLit(n) }
    fn var(name: &str) -> Expr { Expr::Var(name.to_string()) }

    // --- programs ---------------------------------------------------

    #[test]
    fn parses_an_empty_program() {
        for src in ["", "\n\n", "(* only comments *)"] {
            let p = Parser::parse(src).expect("parse");
            assert_eq!(p.defs().len(), 0, "src: {src}");
        }
    }

    #[test]
    fn parses_a_simple_function() {
        let p = Parser::parse("fun f(x: int): int = x + 1").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.name, "f");
        assert_eq!(f.params.len(), 1);
        assert_eq!(f.params[0], Param { borrowed: false, name: "x".into(), ty: Ty::Name("int".into()) });
        assert_eq!(f.ret, Ty::Name("int".into()));
        assert_eq!(f.body, Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(int(1))));
    }

    #[test]
    fn parses_multi_param_and_zero_param_functions() {
        let p = Parser::parse("fun add(x: int, y: int): int = x + y").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.params.len(), 2);

        let p = Parser::parse("fun forty_two(): int = 42").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.params.len(), 0);
        assert_eq!(f.body, int(42));
    }

    #[test]
    fn parses_two_definitions_in_order() {
        let p = Parser::parse(
            "fun f(): int = 1\nimplement main0() = println!(f())",
        ).expect("parse");
        assert_eq!(p.defs().len(), 2);
        assert!(matches!(p.defs()[0], Def::Fun(_)));
        assert!(matches!(p.defs()[1], Def::Implement(_)));
    }

    #[test]
    fn rejects_non_definitions_at_top_level() {
        let err = expect_err("42");
        assert_eq!(err.kind(), ats2_domain::errors::ErrorKind::Parse);
        assert_eq!(err.message(), "expected a definition");
    }

    // --- datatypes -------------------------------------------------

    #[test]
    fn parses_a_datatype_with_type_parameters() {
        let p = Parser::parse("datatype list(a) = nil | cons(a, list(a))").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else { panic!() };
        assert_eq!(d.name, "list");
        assert_eq!(d.ty_params, vec!["a"]);
        assert_eq!(d.ctors.len(), 2);
        assert_eq!(d.ctors[0], Ctor { name: "nil".into(), fields: vec![] });
        assert_eq!(d.ctors[1].name, "cons");
        assert_eq!(d.ctors[1].fields.len(), 2);
    }

    // --- juxtaposition in types -----------------------------------

    #[test]
    fn a_juxtaposed_type_variable_applies_the_type() {
        // `bintree a`, where `a` is the template's own parameter: the
        // juxtaposition is an application, so the element type survives
        // for inference to read.
        let p = Parser::parse("fun{a:t@ype} size (bt: !bintree a): int = 0").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(
            f.params[0].ty,
            Ty::App("bintree".into(), vec![Ty::Name("a".into())]),
            "got {:?}",
            f.params[0].ty
        );
    }

    #[test]
    fn a_juxtaposed_type_variable_in_datatype_fields() {
        // `cons(bintree a, a, bintree a)` — the datatype's own parameter
        // applied to itself, so the recursive field carries the element
        // type.
        let p = Parser::parse("datatype bintree(a) = nil | cons(bintree a, a, bintree a)").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else { panic!() };
        assert_eq!(
            d.ctors[1].fields[0],
            Ty::App("bintree".into(), vec![Ty::Name("a".into())]),
            "got {:?}",
            d.ctors[1].fields[0]
        );
    }

    #[test]
    fn a_juxtaposed_index_is_still_dropped() {
        // `int n` where `n` is an index quantifier, not a type
        // parameter: an indexed `int`, which erases to plain `int`.
        let p = Parser::parse("fun{n:int} f (x: int n): int = 0").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.params[0].ty, Ty::Index(Box::new(Ty::Name("int".into())), vec![SExp::Var("n".into())]));
    }

    #[test]
    fn a_skipped_directive_stops_at_a_datavtype() {
        // A `staload` line is skipped until the next definition begins —
        // and a `datavtype` is a definition, so the skip must stop there
        // rather than eating it.
        let p = Parser::parse("staload _ = \"x.dats\"\ndatavtype t(a) = nil of () | cons of (a, t a)\nfun f(): int = 1").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else { panic!("got {:?}", &p.defs()[0]) };
        assert_eq!(d.name, "t");
        assert_eq!(d.ctors.len(), 2);
    }

    // --- `val rec` -------------------------------------------------

    #[test]
    fn a_val_with_a_literal_pattern_asserts_the_value() {
        // `val- 55 = _55` — the pattern must match, and a literal pattern
        // is an assertion on the value.
        let body = impl_body("implement main0 () = { val _55 = 55 val- 55 = _55 }");
        let Expr::Let(_, inner) = &body else { panic!("got {body:?}") };
        let Expr::Case(scrut, arms) = &**inner else { panic!("got {body:?}") };
        assert!(matches!(&**scrut, Expr::Var(n) if n == "_55"), "got {body:?}");
        assert_eq!(arms[0].0, Pattern::Int(55));
        // no fallback: a non-match leaves through `exit`
        assert_eq!(arms.len(), 2);
    }

    #[test]
    fn a_val_with_a_constructor_pattern_destructures_it() {
        // `val cons(n, ns) = xs` — a pattern that binds the fields
        // scopes over everything that follows it in the block.
        let body = impl_body("implement main0 () = { val cons(n, ns) = xs val () = g(n, ns) }");
        // The pattern is the block's first binding, so the match is the
        // block itself; a name bound before it would wrap it in a `let`.
        let Expr::Case(scrut, arms) = &body else { panic!("got {body:?}") };
        assert!(matches!(&**scrut, Expr::Var(n) if n == "xs"), "got {body:?}");
        assert_eq!(
            arms[0].0,
            Pattern::Ctor("cons".into(), vec![Pattern::Var("n".into()), Pattern::Var("ns".into())])
        );
    }

    #[test]
    fn val_rec_binds_a_chain_of_mutually_recursive_values() {
        // `val rec a = ... and b = ...` — each binding may mention the
        // others, which is what a mutually recursive lazy value needs.
        let p = Parser::parse(
            "val rec a: int = f(b) and b: int = f(a)\nimplement main0 () = ()",
        )
        .expect("parse");
        assert_eq!(p.defs().len(), 3, "got {:?}", p.defs());
        let Def::Val(v0) = &p.defs()[0] else { panic!() };
        let Def::Val(v1) = &p.defs()[1] else { panic!() };
        assert_eq!(v0.name, "a");
        assert_eq!(v1.name, "b");
        assert_eq!(v0.ty, Some(Ty::Name("int".into())));
    }

    #[test]
    fn parses_a_datavtype_as_a_datatype() {
        // `datavtype` — a datatype whose values are linear.  The views
        // that make it linear are erased here, so it parses as an
        // ordinary datatype and its constructors exist at runtime.
        let p = Parser::parse("datavtype bintree(a) = BTnil of () | BTcons of (bintree a, a, bintree a)").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else { panic!("got {:?}", &p.defs()[0]) };
        assert_eq!(d.name, "bintree");
        assert_eq!(d.ctors.len(), 2);
        assert_eq!(d.ctors[0].name, "BTnil");
        assert_eq!(d.ctors[1].name, "BTcons");
    }

    // --- template arguments in braces ------------------------------

    #[test]
    fn brace_template_arguments_name_the_instance() {
        // `BTnil{int}()` — ATS writes a template's arguments in braces
        // as readily as in angle brackets, and a group that parses as
        // types names the instance.
        let p = Parser::parse("implement main0 () = { val x = BTnil{int}() }").expect("parse");
        let rendered = format!("{:?}", &p.defs()[0]);
        assert!(
            rendered.contains("Inst(\"BTnil\", [Name(\"int\")])"),
            "got:\n{rendered}"
        );
    }

    // --- parameterized macros --------------------------------------

    #[test]
    fn a_parameterized_macdef_expands_at_the_use_site() {
        // `macdef size (bt) = succ ,(bt)` — a macro with parameters is
        // expanded where it is used, the argument spliced in for the
        // parameter, exactly as ATS's own macro expander does.
        let p = Parser::parse("macdef size (bt) = succ ,(bt)\nimplement main0 () = size (3)").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else { panic!("got {:?}", &p.defs()[0]) };
        assert_eq!(i.body, Expr::Call(Box::new(var("succ")), vec![int(3)]));
    }

    #[test]
    fn a_parameterized_macdef_substitutes_everywhere_in_its_body() {
        // The parameter may appear more than once, and nested.
        let p = Parser::parse("macdef twice (x) = ,(x) + ,(x)\nimplement main0 () = twice (n)").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else { panic!("got {:?}", &p.defs()[0]) };
        assert_eq!(
            i.body,
            Expr::BinOp(BinOp::Add, Box::new(var("n")), Box::new(var("n")))
        );
    }

    #[test]
    fn a_parameterized_macdef_may_be_called_by_juxtaposition() {
        // `free bt1` — a one-parameter macro used without parentheses:
        // the following atom is the argument.
        let p = Parser::parse("macdef free (bt) = g ,(bt)\nimplement main0 () = free x").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else { panic!("got {:?}", &p.defs()[0]) };
        assert_eq!(i.body, Expr::Call(Box::new(var("g")), vec![var("x")]));
    }

    #[test]
    fn a_comma_prefixed_expression_splices() {
        // `f(,(x))` inside a macro body — the comma is the splice
        // marker; the expression it prefixes stands on its own, and the
        // use site's argument arrives in its place.
        let p = Parser::parse("macdef m (x) = f(,(x))\nimplement main0 () = m(1)").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else { panic!("got {:?}", &p.defs()[0]) };
        assert_eq!(i.body, Expr::Call(Box::new(var("f")), vec![int(1)]));
    }

    #[test]
    fn a_static_brace_group_after_a_name_is_still_skipped() {
        // `from{n:int} (n)` — the group carries a sort, so it is a
        // quantifier-like static argument, not types, and it contributes
        // nothing.
        let p = Parser::parse("fun f(): int = from{n:int} (1)").expect("parse");
        let rendered = format!("{:?}", &p.defs()[0]);
        assert!(
            !rendered.contains("Inst(\"from\""),
            "a static group was read as a template argument:\n{rendered}"
        );
        assert!(!rendered.contains("StaticInst"), "a binder was read as an argument:\n{rendered}");
    }

    #[test]
    fn parses_a_datatype_without_parameters() {
        let p = Parser::parse("datatype color = red | green | blue").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else { panic!() };
        assert_eq!(d.ty_params, vec![] as Vec<String>);
        assert_eq!(d.ctors.len(), 3);
    }

    #[test]
    fn empty_constructor_list_is_an_error() {
        let err = expect_err("datatype t = ");
        assert!(err.message().contains("constructor"), "{}", err);
    }

    // --- implement ------------------------------------------------

    #[test]
    fn parses_an_implement_clause() {
        let p = Parser::parse("implement main0() = println!(\"hi\")").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else { panic!() };
        assert_eq!(i.name, "main0");
        assert_eq!(i.ret, None);
        assert_eq!(
            i.body,
            Expr::MacroCall("println!".into(), vec![Expr::StrLit("hi".into())])
        );
    }

    #[test]
    fn implement_may_carry_an_explicit_return_type() {
        let p = Parser::parse("implement f(): int = 1").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else { panic!() };
        assert_eq!(i.ret, Some(Ty::Name("int".into())));
    }

    // --- expressions: precedence ----------------------------------

    #[test]
    fn multiplication_binds_tighter_than_addition() {
        assert_eq!(
            body_of("fun f(): int = 1 + 2 * 3"),
            Expr::BinOp(BinOp::Add, Box::new(int(1)), Box::new(Expr::BinOp(BinOp::Mul, Box::new(int(2)), Box::new(int(3)))))
        );
        assert_eq!(
            body_of("fun f(): int = 1 * 2 + 3"),
            Expr::BinOp(BinOp::Add, Box::new(Expr::BinOp(BinOp::Mul, Box::new(int(1)), Box::new(int(2)))), Box::new(int(3)))
        );
    }

    #[test]
    fn comparisons_bind_looser_than_arithmetic() {
        assert_eq!(
            body_of("fun f(x: int): int = x + 1 = 2"),
            Expr::BinOp(BinOp::Eq, Box::new(Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(int(1)))), Box::new(int(2)))
        );
    }

    #[test]
    fn boolean_connectives_are_loosest_and_left_associative() {
        assert_eq!(
            body_of("fun f(a: bool, b: bool): bool = a andalso b orelse a"),
            Expr::BinOp(BinOp::Orelse, Box::new(Expr::BinOp(BinOp::Andalso, Box::new(var("a")), Box::new(var("b")))), Box::new(var("a")))
        );
        assert_eq!(
            body_of("fun f(a: bool, b: bool, c: bool): bool = a andalso b andalso c"),
            Expr::BinOp(BinOp::Andalso, Box::new(Expr::BinOp(BinOp::Andalso, Box::new(var("a")), Box::new(var("b")))), Box::new(var("c")))
        );
    }

    #[test]
    fn mod_division_and_multiplication_share_a_precedence_level() {
        assert_eq!(
            body_of("fun f(x: int, y: int): int = x * y mod 2"),
            Expr::BinOp(BinOp::Mod, Box::new(Expr::BinOp(BinOp::Mul, Box::new(var("x")), Box::new(var("y")))), Box::new(int(2)))
        );
    }

    // --- expressions: structure -----------------------------------

    #[test]
    fn parses_if_then_else() {
        assert_eq!(
            body_of("fun fact(n: int): int = if n = 0 then 1 else 2"),
            Expr::IfThenElse(
                Box::new(Expr::BinOp(BinOp::Eq, Box::new(var("n")), Box::new(int(0)))),
                Box::new(int(1)),
                Box::new(int(2)),
            )
        );
    }

    #[test]
    fn if_without_else_is_a_statement() {
        // ATS allows the one-armed `if` as a statement.  The missing arm
        // is unit, so the whole form has type void.
        assert_eq!(
            impl_body("implement main0() = if true then println!(\"hi\")"),
            Expr::IfThenElse(
                Box::new(Expr::BoolLit(true)),
                Box::new(Expr::MacroCall("println!".into(), vec![Expr::StrLit("hi".into())])),
                Box::new(Expr::Unit),
            )
        );
    }

    // --- datatype declarations --------------------------------------

    fn ctors_of(source: &str) -> Vec<Ctor> {
        let p = Parser::parse(source).expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else { panic!("expected a datatype") };
        d.ctors.clone()
    }

    #[test]
    fn a_constructor_may_be_written_with_of() {
        // `C of (t, u)` is how ATS spells it; `C(t, u)` is accepted too.
        let c = ctors_of("datatype t = A of (int, bool) | B of () | C");
        assert_eq!(c[0].name, "A");
        assert_eq!(c[0].fields, vec![Ty::Name("int".into()), Ty::Name("bool".into())]);
        assert!(c[1].fields.is_empty(), "`of ()` is a constructor with no fields");
        assert!(c[2].fields.is_empty(), "a bare name has no fields either");
    }

    #[test]
    fn a_constructor_may_take_one_unparenthesized_field() {
        let c = ctors_of("datatype t = Some of int | None of ()");
        assert_eq!(c[0].fields, vec![Ty::Name("int".into())]);
    }

    #[test]
    fn a_datatype_may_take_type_parameters() {
        let p = Parser::parse("datatype list0(a) = list0_nil of () | list0_cons of (a, list0(a))").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else { panic!("expected a datatype") };
        assert_eq!(d.ty_params, vec!["a".to_string()]);
        assert_eq!(d.ctors[1].fields[0], Ty::Name("a".into()));
        assert_eq!(d.ctors[1].fields[1], Ty::App("list0".into(), vec![Ty::Name("a".into())]));
    }

    #[test]
    fn a_leading_bar_before_the_first_constructor_is_optional() {
        assert_eq!(ctors_of("datatype t = | A | B").len(), 2);
    }

    #[test]
    fn a_datatype_parameter_may_carry_a_sort() {
        let p = Parser::parse("datatype list0(a:t@ype) = nil0 of ()").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else { panic!("expected a datatype") };
        assert_eq!(d.ty_params, vec!["a".to_string()]);
    }

    // --- top-level values -------------------------------------------

    #[test]
    fn a_val_may_stand_at_the_top_level() {
        let p = Parser::parse("val limit = 10").expect("parse");
        let Def::Val(v) = &p.defs()[0] else { panic!("expected a val, got {:?}", p.defs()[0]) };
        assert_eq!(v.name, "limit");
        assert_eq!(v.value, int(10));
        assert_eq!(v.ty, None);
    }

    #[test]
    fn a_top_level_val_may_be_annotated() {
        let p = Parser::parse("val limit: int = 10").expect("parse");
        let Def::Val(v) = &p.defs()[0] else { panic!("expected a val") };
        assert_eq!(v.ty, Some(ty("int")));
    }

    #[test]
    fn the_empty_termination_metric_is_skipped() {
        // `.<>.` — the lexer reads `<>` as the not-equal token, so the
        // empty metric arrives as three tokens rather than four.
        let p = Parser::parse("fun f {n:nat} .<>. (n: int): int = n").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!("expected a fun") };
        assert_eq!(f.name, "f");
    }

    // --- templates and declarations ---------------------------------

    #[test]
    fn an_extern_fun_declares_a_signature() {
        let p = Parser::parse("extern fun twice (x: int): int").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else { panic!("expected an extern, got {:?}", p.defs()[0]) };
        assert_eq!(d.name, "twice");
        assert_eq!(d.params[0].ty, ty("int"));
        assert_eq!(d.ret, ty("int"));
        assert!(d.ty_params.is_empty());
    }

    #[test]
    fn an_extern_template_records_its_type_parameters() {
        let p = Parser::parse("extern fun{a:t@ype} size (xs: int): int").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else { panic!("expected an extern") };
        assert_eq!(d.ty_params, vec!["a".to_string()]);
    }

    #[test]
    fn a_template_definition_records_its_type_parameters() {
        let p = Parser::parse("fun{a:t0p} ident (x: a): a = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!("expected a fun") };
        assert_eq!(f.ty_params, vec!["a".to_string()]);
    }

    #[test]
    fn an_implement_may_leave_its_parameters_untyped() {
        // The types come from the `extern` declaration above it, so the
        // definition need not repeat them.
        let p = Parser::parse("extern fun twice (x: int): int implement twice (x) = x + x").expect("parse");
        let Def::Implement(i) = &p.defs()[1] else { panic!("expected an implement, got {:?}", p.defs()[1]) };
        assert_eq!(i.params.len(), 1);
        assert_eq!(i.params[0].name, "x");
    }

    #[test]
    fn an_implement_records_the_template_parameters_it_binds() {
        let p = Parser::parse("extern fun{a:t@ype} f (x: a): int implement{a} f (x) = 0").expect("parse");
        let Def::Implement(i) = &p.defs()[1] else { panic!("expected an implement") };
        assert_eq!(i.ty_params, vec!["a".to_string()]);
    }

    #[test]
    fn an_unparsable_extern_is_still_skipped() {
        // Foreign declarations carry syntax the subset does not model
        // (`= "ext#name"`, linear types).  Those must go on being ignored
        // rather than becoming parse errors.
        let p = Parser::parse("extern fun weird {n:nat} (x: &int >> int n): void = \"ext#weird\" fun g(): int = 1")
            .expect("parse");
        assert!(p.defs().iter().any(|d| matches!(d, Def::Fun(f) if f.name == "g")));
    }

    // --- case and patterns -----------------------------------------

    fn arms(source: &str) -> Vec<(Pattern, Expr)> {
        let Expr::Case(_, arms) = impl_body(source) else { panic!("expected a case") };
        arms
    }

    #[test]
    fn parses_a_case_with_constructor_patterns() {
        let a = arms("implement main0() = case xs of | nil() => 0 | cons(x, r) => 1");
        assert_eq!(a.len(), 2);
        assert_eq!(a[0].0, Pattern::Ctor("nil".into(), vec![]));
        assert_eq!(
            a[1].0,
            Pattern::Ctor("cons".into(), vec![Pattern::Var("x".into()), Pattern::Var("r".into())])
        );
        assert_eq!(a[1].1, int(1));
    }

    #[test]
    fn a_leading_bar_is_optional() {
        let a = arms("implement main0() = case xs of nil() => 0 | cons(x, r) => 1");
        assert_eq!(a.len(), 2);
    }

    #[test]
    fn the_exhaustiveness_marker_is_part_of_the_keyword() {
        // `case+` asks the type checker for an exhaustiveness proof; the
        // arms are the same either way.
        assert_eq!(arms("implement main0() = case+ xs of | _ => 0").len(), 1);
    }

    #[test]
    fn a_bare_name_pattern_binds_but_a_nullary_constructor_tests() {
        // `x` binds; `nil()` tests.  The parentheses are what tell them
        // apart, which is exactly how ATS reads them.
        let a = arms("implement main0() = case xs of | other => 0");
        assert_eq!(a[0].0, Pattern::Var("other".into()));
    }

    #[test]
    fn parses_literal_and_wildcard_patterns() {
        let a = arms("implement main0() = case n of | 0 => 1 | _ => 2");
        assert_eq!(a[0].0, Pattern::Int(0));
        assert_eq!(a[1].0, Pattern::Wildcard);
    }

    #[test]
    fn parses_a_tuple_pattern() {
        let a = arms("implement main0() = case p of | (x, y) => 0");
        assert_eq!(a[0].0, Pattern::Tuple(vec![Pattern::Var("x".into()), Pattern::Var("y".into())]));
    }

    #[test]
    fn a_case_arm_may_hold_a_let() {
        let a = arms("implement main0() = case xs of | cons(x, r) => let val y = x in y end");
        assert!(matches!(a[0].1, Expr::Let(..)), "got {:?}", a[0].1);
    }

    // --- ascription and indexing -----------------------------------

    #[test]
    fn a_type_ascription_is_kept_as_the_claim_it_is() {
        // `(e): int` says what `e` should be, which is a claim — and
        // there is a checker to make it to.  The value is untouched, so
        // every stage after the checker looks through it.
        let body = impl_body("implement main0() = (1 + 2): int");
        let Expr::Ascribe(inner, ty) = &body else { panic!("{body:?}") };
        assert_eq!(**inner, Expr::BinOp(BinOp::Add, Box::new(int(1)), Box::new(int(2))));
        assert_eq!(*ty, Ty::Name("int".into()));
    }

    #[test]
    fn an_ascription_may_name_a_dependent_type() {
        // `intGte(0)` is where an unbounded integer becomes a bounded
        // one, and the only line in the file that says so.
        let body = impl_body("implement main0() = 5: intGte(0)");
        let Expr::Ascribe(inner, ty) = &body else { panic!("{body:?}") };
        assert_eq!(**inner, int(5));
        assert_eq!(*ty, Ty::Index(Box::new(Ty::Name("intGte".into())), vec![SExp::IntLit(0)]));
    }

    #[test]
    fn indexing_parses_as_an_index_expression() {
        assert_eq!(
            impl_body("implement main0() = argv[1]"),
            Expr::Index(Box::new(var("argv")), Box::new(int(1)))
        );
    }

    #[test]
    fn indexing_binds_tighter_than_arithmetic() {
        assert_eq!(
            impl_body("implement main0() = xs[0] + 1"),
            Expr::BinOp(BinOp::Add, Box::new(Expr::Index(Box::new(var("xs")), Box::new(int(0)))), Box::new(int(1)))
        );
    }

    #[test]
    fn main_may_take_argc_and_argv_without_annotations() {
        // Their types are fixed by the language, so ATS lets them go
        // unwritten.
        let p = Parser::parse("implement main0(argc, argv) = println!(argc)").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else { panic!("expected an implement") };
        assert_eq!(i.params.len(), 2);
        assert_eq!(i.params[0].name, "argc");
        assert_eq!(i.params[0].ty, Ty::Name("int".into()));
        assert_eq!(i.params[1].name, "argv");
    }

    // --- skipping declarations without losing the ones that matter -

    #[test]
    fn a_proof_binding_keeps_its_proof_and_the_block_around_it() {
        // `prval () = fact_ind{n}()` is proof-level: it is kept, marked,
        // and the body that follows it survives.  The `{n}` inside must
        // not be mistaken for the end of the enclosing block, or the
        // `in` after it is never seen.
        let body = impl_body("implement main0() = let prval () = fact_ind{n}() in println!(1) end");
        let Expr::Let(binds, rest) = &body else { panic!("{body:?}") };
        assert!(binds[0].proof);
        assert_eq!(**rest, Expr::MacroCall("println!".into(), vec![int(1)]));
    }

    #[test]
    fn a_proof_binding_whose_left_hand_side_is_a_pattern_is_still_kept() {
        let body = impl_body("implement main0() = let prval EQINT() = eqint_make{n,0}[x] in println!(2) end");
        let Expr::Let(binds, rest) = &body else { panic!("{body:?}") };
        assert!(binds[0].proof);
        assert_eq!(**rest, Expr::MacroCall("println!".into(), vec![int(2)]));
    }

    #[test]
    fn a_block_still_ends_at_its_closing_brace() {
        // The depth tracking must not swallow a genuine block terminator.
        let body = impl_body("implement main0() = { val x = 1 println!(x) }");
        assert!(matches!(body, Expr::Let(..)), "got {body:?}");
    }

    // --- sequencing, wildcards, template arguments -----------------

    #[test]
    fn a_parenthesized_sequence_runs_in_order() {
        // `(a; b)` evaluates `a` for its effect, then yields `b`.  It is
        // the same construct as a `let` with a discard binding, so it
        // desugars to one.
        let body = impl_body("implement main0() = (println!(\"a\"); println!(\"b\"))");
        let Expr::Let(binds, tail) = &body else { panic!("expected a let, got {body:?}") };
        assert_eq!(binds.len(), 1);
        assert_eq!(binds[0].name, None, "the first element is discarded");
        assert_eq!(binds[0].value, Expr::MacroCall("println!".into(), vec![Expr::StrLit("a".into())]));
        assert_eq!(**tail, Expr::MacroCall("println!".into(), vec![Expr::StrLit("b".into())]));
    }

    #[test]
    fn a_longer_sequence_nests_to_the_right() {
        let body = impl_body("implement main0() = (println!(\"a\"); println!(\"b\"); println!(\"c\"))");
        let Expr::Let(_, tail) = &body else { panic!("expected a let") };
        assert!(matches!(**tail, Expr::Let(..)), "expected the rest to nest, got {tail:?}");
    }

    #[test]
    fn a_wildcard_is_an_expression() {
        // `_` stands for a value the caller does not name.
        let body = impl_body("implement main0() = f(_)");
        assert_eq!(body, Expr::Call(Box::new(var("f")), vec![Expr::Wildcard]));
    }

    #[test]
    fn template_arguments_on_a_call_are_recorded() {
        // `gfact<int>(12)` picks an instantiation, and which one is
        // needed later: monomorphisation turns each into its own
        // function, so the types are kept rather than dropped.
        let body = impl_body("implement main0() = gfact<int>(12)");
        assert_eq!(
            body,
            Expr::Call(Box::new(Expr::Inst("gfact".into(), vec![Ty::Name("int".into())])), vec![int(12)])
        );
    }

    #[test]
    fn brace_arguments_on_a_call_name_the_instance() {
        // `cons{int}(l, r)` — a brace group that parses as types names
        // the instance, exactly as `cons<int>(l, r)` does; ATS uses the
        // two notations interchangeably for template arguments.
        let body = impl_body("implement main0() = cons{int}(1, 2)");
        assert_eq!(
            body,
            Expr::Call(Box::new(Expr::Inst("cons".into(), vec![Ty::Name("int".into())])), vec![int(1), int(2)])
        );
    }

    // --- the type grammar of real ATS ------------------------------

    fn ty(name: &str) -> Ty {
        Ty::Name(name.into())
    }

    fn param_ty(source: &str) -> Ty {
        let p = Parser::parse(source).expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!("expected a fun def") };
        f.params[0].ty.clone()
    }

    #[test]
    fn a_by_reference_parameter_keeps_its_underlying_type() {
        // `&int` says the callee may write through the parameter.  That is
        // a calling convention, not a different type.
        assert_eq!(param_ty("fun f(x: &int): int = 1"), ty("int"));
    }

    #[test]
    fn a_linear_parameter_keeps_its_underlying_type() {
        // `!t` borrows a linear value for the call's duration.
        assert_eq!(param_ty("fun f(x: !int): int = 1"), ty("int"));
    }

    #[test]
    fn an_uninitialized_type_keeps_its_underlying_type() {
        // `int?` is an `int` whose storage is not yet written.
        assert_eq!(param_ty("fun f(x: int?): int = 1"), ty("int"));
    }

    #[test]
    fn a_tuple_type_parses_into_its_components() {
        assert_eq!(
            param_ty("fun f(x: (int, bool)): int = 1"),
            Ty::Tuple(vec![ty("int"), ty("bool")])
        );
    }

    #[test]
    fn a_flat_tuple_type_parses_like_a_boxed_one() {
        // `@(...)` is the unboxed spelling; the components are the same.
        assert_eq!(
            param_ty("fun f(x: @(int, int)): int = 1"),
            Ty::Tuple(vec![ty("int"), ty("int")])
        );
    }

    #[test]
    fn a_type_application_records_every_argument_as_written() {
        // `list(int, n)` carries an element type and a length.  Nothing
        // here can tell a type variable from a static index — `a` and `n`
        // look the same — so the parser keeps both and leaves the
        // distinction to whoever assigns them meaning.
        assert_eq!(
            param_ty("fun f(x: bag(int, n)): int = 1"),
            Ty::App("bag".into(), vec![ty("int"), ty("n")])
        );
    }

    // --- mutable state: `var`, `:=`, `while`, `for` ----------------

    #[test]
    fn a_var_declaration_binds_a_mutable_cell() {
        let body = impl_body("implement main0() = let var x: int = 1 in x end");
        let Expr::Let(binds, _) = &body else { panic!("expected a let, got {body:?}") };
        assert_eq!(binds.len(), 1);
        assert!(binds[0].mutable, "`var` must bind a mutable cell");
        assert_eq!(binds[0].name.as_deref(), Some("x"));
        assert_eq!(binds[0].value, int(1));
    }

    #[test]
    fn a_val_declaration_is_still_immutable() {
        let body = impl_body("implement main0() = let val x: int = 1 in x end");
        let Expr::Let(binds, _) = &body else { panic!("expected a let") };
        assert!(!binds[0].mutable);
    }

    #[test]
    fn an_uninitialized_var_gets_a_zero_of_its_type() {
        // `var i: int` — ATS forbids reading it before it is written, so
        // materializing a zero is observationally equivalent.
        let body = impl_body("implement main0() = let var i: int in i end");
        let Expr::Let(binds, _) = &body else { panic!("expected a let") };
        assert!(binds[0].mutable);
        assert_eq!(binds[0].value, int(0));
    }

    #[test]
    fn parses_an_assignment() {
        let body = impl_body("implement main0() = let var x: int = 1 in x := 5 end");
        let Expr::Let(_, inner) = &body else { panic!("expected a let") };
        assert_eq!(**inner, Expr::Assign("x".into(), Box::new(int(5))));
    }

    #[test]
    fn a_compound_assignment_expands_to_the_operator() {
        // `x :=+ 2` means `x := x + 2`; ATS spells the operator into the
        // assignment rather than into a separate form.
        let body = impl_body("implement main0() = let var x: int = 1 in x :=+ 2 end");
        let Expr::Let(_, inner) = &body else { panic!("expected a let") };
        assert_eq!(
            **inner,
            Expr::Assign("x".into(), Box::new(Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(int(2)))))
        );
    }

    #[test]
    fn parses_a_while_loop() {
        let body = impl_body("implement main0() = while (true) println!(\"x\")");
        assert_eq!(
            body,
            Expr::While(
                Box::new(Expr::BoolLit(true)),
                Box::new(Expr::MacroCall("println!".into(), vec![Expr::StrLit("x".into())])),
            )
        );
    }

    #[test]
    fn parses_a_for_loop_with_three_clauses() {
        let body = impl_body("implement main0() = for (i := 0; i < 3; i :=+ 1) println!(i)");
        let Expr::For(init, cond, step, _) = &body else { panic!("expected a for loop, got {body:?}") };
        assert_eq!(**init, Expr::Assign("i".into(), Box::new(int(0))));
        assert_eq!(**cond, Expr::BinOp(BinOp::Lt, Box::new(var("i")), Box::new(int(3))));
        assert_eq!(
            **step,
            Expr::Assign("i".into(), Box::new(Expr::BinOp(BinOp::Add, Box::new(var("i")), Box::new(int(1)))))
        );
    }

    #[test]
    fn parses_let_in_end_bindings() {
        assert_eq!(
            body_of("fun f(x: int): int = let val y = x + 1 in y * 2 end"),
            Expr::Let(
                vec![LetBind { opened: Vec::new(), proof: false, name: Some("y".into()), ty: None, value: Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(int(1))), mutable: false }],
                Box::new(Expr::BinOp(BinOp::Mul, Box::new(var("y")), Box::new(int(2)))),
            )
        );
    }

    #[test]
    fn let_bindings_may_have_type_annotations_and_discards() {
        let p = Parser::parse(
            "fun f(): int = let val x: int = 1; val () = g() in x end",
        ).expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else { panic!("expected let") };
        assert_eq!(binds.len(), 2);
        assert_eq!(binds[0].ty, Some(Ty::Name("int".into())));
        assert_eq!(binds[1].name, None); // val () = g();  discard binding
    }

    #[test]
    fn one_declaration_may_carry_several_bindings_joined_by_and() {
        // `val a = 1 and b = 2` is a single declaration with two
        // bindings.  ATS binds them simultaneously; the run below is
        // lowered sequentially, which agrees whenever the right-hand
        // sides do not mention a name the same declaration rebinds.
        let p = Parser::parse("fun f(): int = let val a = 1 and b = 2 in a + b end").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else { panic!("expected let") };
        assert_eq!(binds.len(), 2);
        assert_eq!(binds[0].name.as_deref(), Some("a"));
        assert_eq!(binds[1].name.as_deref(), Some("b"));
        assert_eq!(binds[1].value, int(2));
    }

    #[test]
    fn a_dot_and_a_number_project_out_of_a_tuple() {
        assert_eq!(
            body_of("fun f(xs: (int, int)): int = xs.0 + xs.1"),
            Expr::BinOp(
                BinOp::Add,
                Box::new(Expr::Proj(Box::new(var("xs")), 0)),
                Box::new(Expr::Proj(Box::new(var("xs")), 1)),
            )
        );
    }

    #[test]
    fn a_projection_can_be_assigned_to() {
        assert_eq!(
            body_of("fun f(xs: (int, int)): void = xs.0 := 7"),
            Expr::Store(Box::new(Expr::Proj(Box::new(var("xs")), 0)), Box::new(int(7)))
        );
    }

    #[test]
    fn a_typedef_names_a_type_and_is_expanded_where_it_is_used() {
        let p = Parser::parse("typedef T = int\nfun f(x: T): T = x").expect("parse");
        let Def::Fun(f) = p.defs().iter().find(|d| matches!(d, Def::Fun(_))).expect("fun") else { panic!() };
        assert_eq!(f.params[0].ty, Ty::Name("int".into()));
        assert_eq!(f.ret, Ty::Name("int".into()));
    }

    #[test]
    fn a_typedef_may_name_a_tuple() {
        let p = Parser::parse("typedef T2 = (int, int)\nfun f(x: T2): int = x.0").expect("parse");
        let Def::Fun(f) = p.defs().iter().find(|d| matches!(d, Def::Fun(_))).expect("fun") else { panic!() };
        assert_eq!(f.params[0].ty, Ty::Tuple(vec![Ty::Name("int".into()), Ty::Name("int".into())]));
    }

    #[test]
    fn a_proof_component_is_erased_from_what_a_value_is() {
        // `(PROOF | int)` is a value of type `int` carrying a proof.
        // The proof is kept, because it is what the checker reasons
        // with; what the value *is* stays `int`, which is what every
        // stage after the checker asks.
        let p = Parser::parse("fun f(x: int): (FACT(n, r) | int) = (pf | x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.ret.erased(), Ty::Name("int".into()));
        assert!(f.ret.proof().is_some(), "the proposition is kept: {:?}", f.ret);
    }

    #[test]
    fn a_proof_component_is_erased_from_what_an_expression_evaluates_to() {
        let body = body_of("fun f(x: int): int = (pf | x)");
        let Expr::ProofPair(proof, value) = &body else { panic!("{body:?}") };
        assert_eq!(**proof, var("pf"));
        assert_eq!(**value, var("x"), "what runs is the value half");
    }

    #[test]
    fn a_proof_argument_is_erased_from_a_call() {
        assert_eq!(
            body_of("fun f(x: int): int = g (pf | x, 1)"),
            Expr::Call(Box::new(var("g")), vec![var("x"), int(1)])
        );
    }

    #[test]
    fn a_proof_component_is_erased_from_a_pattern() {
        let p = Parser::parse("fun f(x: int): int = let val (pf1 | r1) = g(x) in r1 end").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else { panic!("expected let") };
        assert_eq!(binds[0].name.as_deref(), Some("r1"));
    }

    #[test]
    fn a_termination_metric_is_read_rather_than_skipped() {
        // `.<n>.` is the claim that makes a function *total*: without it
        // a definition may promise anything and satisfy the promise by
        // never returning.  It is a claim, so it is kept.
        let p = Parser::parse("fun f {n:nat} .<n>. (x: int n): int = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.metric, vec![SExp::Var("n".into())]);
        assert_eq!(f.universals.len(), 1, "the quantifier must survive the metric");
    }

    #[test]
    fn a_metric_may_be_lexicographic() {
        let p = Parser::parse("fun f {m,n:nat} .<m, n>. (x: int m): int = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.metric, vec![SExp::Var("m".into()), SExp::Var("n".into())]);
    }

    #[test]
    fn a_metric_may_be_an_expression_not_only_a_variable() {
        let p = Parser::parse("fun f {n:nat} .<n-1>. (x: int n): int = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(
            f.metric,
            vec![SExp::App("-".into(), vec![SExp::Var("n".into()), SExp::IntLit(1)])]
        );
    }

    #[test]
    fn the_empty_metric_claims_nothing_and_is_recorded_as_nothing() {
        // `.<>.` is ATS for "no metric here".  It must not become a
        // metric with no components, which would be a claim about an
        // empty tuple.
        let p = Parser::parse("fun f {n:nat} .<>. (x: int n): int = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert!(f.metric.is_empty());
        assert_eq!(f.universals.len(), 1);
    }

    #[test]
    fn a_bracket_may_hold_a_bare_proposition_with_nothing_bound() {
        // `[fact(0) == 1] void` is how a proof function states what it
        // proves: no witness is named, because there is nothing to name
        // — the claim *is* the content.  Read as a binder it parses as
        // nothing at all, and the axiom says nothing.
        let p = Parser::parse("extern fun ax (): [fact(0) == 1] void").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else { panic!("{:?}", p.defs()[0]) };
        assert_eq!(d.existentials.len(), 1);
        assert!(d.existentials[0].vars.is_empty(), "nothing is bound");
        assert_eq!(
            d.existentials[0].guard,
            Some(SExp::App(
                "==".into(),
                vec![SExp::App("fact".into(), vec![SExp::IntLit(0)]), SExp::IntLit(1)]
            ))
        );
    }

    #[test]
    fn a_proof_function_is_a_signature_like_any_other() {
        // `praxi` declares an axiom: a proof that exists by fiat, whose
        // *result type* is the claim it establishes.  Skipping it threw
        // away the only statement in the file that said anything.
        let p = Parser::parse("extern praxi fact_ind {n:pos} (): [fact(n) == n * fact(n-1)] void")
            .expect("parse");
        let Def::Extern(d) = &p.defs()[0] else { panic!("{:?}", p.defs()[0]) };
        assert_eq!(d.name, "fact_ind");
        assert_eq!(d.universals[0].vars, vec![("n".to_string(), Sort::Pos)]);
        assert_eq!(d.existentials.len(), 1);
    }

    #[test]
    fn a_static_argument_at_a_call_site_is_kept() {
        // `fact_ind{n}()` and `fact_ind{m}()` are the same code and
        // different claims.  An axiom applied at the wrong index is the
        // one mistake a proof language exists to catch, so the index
        // cannot be thrown away on the way in.
        let p = Parser::parse("fun f {n:nat} (x: int n): int = g{n, 0}(x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Call(callee, _) = &f.body else { panic!("{:?}", f.body) };
        let Expr::StaticInst(inner, at) = &**callee else { panic!("{:?}", callee) };
        assert_eq!(**inner, Expr::Var("g".into()));
        assert_eq!(*at, vec![SExp::Var("n".into()), SExp::IntLit(0)]);
    }

    #[test]
    fn several_static_argument_groups_are_read_in_order() {
        let p = Parser::parse("fun f {n:nat} (x: int n): int = g{n+1}{n}(x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Call(callee, _) = &f.body else { panic!() };
        let Expr::StaticInst(_, at) = &**callee else { panic!("{:?}", callee) };
        assert_eq!(
            *at,
            vec![
                SExp::App("+".into(), vec![SExp::Var("n".into()), SExp::IntLit(1)]),
                SExp::Var("n".into())
            ]
        );
    }

    #[test]
    fn a_group_that_reads_as_a_type_stays_a_type_argument() {
        // `{int}` and `{n}` are the same shape; the parser cannot tell
        // them apart and does not try.  It calls the group what it
        // parses as, and the checker — which can see the callee's
        // quantifiers — re-reads it when the signature wants an index.
        let p = Parser::parse("fun f (): int = g{n}(1)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Call(callee, _) = &f.body else { panic!() };
        assert_eq!(**callee, Expr::Inst("g".into(), vec![Ty::Name("n".into())]));
    }

    #[test]
    fn a_call_with_no_static_arguments_is_left_unwrapped() {
        let p = Parser::parse("fun f (x: int): int = g(x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Call(callee, _) = &f.body else { panic!() };
        assert_eq!(**callee, Expr::Var("g".into()));
    }

    #[test]
    fn a_proof_value_becomes_a_binding_the_checker_can_see() {
        // `prval () = fact_ind{n}()` is the line that establishes the
        // claim the rest of the body relies on.  Skipping it threw away
        // the proof and left the body unprovable; emitting it would call
        // a function that was never built.  So it is kept, and marked.
        let p = Parser::parse(
            "fun f {n:nat} (x: int n): int = let prval () = ax{n}() in x end",
        )
        .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else { panic!("{:?}", f.body) };
        assert_eq!(binds.len(), 1);
        assert!(binds[0].proof, "a proof binding must say so");
        assert_eq!(binds[0].name, None, "`()` names nothing");
        assert!(matches!(binds[0].value, Expr::Call(..)), "{:?}", binds[0].value);
    }

    #[test]
    fn a_proof_value_may_be_given_a_name() {
        let p = Parser::parse(
            "fun f {n:nat} (x: int n): int = let prval pf = ax{n}() in x end",
        )
        .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else { panic!() };
        assert_eq!(binds[0].name.as_deref(), Some("pf"));
        assert!(binds[0].proof);
    }

    #[test]
    fn a_proof_value_bound_by_a_pattern_still_runs_its_proof() {
        // `prval EQINT() = eqint_make{n,0}()` names nothing this
        // compiler tracks, but the call on the right is still what
        // establishes the equality.
        let p = Parser::parse(
            "fun f {n:nat} (x: int n): int = let prval EQINT() = mk{n,0}() in x end",
        )
        .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else { panic!("{:?}", f.body) };
        assert!(binds[0].proof);
        assert!(matches!(binds[0].value, Expr::Call(..)), "{:?}", binds[0].value);
    }

    #[test]
    fn a_proof_declaration_that_does_not_parse_is_still_skipped() {
        let p = Parser::parse("fun f (): int = let prval pf = ?? ~~ in 1 end").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert!(matches!(f.body, Expr::Let(..) | Expr::IntLit(1)), "{:?}", f.body);
    }

    #[test]
    fn a_dataprop_constructor_becomes_the_signature_it_is() {
        // `dataprop FACT(int,int) = | {n:pos}{r:int} FACTind (n, n*r) of
        // FACT(n-1, r)` declares `FACTind` as a function from a proof of
        // `FACT(n-1,r)` to a proof of `FACT(n, n*r)`.  That is all a
        // constructor of a proposition is, and saying so needs no
        // machinery a function does not already have.
        let p = Parser::parse(
            "dataprop FACT (int, int) = | FACTbas (0, 1) of () \
             | {n:pos}{r:int} FACTind (n, n*r) of FACT (n-1, r)",
        )
        .expect("parse");
        let decl = |name: &str| {
            p.defs()
                .iter()
                .find_map(|d| match d {
                    Def::Extern(d) if d.name == name => Some(d.clone()),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("no `{name}` in {:?}", p.defs()))
        };
        let bas = decl("FACTbas");
        assert!(bas.params.is_empty());
        assert_eq!(
            bas.ret,
            Ty::Index(Box::new(Ty::Name("FACT".into())), vec![SExp::IntLit(0), SExp::IntLit(1)])
        );
        let ind = decl("FACTind");
        assert_eq!(ind.universals.len(), 2);
        assert_eq!(ind.params.len(), 1, "the proof it consumes");
        assert_eq!(
            ind.ret,
            Ty::Index(
                Box::new(Ty::Name("FACT".into())),
                vec![
                    SExp::Var("n".into()),
                    SExp::App("*".into(), vec![SExp::Var("n".into()), SExp::Var("r".into())])
                ]
            )
        );
    }

    #[test]
    fn an_existential_result_may_be_opened_by_naming_its_witness() {
        // `val [r1:int] (pf1 | r1) = fact (x-1)` names the witness the
        // callee refused to name.  Without the name every fact about the
        // returned value is about a variable nobody can mention twice,
        // and the proof that follows has nothing to attach to.
        let p = Parser::parse("fun f (x: int): int = let val [r1:int] (pf1 | res) = g(x) in res end")
            .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else { panic!("{:?}", f.body) };
        assert_eq!(binds[0].opened, vec![("r1".to_string(), Sort::Int)]);
        assert_eq!(binds[0].name.as_deref(), Some("res"), "the value half is what is bound");
        assert!(!binds[0].proof, "the value half runs");
    }

    #[test]
    fn a_binding_that_opens_nothing_says_so() {
        let p = Parser::parse("fun f (x: int): int = let val y = g(x) in y end").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::Let(binds, _) = &f.body else { panic!() };
        assert!(binds[0].opened.is_empty());
    }

    #[test]
    fn a_result_type_keeps_the_proof_it_promises() {
        // `[r:int] (FACT(n,r) | int(r))` pins `r` down through the
        // proposition.  Erasing the proof half leaves only `int(r)`, and
        // then `r` has to be recovered from arithmetic that is often
        // nonlinear and out of any linear solver's reach.
        let p = Parser::parse("fun f {n:nat} (x: int n): [r:int] (FACT(n, r) | int(r)) = x")
            .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Ty::Proof(proof, value) = &f.ret else { panic!("{:?}", f.ret) };
        // A proposition applied to plain names parses as a type
        // application; the checker reads its arguments as index terms.
        assert_eq!(
            **proof,
            Ty::App("FACT".into(), vec![Ty::Name("n".into()), Ty::Name("r".into())])
        );
        assert_eq!(**value, Ty::Index(Box::new(Ty::Name("int".into())), vec![SExp::Var("r".into())]));
        // What the value *is* is still the value half.
        assert_eq!(f.ret.erased(), Ty::Name("int".into()));
        assert_eq!(f.ret.indices(), &[SExp::Var("r".into())]);
    }

    #[test]
    fn a_returned_pair_keeps_the_proof_it_returns() {
        let p = Parser::parse("fun f (x: int): int = (pf | x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let Expr::ProofPair(proof, value) = &f.body else { panic!("{:?}", f.body) };
        assert_eq!(**proof, Expr::Var("pf".into()));
        assert_eq!(**value, Expr::Var("x".into()));
    }

    #[test]
    fn a_plain_parenthesised_expression_is_not_a_pair() {
        let p = Parser::parse("fun f (x: int): int = (x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.body, Expr::Var("x".into()));
    }

    /// The type of `f`'s only parameter.
    fn first_param_ty(src: &str) -> Ty {
        let p = Parser::parse(src).expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!("expected a fun") };
        f.params[0].ty.clone()
    }

    /// `array(int, n)` — an array of `int`, `n` long.
    fn int_array(size: SExp) -> Ty {
        Ty::Index(Box::new(Ty::App("array".into(), vec![Ty::Name("int".into())])), vec![size])
    }

    #[test]
    fn an_array_keeps_the_size_it_was_declared_with() {
        // The size is the whole reason to write `array(int, n)` rather
        // than `array(int)`: without it `A[i]` cannot be checked against
        // anything, and a bounds check is the obligation ATS exists to
        // make.
        assert_eq!(first_param_ty("fun f {n:nat} (a: array(int, n)): int = 1"), int_array(SExp::Var("n".into())));
    }

    #[test]
    fn the_bracket_spelling_of_an_array_is_the_same_array() {
        // `@[int][n]` is a flat array of `n` ints — the same type
        // `array(int, n)` names, written the way a `var` declares one.
        assert_eq!(first_param_ty("fun f {n:nat} (a: @[int][n]): int = 1"), int_array(SExp::Var("n".into())));
    }

    #[test]
    fn a_by_reference_array_is_the_array_it_refers_to() {
        // `&(@[int][m]) >> _` passes the array by reference and says its
        // view is unchanged.  Neither the `&` nor the `>>` alters what
        // the value is or how long it is.
        assert_eq!(
            first_param_ty("fun f {m:nat} (t: &(@[int][m]) >> _): int = 1"),
            int_array(SExp::Var("m".into()))
        );
    }

    #[test]
    fn an_arrayref_is_an_array_with_its_size() {
        assert_eq!(
            first_param_ty("fun f {n:nat} (a: arrayref(int, n)): int = 1"),
            int_array(SExp::Var("n".into()))
        );
    }

    #[test]
    fn a_size_may_be_an_expression_rather_than_a_variable() {
        assert_eq!(
            first_param_ty("fun f {n:nat} (a: array(int, n+1)): int = 1"),
            int_array(SExp::App("+".into(), vec![SExp::Var("n".into()), SExp::IntLit(1)]))
        );
    }

    #[test]
    fn a_run_of_bytes_is_indexed_by_how_many_there_are() {
        // `b0ytes(n)` is `n` bytes, uninitialised; `bytes(n)` is `n`
        // bytes that have been written.  The difference is a view, which
        // this compiler does not track; the length is not, and it is
        // what a bounds check needs.
        for name in ["bytes", "b0ytes"] {
            let ty = first_param_ty(&format!("fun f {{n:pos}} (b: {name}(n)): int = 1"));
            assert_eq!(ty.indices(), &[SExp::Var("n".into())], "{name}: {ty:?}");
        }
    }

    #[test]
    fn an_arrays_size_is_static_and_leaves_no_trace_in_what_it_is() {
        // Emission must not notice any of this: an `array(int, n)` and
        // an `array(int)` are the same bytes.
        assert_eq!(
            first_param_ty("fun f {n:nat} (a: array(int, n)): int = 1").erased(),
            Ty::App("array".into(), vec![Ty::Name("int".into())])
        );
    }

    #[test]
    fn a_block_of_inline_c_survives_to_the_program() {
        // A program that declares `extern fun f = "ext#f"` and defines
        // `f` in a `%{ %}` block used to compile and then fail to link,
        // naming a symbol whose definition was thrown away three stages
        // earlier.  The text is not this compiler's language; it is the
        // toolchain's, and it has to reach it.
        let p = Parser::parse(
            "%{^\nint triple (int n) { return 3 * n; }\n%}\n\
             extern fun triple (n: int): int = \"ext#triple\"\n\
             implement main0 () = println! (triple (2))",
        )
        .expect("parse");
        let c: Vec<&String> = p
            .defs()
            .iter()
            .filter_map(|d| match d {
                Def::InlineC(text) => Some(text),
                _ => None,
            })
            .collect();
        assert_eq!(c.len(), 1, "{:?}", p.defs());
        assert!(c[0].contains("return 3 * n"), "{}", c[0]);
    }

    #[test]
    fn the_marker_that_says_where_the_c_goes_is_not_part_of_it() {
        // `%{^` puts it above the output and `%{$` below.  Neither
        // marker is C, and leaving one in makes the file not compile.
        let p = Parser::parse("%{$\nint z = 1;\n%}\nimplement main0 () = println! (0)")
            .expect("parse");
        let Some(Def::InlineC(text)) = p.defs().iter().find(|d| matches!(d, Def::InlineC(_)))
        else {
            panic!("{:?}", p.defs())
        };
        assert!(!text.contains('$'), "the marker survived: {text}");
        assert!(text.trim().starts_with("int z"), "{text}");
    }

    #[test]
    fn a_linear_datatype_says_that_it_is_one() {
        // `datavtype` declares values that must be consumed exactly
        // once.  Parsing it as an ordinary `datatype` erases the only
        // thing that distinguishes it, and the resource discipline that
        // is half of what ATS is for goes unchecked.
        let p = Parser::parse("datavtype box_vt(a) = mk_vt of (a)").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else { panic!("{:?}", p.defs()[0]) };
        assert!(d.linear, "a datavtype is linear");
    }

    #[test]
    fn an_ordinary_datatype_is_not_linear() {
        let p = Parser::parse("datatype box(a) = mk of (a)").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else { panic!() };
        assert!(!d.linear);
    }

    #[test]
    fn a_dataview_is_linear_as_well() {
        // A `dataview` is a `dataprop` whose proofs are resources: it
        // stands for permission to touch something, and permission that
        // could be used twice would not be permission at all.
        let p = Parser::parse("dataview owned (int) = | own (0) of ()").expect("parse");
        let owned = p.defs().iter().any(|d| matches!(d, Def::Extern(e) if e.name == "own" && e.linear));
        assert!(owned, "{:?}", p.defs());
    }

    #[test]
    fn a_borrowed_parameter_says_that_it_is_borrowed() {
        // `!xs` is lent, not given: the caller keeps it, and the body
        // must *not* consume it.  Dropping the `!` makes every borrow
        // look like a handover.
        let p = Parser::parse("fun f (xs: !box_vt(int), ys: box_vt(int)): int = 1").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert!(f.params[0].borrowed, "`!` marks a borrow");
        assert!(!f.params[1].borrowed, "a plain parameter is given");
    }

    #[test]
    fn a_by_reference_parameter_is_borrowed_too() {
        // `&t` passes a cell the caller keeps: the callee may write
        // through it and may not consume it.
        let p = Parser::parse("fun f (a: &int): int = 1").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert!(f.params[0].borrowed);
    }

    #[test]
    fn a_dataprop_that_does_not_parse_is_skipped_not_fatal() {
        let p = Parser::parse("dataprop WEIRD = | ??? \n fun f(): int = 1").expect("parse");
        assert!(p.defs().iter().any(|d| matches!(d, Def::Fun(f) if f.name == "f")));
    }

    #[test]
    fn a_proof_function_needs_no_extern_before_it() {
        let p = Parser::parse("praxi ax (): [1 == 1] void").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else { panic!("{:?}", p.defs()[0]) };
        assert_eq!(d.name, "ax");
    }

    #[test]
    fn a_proof_function_that_does_not_parse_is_skipped_not_fatal() {
        // The fallback must survive: a proof language this compiler does
        // not model costs its own declaration, never the file.
        let p = Parser::parse("praxi weird {a:t@ype} (!list(a) >> list(a)): void\nfun f(): int = 1")
            .expect("parse");
        assert!(p.defs().iter().any(|d| matches!(d, Def::Fun(f) if f.name == "f")));
    }

    #[test]
    fn a_bracket_holding_a_binder_is_still_read_as_a_binder() {
        let p = Parser::parse("extern fun g (): [r:nat] int r").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else { panic!() };
        assert_eq!(d.existentials[0].vars, vec![("r".to_string(), Sort::Nat)]);
        assert_eq!(d.existentials[0].guard, None);
    }

    #[test]
    fn a_brace_holding_only_a_name_is_an_instantiation_and_binds_nothing() {
        // `f{n}(...)` hands a static argument to a call; it is not a
        // quantifier, and reading it as a bare proposition would turn
        // every instantiation into an assumption.
        let p = Parser::parse("fun f {n:nat} (x: int n): int = g{n}(x)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.universals.len(), 1);
        assert_eq!(f.universals[0].vars, vec![("n".to_string(), Sort::Nat)]);
    }

    #[test]
    fn an_extern_declaration_records_its_quantifiers_too() {
        // `extern fun f {n:nat} (int n): int` is how the corpus declares
        // everything it implements elsewhere, and a declaration that
        // forgets its quantifier is a promise nobody can keep.
        let p = Parser::parse("extern fun ext {n:nat} (x: int n): int").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else { panic!("{:?}", p.defs()[0]) };
        assert_eq!(d.universals.len(), 1);
        assert_eq!(d.universals[0].vars, vec![("n".to_string(), Sort::Nat)]);
    }

    #[test]
    fn a_universal_quantifier_is_recorded_rather_than_skipped() {
        // `{n:nat | n > 0}` is the dependent half of the signature.  It
        // is what makes the type of `f` say something about *which*
        // integers it accepts, so it is kept, not skipped.
        let p = Parser::parse("fun f {n:nat | n > 0} (x: int n): int n = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.universals.len(), 1);
        assert_eq!(f.universals[0].vars, vec![("n".to_string(), Sort::Nat)]);
        assert_eq!(
            f.universals[0].guard,
            Some(SExp::App(">".into(), vec![SExp::Var("n".into()), SExp::IntLit(0)]))
        );
    }

    #[test]
    fn a_guard_may_be_several_claims_separated_by_semicolons() {
        // `{i,j:nat | i <= j+1; i+j == n-1}` is one guard written as two
        // conjuncts, and it is how every real ATS loop invariant is
        // spelled.  Failing to read the `;` cost the *whole* quantifier
        // — the sorts included — so a loop lost even its nat-ness.
        let p = Parser::parse("fun loop {i,j:nat | i <= j; i+j == 4} (x: int i): int = x")
            .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.universals.len(), 1);
        assert_eq!(f.universals[0].vars.len(), 2);
        assert_eq!(
            f.universals[0].guard,
            Some(SExp::App(
                "&&".into(),
                vec![
                    SExp::App("<=".into(), vec![SExp::Var("i".into()), SExp::Var("j".into())]),
                    SExp::App(
                        "==".into(),
                        vec![
                            SExp::App("+".into(), vec![SExp::Var("i".into()), SExp::Var("j".into())]),
                            SExp::IntLit(4)
                        ]
                    ),
                ]
            ))
        );
    }

    #[test]
    fn every_conjunct_of_a_guard_reaches_the_checker_as_a_hypothesis() {
        let p = Parser::parse("fun loop {i,j:nat | i <= j; i+j == 4} (x: int i): int = x")
            .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        let hyps: Vec<String> = f.universals[0].hypotheses().iter().map(|h| h.to_string()).collect();
        assert!(hyps.contains(&"i >= 0".to_string()), "{hyps:?}");
        assert!(hyps.contains(&"j >= 0".to_string()), "{hyps:?}");
        assert!(hyps.iter().any(|h| h.contains("i <= j")), "{hyps:?}");
    }

    #[test]
    fn several_quantifiers_may_precede_a_signature() {
        let p = Parser::parse("fun f {m,n:nat} {r:int} (x: int m): int = x").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.universals.len(), 2);
        assert_eq!(f.universals[0].vars.len(), 2);
        assert_eq!(f.universals[1].vars, vec![("r".to_string(), Sort::Int)]);
    }

    #[test]
    fn an_indexed_type_keeps_its_index() {
        let p = Parser::parse("fun f {n:nat} (x: int n): int(n+1) = x + 1").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.params[0].ty, Ty::Index(Box::new(Ty::Name("int".into())), vec![SExp::Var("n".into())]));
        assert_eq!(
            f.ret,
            Ty::Index(
                Box::new(Ty::Name("int".into())),
                vec![SExp::App("+".into(), vec![SExp::Var("n".into()), SExp::IntLit(1)])]
            )
        );
    }

    #[test]
    fn parses_brace_blocks_as_lets() {
        assert_eq!(
            impl_body("implement main0() = { val x = 1; x + 1 }"),
            Expr::Let(
                vec![LetBind { opened: Vec::new(), proof: false, name: Some("x".into()), ty: None, value: int(1), mutable: false }],
                Box::new(Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(int(1)))),
            )
        );
    }

    #[test]
    fn parses_lambdas() {
        assert_eq!(
            body_of("fun f(): int = lam (x: int) => x + 1"),
            Expr::Lam(
                vec![Param { borrowed: false, name: "x".into(), ty: Ty::Name("int".into()) }],
                None,
                Box::new(Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(int(1)))),
            )
        );
    }

    #[test]
    fn a_macro_splice_may_follow_another_argument() {
        // The comma that separates two arguments is not the comma that
        // opens a splice, and only what follows it says which is which.
        assert_eq!(
            body_of("macdef get (n) = f (xs, ,(n))\nfun g(x: int): int = get(x)"),
            Expr::Call(Box::new(var("f")), vec![var("xs"), var("x")])
        );
        assert_eq!(
            body_of("macdef get (n) = f (xs, 1)\nfun g(x: int): int = get(x)"),
            Expr::Call(Box::new(var("f")), vec![var("xs"), int(1)])
        );
    }

    #[test]
    fn a_macro_body_may_unquote_its_parameter() {
        // `,(n)` inside a `macdef` body is ATS's unquote: it splices the
        // argument in rather than naming it.  Since a macro is expanded
        // as it is read, the splice has already happened by the time the
        // body is parsed, and the marker means nothing more than
        // parentheses do.
        assert_eq!(
            body_of("macdef twice (n) = ,(n) + ,(n)\nfun f(x: int): int = twice(x)"),
            Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(var("x")))
        );
    }

    #[test]
    fn raise_names_the_exception_it_throws() {
        assert_eq!(
            body_of("fun f(): int = $raise StreamSubscriptExn"),
            Expr::Call(Box::new(var("$raise")), vec![Expr::StrLit("StreamSubscriptExn".into())])
        );
    }

    #[test]
    fn an_arrow_may_carry_its_effects() {
        // `-<cloref1>` is an arrow that also says the function is a
        // closure.  Who may call it is a question for the type checker;
        // that it *is* an arrow is a question for the parser.
        let p = Parser::parse("extern fun apply (f: (int) -<cloref1> bool): bool").expect("parse");
        let Def::Extern(d) = &p.defs()[0] else { panic!("expected an extern") };
        assert_eq!(
            d.params[0].ty,
            Ty::Fun(vec![Ty::Name("int".into())], Box::new(Ty::Name("bool".into())))
        );
    }

    #[test]
    fn a_template_parameter_shadows_a_typedef_of_the_same_name() {
        // `implement(res) f<res> (...)` binds `res` as the
        // implementation's own type parameter.  A `typedef res` in scope
        // is an outer name, and a binder shadows one — expanding it here
        // would turn the generic implementation into an instance of
        // whatever the alias happened to mean.
        let p = Parser::parse(
            "typedef res = int\nimplement(res) f<res> (x: res): res = x",
        )
        .expect("parse");
        let Def::Implement(i) = &p.defs()[0] else { panic!("expected an implement") };
        assert_eq!(i.ty_params, vec!["res".to_string()]);
        assert_eq!(i.instance, vec![Ty::Name("res".into())]);
    }

    #[test]
    fn only_angle_brackets_name_the_instance_an_implement_fills_in() {
        // `implement{a} f {n} (xs) = ...` quantifies over the *index*
        // `n`; it is still the generic implementation.  Reading the
        // brace group as a type argument would file it under an instance
        // nobody ever asks for, and the generic body would be missing.
        let p = Parser::parse("implement{a} f {n} (xs: int): int = xs").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else { panic!("expected an implement") };
        assert!(i.instance.is_empty(), "a static argument was read as an instance: {:?}", i.instance);

        let p = Parser::parse("implement f<int> (xs: int): int = xs").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else { panic!("expected an implement") };
        assert_eq!(i.instance, vec![Ty::Name("int".into())]);
    }

    #[test]
    fn a_list_literal_becomes_the_conses_that_build_it() {
        // `$list{int}(1, 2)` is list-literal syntax and nothing more, so
        // it is desugared here rather than carried to the emitter as a
        // form of its own — and everything downstream, inference
        // included, then sees an ordinary list.
        assert_eq!(
            body_of("fun f(): list0(int) = $list{int}(1, 2)"),
            Expr::Call(
                Box::new(Expr::Inst("list0_cons".into(), vec![Ty::Name("int".into())])),
                vec![
                    int(1),
                    Expr::Call(
                        Box::new(Expr::Inst("list0_cons".into(), vec![Ty::Name("int".into())])),
                        vec![
                            int(2),
                            Expr::Call(
                                Box::new(Expr::Inst("list0_nil".into(), vec![Ty::Name("int".into())])),
                                vec![],
                            ),
                        ],
                    ),
                ],
            )
        );
    }

    #[test]
    fn an_assumed_type_is_known_even_above_the_assumption() {
        // `abstype` hides a type; `assume` says what it really is.  The
        // assumption may sit far below the uses — in ordset it is inside
        // a `local` near the end of the file — and it still has to
        // decide what those uses mean.
        let p = Parser::parse(concat!(
            "abstype set (a:t@ype) = ptr\n",
            "fun f(): set(int) = g()\n",
            "assume set (a:t@ype) = list0(a)\n",
        ))
        .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!("expected a fun") };
        assert_eq!(f.ret, Ty::App("list0".into(), vec![Ty::Name("int".into())]));
    }

    #[test]
    fn an_instantiated_template_may_be_applied_without_parentheses() {
        // `f<int> '{ x= 1 }` — ATS lets application drop its
        // parentheses, and naming the instance does not take that away.
        assert_eq!(
            body_of("fun f(): int = make<int> '{ x= 1 }"),
            Expr::Call(
                Box::new(Expr::Inst("make".into(), vec![Ty::Name("int".into())])),
                vec![Expr::RecordLit(vec![("x".into(), int(1))])],
            )
        );
    }

    #[test]
    fn a_typedef_may_take_parameters() {
        // `typedef ordmod (a:t@ype) = '{ ... }` names a *family* of
        // types.  Each use supplies the arguments, and the alias means
        // its body with those substituted in.
        let p = Parser::parse(
            "typedef pair (a:t@ype) = '{ fst= a, snd= a }\nfun f(): pair(int) = g()",
        )
        .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!("expected a fun") };
        assert_eq!(
            f.ret,
            Ty::Record(vec![
                ("fst".into(), Ty::Name("int".into())),
                ("snd".into(), Ty::Name("int".into())),
            ])
        );
    }

    #[test]
    fn skipping_a_directive_stops_at_the_next_val() {
        // Nothing punctuates the end of a `staload`, so the skip runs
        // until it recognises the start of the next form — and a
        // top-level `val` is one.  Missing it swallowed the declaration
        // whole, and the name it bound went undefined.
        let p = Parser::parse("staload \"x.sats\"\nval a: int = 1").expect("parse");
        assert!(
            p.defs().iter().any(|d| matches!(d, Def::Val(v) if v.name == "a")),
            "the `val` was swallowed: {:?}",
            p.defs()
        );
    }

    #[test]
    fn a_stream_takes_its_element_type_by_juxtaposition() {
        // `stream N2` and `stream(N2)` are the same type written two
        // ways.  Without the arity a juxtaposed name reads as a static
        // index and is dropped, which loses the element type.
        let p = Parser::parse("typedef N2 = int\nfun f(): stream N2 = g()").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!("expected a fun") };
        assert_eq!(f.ret, Ty::App("stream".into(), vec![Ty::Name("int".into())]));
    }

    #[test]
    fn delay_wraps_its_body_in_a_nullary_lambda() {
        assert_eq!(
            body_of("fun f(): int = $delay(1)"),
            Expr::Call(
                Box::new(var("$delay")),
                vec![Expr::Lam(vec![], None, Box::new(int(1)))],
            )
        );
    }

    #[test]
    fn ldelay_drops_the_cleanup_it_is_given() {
        // `$ldelay(e, ~xs)` names what to run if the stream is dropped
        // unforced.  The arena frees everything at once, so there is
        // nothing for it to do.
        assert_eq!(
            body_of("fun f(): int = $ldelay(1, free(x))"),
            Expr::Call(
                Box::new(var("$delay")),
                vec![Expr::Lam(vec![], None, Box::new(int(1)))],
            )
        );
    }

    #[test]
    fn a_define_renames_a_constructor_in_patterns_and_expressions() {
        let src = "#define cons stream_vt_cons\n\
                   fun f(xs: list0(int)): int = case xs of | cons(n, r) => n | _ => 0";
        let Expr::Case(_, arms) = body_of(src) else { panic!("expected a case") };
        assert_eq!(
            arms[0].0,
            Pattern::Ctor("stream_vt_cons".into(), vec![Pattern::Var("n".into()), Pattern::Var("r".into())])
        );
    }

    #[test]
    fn a_renamed_constructor_is_renamed_in_expressions_too() {
        let src = "#define cons stream_vt_cons\nfun f(x: int): int = cons(x, x)";
        assert_eq!(
            body_of(src),
            Expr::Call(Box::new(var("stream_vt_cons")), vec![var("x"), var("x")])
        );
    }

    #[test]
    fn a_vtypedef_names_a_type_the_same_way_a_typedef_does() {
        let p = Parser::parse("vtypedef res = list0(int)
fun f(): res = list0_nil()")
            .expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!("expected a fun") };
        assert_eq!(f.ret, Ty::App("list0".into(), vec![Ty::Name("int".into())]));
    }

    #[test]
    fn an_implement_may_take_its_template_parameters_in_parentheses() {
        let p = Parser::parse("implement(a) f<a> (x) = x").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else { panic!("expected an implement") };
        assert_eq!(i.ty_params, vec!["a".to_string()]);
    }

    #[test]
    fn a_let_body_may_be_a_sequence() {
        assert_eq!(
            body_of("fun f(): int = let val x = 1 in g(); x end"),
            Expr::Let(
                vec![LetBind { opened: Vec::new(), proof: false, name: Some("x".into()), ty: None, value: int(1), mutable: false }],
                Box::new(Expr::Let(
                    vec![LetBind {
                        opened: Vec::new(),
                        proof: false,
                        name: None,
                        ty: None,
                        value: Expr::Call(Box::new(var("g")), vec![]),
                        mutable: false
                    }],
                    Box::new(var("x")),
                )),
            )
        );
    }

    #[test]
    fn fold_at_is_a_no_op() {
        assert_eq!(
            body_of("fun f(x: int): int = let val () = fold@ x in x end"),
            Expr::Let(
                vec![LetBind { opened: Vec::new(), proof: false, name: None, ty: None, value: Expr::Unit, mutable: false }],
                Box::new(var("x")),
            )
        );
    }

    #[test]
    fn a_semicolon_may_follow_a_pattern_binding() {
        let body = body_of("fun f(xs: list0(int)): int = let val-cons(n, r) = xs; val p = n in p end");
        assert!(matches!(body, Expr::Case(..)), "expected a case, got {body:?}");
    }

    #[test]
    fn a_module_qualifier_is_dropped_from_a_call() {
        assert_eq!(
            body_of("fun f(): double = $STDLIB.drand48()"),
            Expr::Call(Box::new(var("drand48")), vec![])
        );
    }

    #[test]
    fn a_val_binding_may_open_with_an_at_pattern() {
        let Expr::Case(_, arms) =
            body_of("fun f(xs: list0(int)): int = let val-@cons(n, r) = xs in n end")
        else {
            panic!("expected a case")
        };
        assert_eq!(
            arms[0].0,
            Pattern::InPlace(Box::new(Pattern::Ctor(
                "cons".into(),
                vec![Pattern::Var("n".into()), Pattern::Var("r".into())]
            )))
        );
    }

    #[test]
    fn a_local_block_inside_a_body_contributes_its_public_bindings() {
        let Expr::Let(binds, body) = body_of(
            "fun f(): int = let local val hidden = 1 in val shown = 2 end in shown end",
        ) else {
            panic!("expected a let")
        };
        assert_eq!(
            binds.iter().filter_map(|b| b.name.as_deref()).collect::<Vec<_>>(),
            vec!["hidden", "shown"]
        );
        assert_eq!(*body, var("shown"));
    }

    #[test]
    fn an_implement_may_qualify_its_name_with_a_module() {
        let p = Parser::parse("implement $RG.randgen_val<int> () = 1").expect("parse");
        let Def::Implement(i) = &p.defs()[0] else { panic!("expected an implement") };
        assert_eq!(i.name, "randgen_val");
    }

    #[test]
    fn begin_end_brackets_a_sequence() {
        assert_eq!(
            body_of("fun f(): int = begin g(); 1 end"),
            Expr::Let(
                vec![LetBind {
                    opened: Vec::new(),
                    proof: false,
                    name: None,
                    ty: None,
                    value: Expr::Call(Box::new(var("g")), vec![]),
                    mutable: false
                }],
                Box::new(int(1)),
            )
        );
    }

    #[test]
    fn begin_end_tolerates_a_trailing_semicolon() {
        assert_eq!(body_of("fun f(): int = begin 1 ; end"), int(1));
    }

    #[test]
    fn an_at_marks_a_pattern_as_matching_in_place() {
        let Expr::Case(_, arms) = body_of("fun f(xs: list0(int)): int = case xs of | @cons(n, r) => 1 | _ => 0")
        else {
            panic!("expected a case")
        };
        assert_eq!(
            arms[0].0,
            Pattern::InPlace(Box::new(Pattern::Ctor(
                "cons".into(),
                vec![Pattern::Var("n".into()), Pattern::Var("r".into())]
            )))
        );
    }

    #[test]
    fn a_proof_bar_drops_the_proofs_from_a_tuple_pattern() {
        let Expr::Let(binds, _) =
            body_of("fun f(): int = let val (pfat, pfgc | p) = g() in p end")
        else {
            panic!("expected a let")
        };
        assert_eq!(binds[0].name.as_deref(), Some("p"));
    }

    #[test]
    fn template_arguments_may_be_type_applications() {
        let Expr::Call(head, _) = body_of(
            "fun f(out: int): int = fprint_tupval2<int,tup(bool,char)> (out, 1)",
        ) else {
            panic!("expected a call")
        };
        let Expr::Inst(name, args) = *head else { panic!("expected an instantiation, got {head:?}") };
        assert_eq!(name, "fprint_tupval2");
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn parses_cons_as_an_infix_pattern() {
        let Expr::Case(_, arms) = body_of(
            "fun f(xs: list0(int)): int = case xs of | x :: rest => 1 | _ => 0",
        ) else {
            panic!("expected a case")
        };
        assert_eq!(
            arms[0].0,
            Pattern::Ctor("cons".into(), vec![Pattern::Var("x".into()), Pattern::Var("rest".into())])
        );
    }

    #[test]
    fn cons_patterns_nest_to_the_right() {
        let Expr::Case(_, arms) = body_of(
            "fun f(xs: list0(int)): int = case xs of | x :: y :: rest => 1 | _ => 0",
        ) else {
            panic!("expected a case")
        };
        assert_eq!(
            arms[0].0,
            Pattern::Ctor(
                "cons".into(),
                vec![
                    Pattern::Var("x".into()),
                    Pattern::Ctor(
                        "cons".into(),
                        vec![Pattern::Var("y".into()), Pattern::Var("rest".into())]
                    ),
                ]
            )
        );
    }

    #[test]
    fn parses_cons_as_an_infix_expression() {
        assert_eq!(
            body_of("fun f(x: int, xs: list0(int)): list0(int) = x :: xs"),
            Expr::Call(
                Box::new(var("cons")),
                vec![var("x"), var("xs")],
            )
        );
    }

    #[test]
    fn a_define_renames_the_cons_operator() {
        let Expr::Case(_, arms) = body_of(
            "#define :: stream_vt_cons
fun f(xs: list0(int)): int = case xs of | x :: rest => 1 | _ => 0",
        ) else {
            panic!("expected a case")
        };
        assert_eq!(
            arms[0].0,
            Pattern::Ctor(
                "stream_vt_cons".into(),
                vec![Pattern::Var("x".into()), Pattern::Var("rest".into())]
            )
        );
    }

    #[test]
    fn parses_lambda_with_bare_parameter() {
        assert_eq!(
            body_of("fun f(): int = lam x => x + 1"),
            Expr::Lam(
                vec![Param { borrowed: false, name: "x".into(), ty: Ty::Name("_".into()) }],
                None,
                Box::new(Expr::BinOp(BinOp::Add, Box::new(var("x")), Box::new(int(1)))),
            )
        );
    }

    #[test]
    fn parses_lambda_with_unannotated_parameters() {
        assert_eq!(
            body_of("fun f(): int = lam (x0, x1) => x0 + x1"),
            Expr::Lam(
                vec![
                    Param { borrowed: false, name: "x0".into(), ty: Ty::Name("_".into()) },
                    Param { borrowed: false, name: "x1".into(), ty: Ty::Name("_".into()) },
                ],
                None,
                Box::new(Expr::BinOp(BinOp::Add, Box::new(var("x0")), Box::new(var("x1")))),
            )
        );
    }

    #[test]
    fn parses_unary_negation_with_tilde_and_dash() {
        assert_eq!(body_of("fun f(x: int): int = ~x"), Expr::UnaryNeg(Box::new(var("x"))));
        assert_eq!(body_of("fun f(x: int): int = -x"), Expr::UnaryNeg(Box::new(var("x"))));
        // Unary binds tighter than multiplication.
        assert_eq!(
            body_of("fun f(x: int): int = ~x * 2"),
            Expr::BinOp(BinOp::Mul, Box::new(Expr::UnaryNeg(Box::new(var("x")))), Box::new(int(2)))
        );
    }

    #[test]
    fn parses_calls_and_chained_calls() {
        assert_eq!(
            body_of("fun f(): int = fact(n - 1)"),
            Expr::Call(Box::new(var("fact")), vec![Expr::BinOp(BinOp::Sub, Box::new(var("n")), Box::new(int(1)))])
        );
        assert_eq!(
            body_of("fun f(): int = g(1)(2)"),
            Expr::Call(Box::new(Expr::Call(Box::new(var("g")), vec![int(1)])), vec![int(2)])
        );
    }

    #[test]
    fn parses_macro_calls_after_an_identifier() {
        assert_eq!(
            impl_body("implement main0() = println!(\"x = \", 1)"),
            Expr::MacroCall("println!".into(), vec![Expr::StrLit("x = ".into()), int(1)])
        );
    }

    #[test]
    fn parses_function_types() {
        // A higher-order parameter type: (int, int) -> int   and   int -> int
        let p = Parser::parse(
            "fun apply(f: (int, int) -> int, x: int): int = f(x, x)",
        ).expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(
            f.params[0].ty,
            Ty::Fun(vec![Ty::Name("int".into()), Ty::Name("int".into())], Box::new(Ty::Name("int".into())))
        );

        let p = Parser::parse("fun id(f: int -> int): int = f(1)").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(
            f.params[0].ty,
            Ty::Fun(vec![Ty::Name("int".into())], Box::new(Ty::Name("int".into())))
        );
    }

    #[test]
    fn parses_type_applications() {
        // A name with no special meaning: `list` is the prelude's, and
        // would be canonicalised.
        let p = Parser::parse("fun len(xs: bag(a)): int = 0").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(
            f.params[0].ty,
            Ty::App("bag".into(), vec![Ty::Name("a".into())])
        );

        let p = Parser::parse("datatype tree = leaf | node(tree, tree)").expect("parse");
        let Def::Datatype(d) = &p.defs()[0] else { panic!() };
        assert_eq!(d.ctors[1].fields[0], Ty::Name("tree".into()));
    }

    #[test]
    fn type_application_insists_on_matching_parens() {
        let err = expect_err("fun len(xs: list(a): int = 0");
        assert!(err.message().contains(")"), "{}", err);
    }

    // --- strings ---------------------------------------------------

    #[test]
    fn decodes_string_escapes_at_parse_time() {
        let p = Parser::parse("fun f(): string = \"a\\nb\"").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.body, Expr::StrLit("a\nb".into()));

        let p = Parser::parse("fun f(): string = \"q\\\"w\"").expect("parse");
        let Def::Fun(f) = &p.defs()[0] else { panic!() };
        assert_eq!(f.body, Expr::StrLit("q\"w".into()));
    }

    #[test]
    fn unknown_escape_sequences_are_errors() {
        let err = expect_err("fun f(): string = \"a\\qz\"");
        assert!(err.message().contains("escape"), "{}", err);
    }

    // --- errors ----------------------------------------------------

    #[test]
    fn missing_type_annotation_is_an_error() {
        let err = expect_err("fun f(x) = x");
        assert!(err.message().contains("type"), "{}", err);
    }

    #[test]
    fn termination_metrics_are_skipped() {
        // `.<x>.` proves the recursion terminates — a promise to the ATS
        // type checker with no bearing on what we emit.
        assert_eq!(body_of("fun f(x: int): int .<x>. = x"), Expr::Var("x".into()));
    }

    #[test]
    fn template_parameters_are_skipped() {
        // `{a:type}` constrains the static language, which this compiler
        // does not check; the function underneath it parses normally.
        assert_eq!(body_of("fun f{a:type}(x: int): int = x"), Expr::Var("x".into()));
    }

    #[test]
    fn dangling_constructor_call_is_an_error() {
        let err = expect_err("datatype t = a | ");
        assert!(err.message().contains("constructor"), "{}", err);
    }

    #[test]
    fn truncated_inputs_yield_errors_not_panics() {
        for src in ["fun f(", "fun f(): int =", "fun f(): int = 1 +", "implement main0(", "let x = 1 in 2"] {
            let err = expect_err(src);
            assert_eq!(err.kind(), ats2_domain::errors::ErrorKind::Parse, "src: {src}");
        }
    }

    #[test]
    fn empty_token_stream_is_rejected() {
        let err = expect_err_from_tokens(&[]);
        assert!(err.message().contains("empty"), "{}", err);
    }

    fn expect_err_from_tokens(tokens: &[Token]) -> CompileError {
        Parser::parse_tokens(tokens).expect_err("should fail").into_iter().next().expect("at least one error")
    }

    // --- integration: a realistic mini-program --------------------

    #[test]
    fn parses_a_realistic_program() {
        let src = "datatype list(a) = nil | cons(a, list(a))\n\nfun len(xs: list(a)): int = 0\n\nimplement main0() = { val xs = nil; println!(\"ok\") }\n";
        let p = Parser::parse(src).expect("parse");
        assert_eq!(p.defs().len(), 3);
        assert!(matches!(p.defs()[0], Def::Datatype(_)));
        assert!(matches!(p.defs()[1], Def::Fun(_)));
        assert!(matches!(p.defs()[2], Def::Implement(_)));
    }
}
