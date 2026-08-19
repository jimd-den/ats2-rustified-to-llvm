use std::collections::HashMap;

use ats2_domain::ast::{BinOp, Def, Expr, Param, Pattern, Program, Ty};
use ats2_domain::errors::CompileError;

/// A stateless emitter: `emit` is a pure function of the program.
pub struct LlvmIrEmitter;

impl LlvmIrEmitter {
    /// Lower a program to textual LLVM IR.
    pub fn emit(program: &Program) -> Result<String, CompileError> {
        // Two source-level constructs have no counterpart in LLVM and are
        // removed before anything else looks at the program.  Templates go
        // first: expanding one produces ordinary functions, and those may
        // themselves contain the nested functions lifting deals with.
        // The prelude supplies the declarations every ATS program assumes
        // it has.  It comes first so that inference and expansion see one
        // program, with no notion of where a declaration came from.
        let program = &with_prelude(program)?;
        // Naming the instance a bare template call means needs the types
        // of its arguments, so inference runs before expansion.
        let program = &crate::infer::Inferencer::resolve(program)?;
        let program = &crate::mono::Monomorphiser::expand(program)?;
        let program = &crate::lift::Lifter::lift(program)?;
        let registry = registry_of(program)?;
        let mut module = ModuleBuilder::new();
        for def in &program.defs {
            match def {
                Def::Fun(f) => emit_function(f, &registry, &mut module)?,
                Def::Implement(im) if im.name == "main0" || im.name == "main" => {
                    // The initializers run first, in the order they were
                    // written, so a value may be defined in terms of one
                    // above it.
                    let inits: Vec<&ats2_domain::ast::ValDef> = program
                        .defs
                        .iter()
                        .filter_map(|d| match d {
                            Def::Val(v) => Some(v),
                            _ => None,
                        })
                        .collect();
                    emit_main(im, &inits, &registry, &mut module)?
                }
                // A template hole is inlined where it is used, so it
                // emits no function of its own.
                Def::Implement(im) if im.name.contains('$') => {}
                // An `implement` of a declared function is that function.
                Def::Implement(im) => {
                    let sig = registry.fns[&im.name].clone();
                    let params = im
                        .params
                        .iter()
                        .zip(&sig.params)
                        .map(|(p, ty)| Param { name: p.name.clone(), ty: ty_for(*ty) })
                        .collect();
                    let f = ats2_domain::ast::FunDef {
                        ty_params: im.ty_params.clone(),
                        // An `implement` inherits the declaration's
                        // quantifiers; nothing here re-states them.
                        universals: vec![],
                        existentials: vec![],
                        name: im.name.clone(),
                        params,
                        ret: im.ret.clone().unwrap_or_else(|| ty_for(sig.ret)),
                        body: im.body.clone(),
                    };
                    emit_function(&f, &registry, &mut module)?
                }
                Def::Datatype(d) => module.lines.push(format!("; datatype {}", d.name)),
                // A constant is substituted at every use site, so it
                // contributes a comment and nothing else.
                Def::Const(c) => module.lines.push(format!("; #define {}", c.name)),
                // A declaration promises a definition elsewhere; only the
                // definition emits anything.
                Def::Extern(d) => module.lines.push(format!("; extern {}", d.name)),
                Def::Overload { op, func } => module.lines.push(format!("; overload {op} with {func}")),
                // The storage is declared here; the value is computed in
                // `main`, in the order the program wrote them.
                Def::Val(v) if v.name.starts_with(crate::parser::TOPLEVEL_STATEMENT) => {}
                Def::Val(v) => {
                    let ty = registry.globals[&v.name];
                    module.globals.push(format!(
                        "@{} = internal global {} {}",
                        sanitize(&v.name),
                        llvm_ty_str(ty),
                        zero_literal(ty)
                    ));
                }
            }
        }
        Ok(module.render())
    }
}

/// Prepend the prelude declarations the program did not make for itself.
///
/// A program that declares its own `list0` keeps it: the prelude fills
/// gaps rather than shadowing.  Anything unused is dropped later, since
/// datatypes are only instantiated on demand.
fn with_prelude(program: &Program) -> Result<Program, CompileError> {
    let prelude = crate::parser::Parser::parse(crate::prelude::PRELUDE_SOURCE)
        .map_err(|e| CompileError::emit(format!("the built-in prelude does not parse: {}", e[0])))?;

    // A name the program defines for itself is the program's; the prelude
    // only fills gaps.
    //
    // An `implement` does not define a name — it supplies a *body* for
    // one declared elsewhere, and that elsewhere is often the prelude.
    // Counting it here would take the declaration away and leave the
    // body with nothing to be the body of, which is exactly what a
    // program adding its own `fprint_val<t>` does.
    let own: std::collections::HashSet<String> = program
        .defs
        .iter()
        .filter(|d| !matches!(d, Def::Implement(_)))
        .filter_map(def_name)
        .collect();

    // Which prelude definitions are actually wanted?  Start from the names
    // the program mentions, and keep going: a prelude function may call
    // another, and `fileref_get_lines_stringlst` needs the list datatype
    // that only it mentions.  The fixpoint is what keeps an unused prelude
    // from costing anything.
    let mut wanted: std::collections::HashSet<String> = std::collections::HashSet::new();
    collect_names(&program.defs, &mut wanted);
    loop {
        let mut added = false;
        for def in &prelude.defs {
            let Some(name) = def_name(def) else { continue };
            if own.contains(&name) || !wanted.contains(&name) {
                continue;
            }
            let before = wanted.len();
            collect_names(std::slice::from_ref(def), &mut wanted);
            if wanted.len() != before {
                added = true;
            }
        }
        if !added {
            break;
        }
    }

    let mut defs: Vec<Def> = prelude
        .defs
        .iter()
        .filter(|d| match def_name(d) {
            // A datatype is always available: it emits nothing unless a
            // program actually instantiates it.
            None => true,
            Some(name) => {
                !own.contains(&name)
                    && (wanted.contains(&name) || matches!(d, Def::Datatype(_)))
            }
        })
        .cloned()
        .collect();
    defs.extend(program.defs.iter().cloned());
    Ok(Program::new(defs))
}

/// The type of a top-level `val`'s initializer, where it can be read off
/// the expression without evaluating it.
fn global_type_of(expr: &Expr, registry: &Registry) -> Option<LlvmType> {
    match expr {
        Expr::IntLit(_) => Some(LlvmType::I64),
        Expr::BoolLit(_) => Some(LlvmType::I1),
        Expr::StrLit(_) => Some(LlvmType::I8Ptr),
        Expr::CharLit(_) => Some(LlvmType::I8),
        Expr::FloatLit(_) => Some(LlvmType::F64),
        Expr::UnaryNeg(_) => Some(LlvmType::I64),
        Expr::BinOp(op, l, _) => {
            if op.is_comparison() {
                Some(LlvmType::I1)
            } else {
                global_type_of(l, registry)
            }
        }
        Expr::Var(n) => registry.globals.get(n).copied(),
        // `'{ sing= ..., isemp= ... }` — a record of functions, which is
        // how ATS passes a module around.  Its type is read off its
        // fields, in the order they are written.
        Expr::RecordLit(fields) => {
            let parts: Option<Vec<(String, LlvmType)>> = fields
                .iter()
                .map(|(n, v)| Some((n.clone(), global_type_of(v, registry)?)))
                .collect();
            Some(LlvmType::Record(registry.intern_record(parts?)))
        }
        // `setmod_int.sing` — one field of a record global.
        Expr::Field(base, name) => {
            let LlvmType::Record(index) = global_type_of(base, registry)? else { return None };
            registry.record_fields(index).into_iter().find(|(n, _)| n == name).map(|(_, t)| t)
        }
        Expr::Call(callee, args) => match &**callee {
            // `setmod_int.sing (0)` — applying a field means the type it
            // returns, which its closure signature says.
            Expr::Field(..) => match global_type_of(callee, registry)? {
                LlvmType::Closure(i) => Some(registry.closure_sig(i).ret),
                _ => None,
            },
            Expr::Var(n) | Expr::Inst(n, _) => {
                if matches!(n.as_str(), "ref" | "ref_make_elt" | "refc_make_elt") {
                    // A fresh cell holding the argument: its type is the
                    // one-slot tuple of the argument's type.
                    return global_type_of(args.first()?, registry)
                        .map(|t| LlvmType::Tuple(registry.intern_tuple(vec![t])));
                }
                if n == "ref_make_viewptr" {
                    // `ref_make_viewptr (pf | addr@ x)` hands back the cell
                    // `x` already is, so it has exactly `x`'s type.
                    return match args.first()? {
                        Expr::Call(c, a) if matches!(&**c, Expr::Var(m) if m == "addr@" || m == "view@" || m == "ptrof") => {
                            global_type_of(a.first()?, registry)
                        }
                        a => global_type_of(a, registry).map(|t| LlvmType::Tuple(registry.intern_tuple(vec![t]))),
                    };
                }
                registry.fns.get(n).map(|s| s.ret)
            }
            _ => None,
        },
        Expr::Lam(params, Some(ret), _) => {
            let ps = params
                .iter()
                .map(|p| llvm_type_in(&p.ty, registry))
                .collect::<Result<Vec<_>, _>>()
                .ok()?;
            let r = llvm_type_in(ret, registry).ok()?;
            Some(LlvmType::Closure(registry.intern_closure(FnSig { params: ps, ret: r })))
        }
        _ => None,
    }
}

/// The bit pattern a cell of this type starts out holding.
///
/// A global holds it before its initializer runs, and an uninitialized
/// `var` holds it until its first write.  Nothing observes either —
/// `main` writes every global before the program's own code runs, and
/// ATS's type system is what stops a `var` being read too early — but
/// LLVM requires a value, and the representation's own nothing is the
/// honest one.
fn zero_literal(ty: LlvmType) -> &'static str {
    match ty {
        LlvmType::F64 => "0.0",
        LlvmType::I1 => "false",
        LlvmType::I8Ptr | LlvmType::Argv | LlvmType::FileRef | LlvmType::Data(_)
        | LlvmType::Tuple(_) | LlvmType::Array(_) | LlvmType::Closure(_)
        | LlvmType::Lazy(_) | LlvmType::Record(_) => "null",
        _ => "0",
    }
}

/// The name a definition introduces, if it introduces one.
fn def_name(def: &Def) -> Option<String> {
    match def {
        Def::Fun(f) => Some(f.name.clone()),
        Def::Extern(d) => Some(d.name.clone()),
        Def::Implement(im) => Some(im.name.clone()),
        Def::Datatype(d) => Some(d.name.clone()),
        Def::Const(c) => Some(c.name.clone()),
        Def::Val(v) => Some(v.name.clone()),
        Def::Overload { .. } => None,
    }
}

/// Every name these definitions mention, in types or in code.
fn collect_names(defs: &[Def], out: &mut std::collections::HashSet<String>) {
    for def in defs {
        match def {
            Def::Fun(f) => {
                for p in &f.params {
                    collect_type_names(&p.ty, out);
                }
                collect_type_names(&f.ret, out);
                collect_expr_names(&f.body, out);
            }
            Def::Implement(im) => {
                for p in &im.params {
                    collect_type_names(&p.ty, out);
                }
                collect_expr_names(&im.body, out);
            }
            Def::Extern(d) => {
                for p in &d.params {
                    collect_type_names(&p.ty, out);
                }
                collect_type_names(&d.ret, out);
            }
            Def::Datatype(d) => {
                for c in &d.ctors {
                    out.insert(c.name.clone());
                    for f in &c.fields {
                        collect_type_names(f, out);
                    }
                }
            }
            Def::Const(c) => collect_expr_names(&c.value, out),
            Def::Val(v) => {
                if let Some(t) = &v.ty {
                    collect_type_names(t, out);
                }
                collect_expr_names(&v.value, out);
            }
            Def::Overload { func, .. } => {
                out.insert(func.clone());
            }
        }
    }
}

fn collect_type_names(ty: &Ty, out: &mut std::collections::HashSet<String>) {
    match ty {
        Ty::Name(n) => {
            out.insert(n.clone());
        }
        Ty::App(n, args) => {
            out.insert(n.clone());
            for a in args {
                collect_type_names(a, out);
            }
        }
        Ty::Tuple(items) => items.iter().for_each(|i| collect_type_names(i, out)),
        Ty::Record(fields) => fields.iter().for_each(|(_, t)| collect_type_names(t, out)),
        Ty::Fun(ps, r) => {
            ps.iter().for_each(|p| collect_type_names(p, out));
            collect_type_names(r, out);
        }
        Ty::Index(base, _) => collect_type_names(base, out),
    }
}

fn collect_expr_names(expr: &Expr, out: &mut std::collections::HashSet<String>) {
    fn go(e: &Expr, out: &mut std::collections::HashSet<String>) {
        collect_expr_names(e, out);
    }
    match expr {
        Expr::Var(n) => {
            out.insert(n.clone());
        }
        Expr::Inst(n, tys) => {
            out.insert(n.clone());
            for t in tys {
                collect_type_names(t, out);
            }
        }
        Expr::UnaryNeg(e) => go(e, out),
        Expr::BinOp(_, l, r) => {
            go(l, out);
            go(r, out);
        }
        Expr::Index(a, b) => {
            go(a, out);
            go(b, out);
        }
        Expr::Proj(a, _) | Expr::Deref(a) => go(a, out),
        Expr::Store(p, v) => {
            go(p, out);
            go(v, out);
        }
        Expr::Assign(n, v) => {
            out.insert(n.clone());
            go(v, out);
        }
        Expr::While(a, b) => {
            go(a, out);
            go(b, out);
        }
        Expr::For(a, b, c, d) => {
            go(a, out);
            go(b, out);
            go(c, out);
            go(d, out);
        }
        Expr::Call(c, args) => {
            go(c, out);
            args.iter().for_each(|a| go(a, out));
        }
        Expr::MacroCall(_, args) | Expr::TupleLit(args) => args.iter().for_each(|a| go(a, out)),
        Expr::IfThenElse(a, b, c) => {
            go(a, out);
            go(b, out);
            go(c, out);
        }
        Expr::Lam(_, _, b) => go(b, out),
        Expr::Let(binds, body) => {
            for b in binds {
                if let Some(t) = &b.ty {
                    collect_type_names(t, out);
                }
                collect_expr_names(&b.value, out);
            }
            collect_expr_names(body, out);
        }
        Expr::Case(s, arms) => {
            collect_expr_names(s, out);
            for (p, b) in arms {
                collect_pattern_names(p, out);
                collect_expr_names(b, out);
            }
        }
        Expr::LetFun(funs, body) => {
            for f in funs {
                collect_expr_names(&f.body, out);
                collect_type_names(&f.ret, out);
            }
            collect_expr_names(body, out);
        }
        _ => {}
    }
}

fn collect_pattern_names(pattern: &Pattern, out: &mut std::collections::HashSet<String>) {
    match pattern {
        Pattern::Ctor(n, fields) => {
            out.insert(n.clone());
            fields.iter().for_each(|f| collect_pattern_names(f, out));
        }
        Pattern::Tuple(items) => items.iter().for_each(|i| collect_pattern_names(i, out)),
        Pattern::InPlace(inner) => collect_pattern_names(inner, out),
        _ => {}
    }
}

/// The small set of LLVM types the subset lowers to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LlvmType {
    I64,
    I1,
    I32,
    I8Ptr,
    /// `char **` — the argument vector handed to `main`.  It is a
    /// distinct type from `string` so that indexing can be allowed on one
    /// and refused on the other, even though both are `ptr` in the IR.
    Argv,
    /// `FILEref` — a C `FILE *`.  Like `argv` it is a `ptr` under opaque
    /// pointers, and like `argv` it is kept distinct so the operations
    /// that apply to a stream can be told from those that do not.
    FileRef,
    /// `double` — a 64-bit float.  It has its own arithmetic and its own
    /// comparisons, so it cannot share the integer paths.
    F64,
    /// `char` — one byte.  It is kept apart from `int` because ATS does:
    /// a character is not a small number, and mixing them silently is the
    /// kind of thing a type system exists to stop.
    I8,
    /// A closure: a function together with the values it captured,
    /// identified by its index in the registry's closure table.
    ///
    /// It is a pointer to a record whose first word is the code and whose
    /// remaining words are the captures.  Calling one is therefore a load
    /// and an indirect call — the price of a function that carries part of
    /// its scope around with it.
    Closure(usize),
    /// A tuple, identified by its index in the registry's tuple table.
    ///
    /// Like a datatype value it is a pointer to a record of words, but
    /// with no tag: a tuple has only one shape, so there is nothing to
    /// discriminate.
    Tuple(usize),
    /// `arrayptr(t)` / `@[t][n]` — a pointer to a run of cells of one
    /// type, identified by that type's index in the registry's element
    /// table.
    ///
    /// Unlike a tuple, an array's length is not part of its shape: the
    /// length is a *static* index, erased before emission, so the value
    /// the emitter sees is only ever a pointer.  This is exactly why
    /// bounds are checked by the constraint checker rather than at run
    /// time — ATS spends the length on the proof, not on the machine.
    Array(usize),
    /// A value of a user-declared `datatype`, identified by its index in
    /// the registry's datatype table.
    ///
    /// Every such value is a pointer to a record whose first word is the
    /// constructor's tag and whose remaining words are its fields.  One
    /// uniform shape means `case` can read a tag without knowing which
    /// constructor built the value — which is the whole point.
    Data(usize),
    /// A record: a tuple whose slots have names, identified by its index
    /// in the registry's record table.
    ///
    /// Its representation is a tuple's — a pointer to a run of words —
    /// and everything that separates the two is in the type: which name
    /// sits at which slot, and the fact that two records agreeing on
    /// every type but disagreeing on a name are different types.
    Record(usize),
    /// A suspended value — what ATS spells `stream`, `stream_vt` or
    /// `lazy` — identified by the type it produces once forced.
    ///
    /// It is a pointer to two words: the thunk, and the answer.  The
    /// thunk is nulled when it runs, which is both how the answer is
    /// marked present and why it can only run once.  That "only once" is
    /// not an optimisation: Erathosthenes' sieve builds a filter over a
    /// filter over a filter, and re-running any of them re-runs all of
    /// them beneath it.  A stream that forgets is a stream that never
    /// finishes.
    Lazy(usize),
    /// The type of an expression that never produces a value because
    /// control never comes back — `exit(1)`, and anything ending in it.
    ///
    /// It is the *bottom* type: compatible with every other, because a
    /// branch that never arrives can never disagree about what it
    /// arrived with.  Keeping it in the lattice is what lets `if c then n
    /// else exit(1)` typecheck as an `int`.
    Never,
    /// `void` — the type of a statement.  A void `FnValue` carries an
    /// empty register, because there is no SSA name to carry: nothing was
    /// produced.  Keeping it in the same lattice as the other types lets
    /// `val () = ...`, void-returning `fun`s, and an empty `let` body all
    /// flow through the ordinary expression path.
    Void,
}

/// A function's signature: parameter types and return type.
#[derive(Debug, Clone)]
struct FnSig {
    params: Vec<LlvmType>,
    ret: LlvmType,
}

impl Registry {
    /// The index of a tuple shape, adding it if it is new.
    ///
    /// Shapes are interned so that two tuples with the same components
    /// share a type — `(int, int)` written twice is one type, and code
    /// that returns one can be passed to code that takes the other.
    fn intern_tuple(&self, parts: Vec<LlvmType>) -> usize {
        let mut tuples = self.tuples.borrow_mut();
        if let Some(i) = tuples.iter().position(|t| *t == parts) {
            return i;
        }
        tuples.push(parts);
        tuples.len() - 1
    }

    /// The components of a tuple shape.
    fn tuple_parts(&self, index: usize) -> Vec<LlvmType> {
        self.tuples.borrow()[index].clone()
    }

    /// The index of an array element type, adding it if it is new.
    fn intern_array(&self, elem: LlvmType) -> usize {
        let mut arrays = self.arrays.borrow_mut();
        if let Some(i) = arrays.iter().position(|t| *t == elem) {
            return i;
        }
        arrays.push(elem);
        arrays.len() - 1
    }

    /// What one cell of an array holds.
    fn array_elem(&self, index: usize) -> LlvmType {
        self.arrays.borrow()[index]
    }

    /// The index of a record shape, adding it if it is new.
    fn intern_record(&self, fields: Vec<(String, LlvmType)>) -> usize {
        let mut records = self.records.borrow_mut();
        if let Some(i) = records.iter().position(|r| *r == fields) {
            return i;
        }
        records.push(fields);
        records.len() - 1
    }

    /// A record's fields, in slot order.
    fn record_fields(&self, index: usize) -> Vec<(String, LlvmType)> {
        self.records.borrow()[index].clone()
    }

    /// The index of a forced type, adding it if it is new.
    fn intern_lazy(&self, forced: LlvmType) -> usize {
        let mut lazies = self.lazies.borrow_mut();
        if let Some(i) = lazies.iter().position(|t| *t == forced) {
            return i;
        }
        lazies.push(forced);
        lazies.len() - 1
    }

    /// What forcing a suspended value yields.
    fn lazy_forced(&self, index: usize) -> LlvmType {
        self.lazies.borrow()[index]
    }

    /// The index of a closure signature, adding it if it is new.
    fn intern_closure(&self, sig: FnSig) -> usize {
        let mut closures = self.closures.borrow_mut();
        if let Some(i) = closures.iter().position(|c| c.params == sig.params && c.ret == sig.ret) {
            return i;
        }
        closures.push(sig);
        closures.len() - 1
    }

    /// The signature behind a closure type.
    fn closure_sig(&self, index: usize) -> FnSig {
        self.closures.borrow()[index].clone()
    }
}

/// Everything an expression needs to know about the rest of the program:
/// the signature of every function (so recursion and mutual recursion
/// resolve regardless of order), and the value of every `#define`
/// constant (which is substituted, not stored).
#[derive(Debug, Default)]
struct Registry {
    fns: HashMap<String, FnSig>,
    consts: HashMap<String, Expr>,
    /// Declared datatypes, in declaration order; `LlvmType::Data` indexes
    /// into this.
    datatypes: Vec<String>,
    /// Top-level `val`s: name → the type of the global holding it.
    ///
    /// Their *values* are not known here — a global's initializer may be
    /// any expression — so each is a piece of storage written once, before
    /// `main` runs.
    globals: HashMap<String, LlvmType>,
    /// Operators the program has given a function to fall back on.
    overloads: HashMap<String, String>,
    /// The distinct closure signatures the program uses.
    closures: std::cell::RefCell<Vec<FnSig>>,
    /// The distinct tuple shapes the program uses.
    tuples: std::cell::RefCell<Vec<Vec<LlvmType>>>,
    /// The distinct array element types the program uses.
    arrays: std::cell::RefCell<Vec<LlvmType>>,
    /// The distinct types a suspended value can produce once forced.
    lazies: std::cell::RefCell<Vec<LlvmType>>,
    /// The distinct record shapes the program uses: for each, the fields
    /// in slot order.
    records: std::cell::RefCell<Vec<Vec<(String, LlvmType)>>>,
    /// Every constructor of every datatype, by name.
    ///
    /// A name may belong to several: two instances of one parameterized
    /// datatype declare the same constructors, so `None` can build an
    /// `opt$int` or an `opt$string`.  Which one is meant depends on the
    /// types around it, so all the candidates are kept and the choice is
    /// made at the use site.
    ctors: HashMap<String, Vec<CtorInfo>>,
    /// The functions this program actually defines, as opposed to merely
    /// declaring.
    ///
    /// An `extern fun ... = "ext#"` says the definition lives outside
    /// ATS — often in the `%{ ... %}` block of C this compiler skips.
    /// Declaring it must not stop the compiler answering it with a shim,
    /// and when nothing answers it, a C declaration is what lets the
    /// program call out at all.  Either way, a declaration alone is not
    /// a definition to call.
    defined: std::collections::HashSet<String>,
    /// Which of a function's parameters it writes back through.
    ///
    /// `r: &int` where the body says `r := 7` is an *out* parameter: the
    /// write must land in the caller's cell, so the parameter is that
    /// cell's address.  A `&` the body only reads needs no indirection —
    /// and an aggregate is its own storage, so writes *into* one land
    /// without any of this.  Assignment to the parameter is therefore
    /// the thing that decides, and it is decided from the body rather
    /// than from the annotation, which cannot be trusted to be there.
    by_ref: HashMap<String, Vec<bool>>,
    /// Template *holes*: `implement array_foreach$fwork<a><env> (x, e) =
    /// ...`, by name.
    ///
    /// A hole is not a function.  ATS's `$`-suffixed names are the parts
    /// of a template a caller supplies, and the library routine that
    /// uses one is specialised around it — which is why they are kept as
    /// syntax and inlined at the use site rather than emitted and
    /// called.  Inlining is also what makes `env := ...` inside a hole
    /// write the caller's own cell, which is the by-reference behaviour
    /// the library's signature promises and a call could not give.
    holes: HashMap<String, ats2_domain::ast::ImplementDef>,
}

/// What the emitter needs to know about one constructor.
#[derive(Debug, Clone)]
struct CtorInfo {
    /// Which datatype it builds (an index into `Registry::datatypes`).
    datatype: usize,
    /// Its tag: the position it was declared in.
    tag: i64,
    /// The types of its fields, in order.
    fields: Vec<LlvmType>,
    /// The widest constructor of the same datatype.
    ///
    /// Every value reserves that much, so reading field `i` of *any*
    /// constructor lands inside the value.  That is what makes a nested
    /// pattern safe to lay out as a sequence of loads and tests: the load
    /// happens before the tag is known to match, and it must not run off
    /// the end of a narrower record.
    width: usize,
}

/// Where a print macro sends its bytes.
///
/// The two standard destinations are named rather than computed, because
/// `printf` needs no stream operand at all and that is the common case.
/// `Ref` covers a stream the program worked out for itself — the `out` a
/// function was handed, a file it opened.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Stream {
    Stdout,
    Stderr,
    Ref(String),
}

/// An SSA value produced by an expression: its register text and its type.
#[derive(Debug, Clone)]
struct FnValue {
    reg: String,
    ty: LlvmType,
}

/// Collects every function's signature up front, so recursive and
/// mutually-recursive calls resolve regardless of definition order.
fn registry_of(program: &Program) -> Result<Registry, CompileError> {
    let mut registry = Registry::default();
    // Datatypes come first: a function's signature may mention one, and a
    // datatype may mention itself (a list holds a list), so every name
    // must be known before any field type is resolved.
    for def in &program.defs {
        if let Def::Datatype(d) = def {
            if registry.datatypes.contains(&d.name) {
                return Err(CompileError::emit(format!("datatype `{}` is declared twice", d.name)));
            }
            registry.datatypes.push(d.name.clone());
        }
    }
    for def in &program.defs {
        if let Def::Datatype(d) = def {
            let index = registry.datatypes.iter().position(|n| n == &d.name).expect("just added");
            let widest = d.ctors.iter().map(|c| c.fields.len()).max().unwrap_or(0);
            let _ = widest;
            for (tag, ctor) in d.ctors.iter().enumerate() {
                let fields = ctor
                    .fields
                    .iter()
                    .map(|f| llvm_type_in(f, &registry))
                    .collect::<Result<Vec<_>, _>>()?;
                let candidates = registry.ctors.entry(ctor.name.clone()).or_default();
                if candidates.iter().any(|c| c.datatype == index) {
                    return Err(CompileError::emit(format!(
                        "constructor `{}` is declared twice in `{}`",
                        ctor.name, d.name
                    )));
                }
                candidates.push(CtorInfo { datatype: index, tag: tag as i64, fields, width: 0 });
            }
            // Now that every constructor is known, give them all the
            // width of the widest.
            let widest = d.ctors.iter().map(|c| c.fields.len()).max().unwrap_or(0);
            for ctor in &d.ctors {
                if let Some(cands) = registry.ctors.get_mut(&ctor.name) {
                    for c in cands.iter_mut().filter(|c| c.datatype == index) {
                        c.width = widest;
                    }
                }
            }
        }
    }
    // `nil`/`cons` are the shorthands ATS programs write for the
    // prelude's list constructors.  They are registered as further names
    // for the same constructors, and only where the program has not used
    // the name for something of its own.
    for (alias, declared) in crate::prelude::CTOR_ALIASES {
        if registry.ctors.contains_key(*alias) {
            continue;
        }
        if let Some(infos) = registry.ctors.get(*declared).cloned() {
            registry.ctors.insert((*alias).to_string(), infos);
        }
    }
    for def in &program.defs {
        match def {
            Def::Fun(f) => {
                let params = f.params.iter().map(|p| llvm_type_in(&p.ty, &registry)).collect::<Result<Vec<_>, _>>()?;
                // `fun f (m: int) = lam (n: int): int => ...` writes no
                // return type.  The lambda's own annotations give it, and
                // they must be read *before* the body is emitted, because
                // the body may call `f` again.
                let declared = match (&f.ret, &f.body) {
                    (Ty::Name(n), Expr::Lam(ps, Some(r), _)) if n == "_" => {
                        Ty::Fun(ps.iter().map(|p| p.ty.clone()).collect(), Box::new(r.clone()))
                    }
                    (other, _) => other.clone(),
                };
                let ret = llvm_type_in(&declared, &registry)?;
                registry.by_ref.insert(f.name.clone(), assigned_parameters(&f.params, &f.body));
                registry.defined.insert(f.name.clone());
                registry.fns.insert(f.name.clone(), FnSig { params, ret });
            }
            // A template hole fills a name the *library* declared, not
            // one this program did, so there is no declaration here to
            // check it against.
            Def::Implement(im) if im.name.contains('$') => {
                registry.holes.insert(im.name.clone(), im.clone());
            }
            Def::Implement(im) if im.name != "main0" && im.name != "main" => {
                // Any other name must have been declared: an `implement`
                // fills in a signature stated elsewhere, and without the
                // declaration there is nothing to say what its untyped
                // parameters are.
                let Some(sig) = registry.fns.get(&im.name).cloned() else {
                    return Err(CompileError::emit(format!(
                        "`{}` is implemented but never declared; add an `extern fun` for it",
                        im.name
                    )));
                };
                if sig.params.len() != im.params.len() {
                    return Err(CompileError::emit(format!(
                        "`{}` is declared with {} parameter(s) but implemented with {}",
                        im.name,
                        sig.params.len(),
                        im.params.len()
                    )));
                }
                registry.defined.insert(im.name.clone());
                registry
                    .by_ref
                    .insert(im.name.clone(), assigned_parameters(&im.params, &im.body));
            }
            Def::Implement(im) => {
                // ATS has two entry points: `main0`, whose result is
                // discarded, and `main`, whose `int` result is the
                // process's exit code.
                // `main0 ()` or `main0 (argc, argv)` — nothing else.
                let params = match im.params.len() {
                    0 => vec![],
                    2 => vec![LlvmType::I64, LlvmType::Argv],
                    _ => return Err(CompileError::emit("main0 takes either no parameters or `(argc, argv)`")),
                };
                registry.fns.insert(im.name.clone(), FnSig { params, ret: LlvmType::I32 });
            }
            Def::Const(c) => {
                registry.consts.insert(c.name.clone(), c.value.clone());
            }
            // An `extern` states the signature an `implement` will fill
            // in, so the definition can leave its parameters untyped.
            // A template's declaration mentions type *holes*, which have
            // no LLVM type; monomorphisation has already replaced every
            // use of it with an instance.
            Def::Overload { op, func } => {
                registry.overloads.insert(op.clone(), func.clone());
            }
            // A top-level statement is run, not stored: it has no type
            // to declare storage for and no name anything can read.
            Def::Val(v) if v.name.starts_with(crate::parser::TOPLEVEL_STATEMENT) => {}
            Def::Val(v) => {
                let ty = match &v.ty {
                    Some(t) => llvm_type_in(t, &registry)?,
                    // With no annotation the type comes from the value.
                    // Only the shapes that need no context are read here;
                    // anything else must be written down.
                    None => global_type_of(&v.value, &registry).ok_or_else(|| {
                        CompileError::emit(format!(
                            "cannot tell what type `{}` has; give it an annotation",
                            v.name
                        ))
                    })?,
                };
                registry.globals.insert(v.name.clone(), ty);
            }
            Def::Extern(d) if !d.ty_params.is_empty() => {}
            Def::Extern(d) => {
                let params = d.params.iter().map(|p| llvm_type_in(&p.ty, &registry)).collect::<Result<Vec<_>, _>>()?;
                let ret = llvm_type_in(&d.ret, &registry)?;
                registry.fns.insert(d.name.clone(), FnSig { params, ret });
            }
            Def::Datatype(_) => {}
        }
    }
    Ok(registry)
}

/// As `llvm_type_of`, but also resolving the datatypes declared here.
fn llvm_type_in(ty: &Ty, registry: &Registry) -> Result<LlvmType, CompileError> {
    // `(int) -> int` is a function *value*, which in this subset means a
    // closure: nothing else can produce one.
    if let Ty::Fun(params, ret) = ty {
        let params = params.iter().map(|p| llvm_type_in(p, registry)).collect::<Result<Vec<_>, _>>()?;
        let ret = llvm_type_in(ret, registry)?;
        return Ok(LlvmType::Closure(registry.intern_closure(FnSig { params, ret })));
    }
    if let Ty::Record(fields) = ty {
        let parts = fields
            .iter()
            .map(|(n, t)| Ok((n.clone(), llvm_type_in(t, registry)?)))
            .collect::<Result<Vec<_>, CompileError>>()?;
        return Ok(LlvmType::Record(registry.intern_record(parts)));
    }
    if let Ty::Tuple(items) = ty {
        let parts = items.iter().map(|i| llvm_type_in(i, registry)).collect::<Result<Vec<_>, _>>()?;
        return Ok(LlvmType::Tuple(registry.intern_tuple(parts)));
    }
    // `arrayptr(t)`, `array(t, n)`, `@[t][n]` — one name each for the
    // same machine value: a pointer to cells of `t`.  ATS keeps them
    // apart because their *views* differ (who owns the cells, and who
    // may free them), and views are erased here.
    if let Ty::Index(base, _) = ty {
        return llvm_type_in(base, registry);
    }
    if let Ty::App(n, args) = ty {
        if matches!(n.as_str(), "array" | "arrayptr" | "arrszref" | "arrayref") {
            if let Some(elem) = args.first() {
                let elem = llvm_type_in(elem, registry)?;
                return Ok(LlvmType::Array(registry.intern_array(elem)));
            }
        }
        // `$lazy(t)` — the internal type monomorphisation rewrites
        // `stream`, `stream_vt` and `lazy` into.  What it carries is the
        // type it produces once forced, which is the only thing the
        // suspension's users need to agree on.
        if n == crate::mono::LAZY {
            if let Some(forced) = args.first() {
                let forced = llvm_type_in(forced, registry)?;
                return Ok(LlvmType::Lazy(registry.intern_lazy(forced)));
            }
        }
        // `ref(t)` — one cell, which is a one-slot tuple.  Sharing the
        // tuple representation is what makes `!r` and `!r := v` fall out
        // of the slot machinery already written for projections.
        if n == "ref" {
            if let Some(inner) = args.first() {
                let inner = llvm_type_in(inner, registry)?;
                return Ok(LlvmType::Tuple(registry.intern_tuple(vec![inner])));
            }
        }
    }
    let head = match ty {
        Ty::Name(n) => Some(n),
        Ty::App(n, _) => Some(n),
        _ => None,
    };
    if let Some(head) = head {
        if let Some(i) = registry.datatypes.iter().position(|n| n == head) {
            return Ok(LlvmType::Data(i));
        }
    }
    llvm_type_of(ty)
}

/// Map a domain type to an LLVM type, or report it as unsupported.
fn llvm_type_of(ty: &Ty) -> Result<LlvmType, CompileError> {
    match ty {
        // An index is a fact *about* a value, never a part of one, so
        // emission looks straight through it.  This is what ATS itself
        // does: the static language is gone before any code is emitted.
        Ty::Index(base, _) => llvm_type_of(base),
        // `int(n)`, `intGte(0)`, `string(n)` — an *indexed* type.  The
        // index is a static fact (this int equals n, that one is at least
        // zero); it describes no part of the machine value, so the type
        // erases to the base it decorates.  This is what ATS itself does:
        // the static language is gone by the time code is emitted.
        Ty::App(head, args) => match base_type_named(head) {
            Some(base) => Ok(base),
            None => Err(CompileError::emit(format!(
                "type application `{head}` is not supported yet ({} argument(s))",
                args.len()
            ))),
        },
        // `argv` is C's `char **`.  Under opaque pointers every pointer is
        // spelled `ptr`, so it shares a representation with `string` and
        // is told apart only by how it may be used.
        Ty::Name(n) => base_type_named(n)
            .ok_or_else(|| CompileError::emit(format!("unsupported type `{n}` (only int, bool, string)"))),
        Ty::Fun(_, _) => Err(CompileError::emit("higher-order function types are not supported yet")),
        Ty::Tuple(_) => Err(CompileError::emit("tuple types are not supported yet")),
        Ty::Record(_) => Err(CompileError::emit("internal: a record type reached the fallback mapper")),
    }
}

/// How an operator is written, for looking it up among the overloads.
fn operator_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+", BinOp::Sub => "-", BinOp::Mul => "*", BinOp::Div => "/",
        BinOp::Mod => "mod", BinOp::Eq => "=", BinOp::Ne => "<>", BinOp::Lt => "<",
        BinOp::Le => "<=", BinOp::Gt => ">", BinOp::Ge => ">=",
        BinOp::Andalso => "andalso", BinOp::Orelse => "orelse",
    }
}

/// Whether a pattern always matches, so that no later arm can be reached.
fn is_irrefutable(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Wildcard | Pattern::Var(_) => true,
        Pattern::Tuple(items) => items.iter().all(is_irrefutable),
        _ => false,
    }
}

/// Which of these parameters the body assigns to.
fn assigned_parameters(params: &[Param], body: &Expr) -> Vec<bool> {
    let mut written = std::collections::HashSet::new();
    collect_assigned(body, &mut written);
    params.iter().map(|p| written.contains(&p.name)).collect()
}

/// Every name assigned to anywhere in an expression.
fn collect_assigned(expr: &Expr, out: &mut std::collections::HashSet<String>) {
    if let Expr::Assign(name, _) = expr {
        out.insert(name.clone());
    }
    expr.each_subexpr(&mut |e| collect_assigned(e, out));
}

/// Choose which datatype a constructor name refers to.
///
/// With one candidate there is nothing to decide.  With several — the
/// instances of one parameterized datatype — the expected type is what
/// settles it, and when the context supplies none the program is genuinely
/// ambiguous and is told so rather than guessed at.
fn resolve_ctor(name: &str, ty_args: &[Ty], expected: Option<LlvmType>, registry: &Registry) -> Result<CtorInfo, CompileError> {
    let candidates = &registry.ctors[name];
    if let [only] = &candidates[..] {
        return Ok(only.clone());
    }
    // `cons0{list0(int)}(x, xs)` — the braces name the instance
    // directly, which is what a program writes exactly when the context
    // does not settle it.  Monomorphisation has already turned each
    // argument into the name of an instance, so the datatype wanted is
    // spelled the same way its own instance name was built.
    if !ty_args.is_empty() {
        let wanted = instance_name(candidates, ty_args, registry);
        if let Some(found) = wanted.and_then(|w| {
            candidates.iter().find(|c| registry.datatypes[c.datatype] == w)
        }) {
            return Ok(found.clone());
        }
    }
    if let Some(LlvmType::Data(want)) = expected {
        if let Some(found) = candidates.iter().find(|c| c.datatype == want) {
            return Ok(found.clone());
        }
        return Err(CompileError::emit(format!(
            "`{name}` does not build a `{}`",
            registry.datatypes[want]
        )));
    }
    let names: Vec<&str> = candidates.iter().map(|c| registry.datatypes[c.datatype].as_str()).collect();
    Err(CompileError::emit(format!(
        "`{name}` could build any of {}; say which with a type annotation",
        names.join(", ")
    )))
}

/// The instance name `name<args>` would have been mangled to.
///
/// The candidates all come from one parameterized datatype, so the base
/// is whatever precedes the `$` in any of their instance names — that is
/// how monomorphisation built them, and reading it back is what lets an
/// explicit `{...}` pick between them.
fn instance_name(candidates: &[CtorInfo], ty_args: &[Ty], registry: &Registry) -> Option<String> {
    let first = registry.datatypes.get(candidates.first()?.datatype)?;
    let base = first.split('$').next()?;
    let mut out = base.to_string();
    for arg in ty_args {
        let Ty::Name(n) = arg else { return None };
        out.push('$');
        out.push_str(n);
    }
    Some(out)
}

/// A domain type that maps back to this LLVM type.
///
/// Used when an `implement` leaves its parameters unannotated: the types
/// come from the declaration, and the function emitter wants them in the
/// same shape a written annotation would have had.
fn ty_for(t: LlvmType) -> Ty {
    Ty::Name(
        match t {
            LlvmType::I64 | LlvmType::I32 => "int",
            LlvmType::I8 => "char",
            LlvmType::F64 => "double",
            LlvmType::I1 => "bool",
            LlvmType::I8Ptr => "string",
            LlvmType::Argv => "argv",
            LlvmType::FileRef => "FILEref",
            LlvmType::Void | LlvmType::Never => "void",
            // A datatype's name is recovered from the registry by the
            // caller when it matters; this path only needs a placeholder
            // the type mapper will accept.
            LlvmType::Data(_) | LlvmType::Tuple(_) | LlvmType::Array(_)
            | LlvmType::Closure(_) | LlvmType::Lazy(_) | LlvmType::Record(_) => "void",
        }
        .into(),
    )
}

/// The libc global behind an ATS standard-stream name.
fn standard_stream(name: &str) -> Option<&'static str> {
    match name {
        "stdin_ref" => Some("stdin"),
        "stdout_ref" => Some("stdout"),
        "stderr_ref" => Some("stderr"),
        _ => None,
    }
}

/// The C mode string an ATS file-mode name stands for.
fn file_mode(name: &str) -> Option<&'static str> {
    match name {
        "file_mode_r" => Some("r"),
        "file_mode_w" => Some("w"),
        "file_mode_a" => Some("a"),
        "file_mode_rw" => Some("r+"),
        _ => None,
    }
}

/// The base type a name denotes, if it denotes one.
///
/// The `Gt`/`Gte`/`Lt`/`Lte` families are the same machine integer with a
/// bound attached, and `size_t` is how ATS spells a length.
fn base_type_named(name: &str) -> Option<LlvmType> {
    match name {
        // Every integer ATS distinguishes — by width, by signedness, by
        // which static sort tracks it — is one machine word here.  The
        // distinctions are real to its type checker and invisible to a
        // 64-bit target.
        "int" | "intGt" | "intGte" | "intLt" | "intLte" | "nat" | "pos"
        | "size_t" | "sizeGt" | "sizeGte" | "sizeLt" | "sizeLte" | "ssize_t"
        | "uint" | "lint" | "ulint" | "llint" | "ullint" | "sint" | "usint"
        | "Int" | "Nat" | "Uint" | "intmax" | "uintmax" => Some(LlvmType::I64),
        // `ptr` is an address with nothing said about what is at it.
        "ptr" | "ptr0" | "ptr1" | "Ptr" | "Ptr0" | "Ptr1" => Some(LlvmType::I8Ptr),
        // `bytes(n)` is `n` bytes and `b0ytes(n)` the same bytes before
        // anything has been written to them.  The count is static, so a
        // pointer to the first of them is the whole of the value.
        "byte" | "bytes" | "b0ytes" | "b1ytes" => Some(LlvmType::I8Ptr),
        "bool" => Some(LlvmType::I1),
        "char" | "charNZ" => Some(LlvmType::I8),
        "double" | "float" | "ldouble" => Some(LlvmType::F64),
        "string" => Some(LlvmType::I8Ptr),
        // A file mode is the string libc wants: `"r"`, `"w"`, `"a"`.
        "fmode" | "fmode_r" | "fmode_w" | "fmode_a" | "strptr" | "strptr0" | "strptr1"
        | "strnptr" | "Strptr0" | "Strptr1" => Some(LlvmType::I8Ptr),
        "void" => Some(LlvmType::Void),
        "argv" => Some(LlvmType::Argv),
        "FILEref" | "FILEptr" => Some(LlvmType::FileRef),
        _ => None,
    }
}

fn llvm_ty_str(t: LlvmType) -> &'static str {
    match t {
        LlvmType::I64 => "i64",
        LlvmType::I1 => "i1",
        LlvmType::I32 => "i32",
        LlvmType::I8Ptr => "ptr",
        LlvmType::Argv => "ptr",
        LlvmType::FileRef => "ptr",
        LlvmType::F64 => "double",
        LlvmType::I8 => "i8",
        LlvmType::Closure(_) => "ptr",
        LlvmType::Tuple(_) => "ptr",
        LlvmType::Array(_) => "ptr",
        LlvmType::Data(_) => "ptr",
        LlvmType::Lazy(_) => "ptr",
        LlvmType::Record(_) => "ptr",
        // Never reached, so never rendered as an operand type; `void` is
        // the harmless spelling if it ever escapes into a message.
        LlvmType::Never => "void",
        LlvmType::Void => "void",
    }
}

/// Make an ATS name safe to use as an LLVM identifier.
///
/// ATS names may contain `'`, which LLVM does not accept.  `$` is kept:
/// LLVM allows it, and monomorphisation relies on it — `ident$int` cannot
/// collide with any name the program itself could have written, because a
/// source `$` only ever appears inside a template hole.
fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' || c == '$' { c } else { '_' })
        .collect()
}

/// Escape a decoded string for an LLVM `c"..."` constant body: printable
/// ASCII passes through, everything else becomes `\HH` hex escapes.
fn llvm_escape(s: &str) -> String {
    let mut out = String::new();
    for b in s.bytes() {
        match b {
            b'"' => out.push_str("\\22"),
            b'\\' => out.push_str("\\5C"),
            0x20..=0x7e => out.push(b as char),
            _ => out.push_str(&format!("\\{b:02X}")),
        }
    }
    out
}

/// How much storage the *static* arena holds, in bytes.
///
/// Allocation is a bump pointer into this buffer, which is both the
/// cheapest allocator there is and one that cannot leak.  A program that
/// outgrows it does not fail: it asks for another chunk.
const HEAP_BYTES: usize = 1 << 20;

/// How much a chunk holds once the static arena is full, in bytes.
///
/// Large enough that a program walking a long stream asks the allocator
/// for memory a few dozen times rather than a few million.
const HEAP_CHUNK_BYTES: usize = 1 << 23;

/// The bytes at the head of a malloc'd chunk, reserved for the link that
/// threads it onto the list of chunks to free.  A whole slot rather than
/// a word, so the data after it stays slot-aligned.
const HEAP_CHUNK_HEADER: usize = WORD * 2;

/// The two runtime routines the arena needs, as LLVM IR.
///
/// They are functions rather than inline code because allocation happens
/// at every constructor, and a dozen instructions repeated at each of
/// them would swamp the IR that says what the program actually does.
fn heap_runtime() -> String {
    format!(
        r#"define internal ptr @.ats_alloc(i64 %n) {{
entry:
  %started = load ptr, ptr @.heap.cur
  %fresh = icmp eq ptr %started, null
  br i1 %fresh, label %init, label %bump
init:
  store ptr @.heap, ptr @.heap.cur
  br label %bump
bump:
  %base = load ptr, ptr @.heap.cur
  %off = load i64, ptr @.heap.off
  %cap = load i64, ptr @.heap.cap
  %next = add i64 %off, %n
  %fits = icmp ule i64 %next, %cap
  br i1 %fits, label %ok, label %grow
grow:
  ; A chunk large enough for this request even if the request is large.
  %want = add i64 %n, {header}
  %big = icmp ugt i64 %want, {chunk}
  %size = select i1 %big, i64 %want, i64 {chunk}
  %raw = call ptr @malloc(i64 %size)
  %failed = icmp eq ptr %raw, null
  br i1 %failed, label %oom, label %link
oom:
  %err = load ptr, ptr @stderr
  call i32 (ptr, ptr, ...) @fprintf(ptr %err, ptr @.heap.msg)
  call void @exit(i32 3)
  unreachable
link:
  %head = load ptr, ptr @.heap.chunks
  store ptr %head, ptr %raw
  store ptr %raw, ptr @.heap.chunks
  %data = getelementptr i8, ptr %raw, i64 {header}
  store ptr %data, ptr @.heap.cur
  store i64 0, ptr @.heap.off
  %room = sub i64 %size, {header}
  store i64 %room, ptr @.heap.cap
  ; Retry: the new chunk was sized so that this time it fits.
  br label %bump
ok:
  store i64 %next, ptr @.heap.off
  %p = getelementptr i8, ptr %base, i64 %off
  ret ptr %p
}}

define internal void @.ats_heap_release() {{
entry:
  br label %loop
loop:
  %c = load ptr, ptr @.heap.chunks
  %done = icmp eq ptr %c, null
  br i1 %done, label %end, label %step
step:
  %rest = load ptr, ptr %c
  store ptr %rest, ptr @.heap.chunks
  call void @free(ptr %c)
  br label %loop
end:
  ret void
}}
"#,
        header = HEAP_CHUNK_HEADER,
        chunk = HEAP_CHUNK_BYTES
    )
}

/// The width of one slot in a datatype value.  Every field occupies one,
/// whatever its type, so field `i` sits at the same offset regardless of
/// which constructor built the value.
const WORD: usize = 8;

/// Grows the module: declaration lines, string constants, format constants.
/// String constants are deduplicated by value.
struct ModuleBuilder {
    lines: Vec<String>,
    strings: Vec<String>,
    formats: Vec<String>,
    string_index: HashMap<String, usize>,
    /// Storage for the program's top-level values.
    globals: Vec<String>,
    /// The libc functions a shim reached for, declared only if used.
    externs: std::collections::BTreeSet<&'static str>,
    /// Whether anything in the program allocates, and so needs the arena.
    needs_heap: bool,
    /// How many lambdas have been given names.
    lambdas: usize,
}

impl ModuleBuilder {
    fn new() -> Self {
        Self {
            lines: Vec::new(),
            strings: Vec::new(),
            formats: Vec::new(),
            string_index: HashMap::new(),
            globals: Vec::new(),
            externs: std::collections::BTreeSet::new(),
            needs_heap: false,
            lambdas: 0,
        }
    }

    /// A fresh name for a lifted lambda body.
    fn next_lambda(&mut self) -> usize {
        let id = self.lambdas;
        self.lambdas += 1;
        id
    }

    fn add_string(&mut self, s: &str) -> String {
        if let Some(&i) = self.string_index.get(s) {
            return format!("@.str.{i}");
        }
        let i = self.strings.len();
        self.strings.push(s.to_string());
        self.string_index.insert(s.to_string(), i);
        format!("@.str.{i}")
    }

    fn add_format(&mut self, f: &str) -> String {
        let i = self.formats.len();
        self.formats.push(f.to_string());
        format!("@.fmt.{i}")
    }

    fn render(&self) -> String {
        let mut out = String::new();
        out.push_str("; ModuleID = 'ats2llvm'\n");
        out.push_str("declare i32 @printf(ptr, ...)\n");
        out.push_str("declare i32 @fprintf(ptr, ptr, ...)\n");
        out.push_str("declare void @exit(i32) noreturn\n");
        // `stderr` is a libc global, not a function: to write to it we
        // must load the FILE* it holds before each call.
        out.push_str("@stderr = external global ptr\n");
        for decl in &self.externs {
            out.push_str(decl);
            out.push('\n');
        }
        for g in &self.globals {
            out.push_str(g);
            out.push('\n');
        }
        if self.needs_heap {
            // Datatype values are allocated and never freed *by the
            // program*, so allocation is a bump pointer into a static
            // buffer: the cheapest allocator there is, and one that
            // cannot leak.
            //
            // When that buffer runs out the program asks for another
            // chunk rather than giving up — no fixed size is right for
            // every program, and a lazy stream allocates for as long as
            // it is walked.  Each chunk is threaded onto a list and the
            // whole list is handed back before `main` returns, so the
            // samples still run clean under valgrind.
            out.push_str(&format!("@.heap = internal global [{HEAP_BYTES} x i8] zeroinitializer\n"));
            out.push_str("@.heap.cur = internal global ptr null\n");
            out.push_str("@.heap.off = internal global i64 0\n");
            out.push_str(&format!("@.heap.cap = internal global i64 {HEAP_BYTES}\n"));
            out.push_str("@.heap.chunks = internal global ptr null\n");
            let msg = "exit(ATS): out of memory\n";
            out.push_str(&format!(
                "@.heap.msg = private unnamed_addr constant [{} x i8] c\"{}\\00\"\n",
                msg.len() + 1,
                llvm_escape(msg)
            ));
        }
        for (i, s) in self.strings.iter().enumerate() {
            let len = s.len() + 1;
            out.push_str(&format!("@.str.{i} = private unnamed_addr constant [{len} x i8] c\"{}\\00\"\n", llvm_escape(s)));
        }
        for (i, f) in self.formats.iter().enumerate() {
            let len = f.len() + 1;
            out.push_str(&format!("@.fmt.{i} = private unnamed_addr constant [{len} x i8] c\"{}\\00\"\n", llvm_escape(f)));
        }
        out.push('\n');
        if self.needs_heap {
            out.push_str(&heap_runtime());
            out.push('\n');
        }
        for line in &self.lines {
            out.push_str(line);
            out.push('\n');
        }
        out
    }
}

/// Per-function emission state: emitted lines, fresh-name counters, and
/// the ATS-name → SSA-value environment.
struct FnBuilder {
    lines: Vec<String>,
    temps: usize,
    block_ids: usize,
    env: HashMap<String, FnValue>,
    /// The label of the block instructions are landing in right now.
    ///
    /// A `phi` must name the block control *actually* arrived from, which
    /// is not necessarily the block a branch started in: if the branch
    /// contains its own `if`, the arm ends in that inner merge block.
    /// Tracking the open block is what makes nested conditionals — the
    /// shape every recursive ATS function has — come out correct.
    cur_block: String,
    /// The `var` cells in scope: name → the pointer holding it.
    ///
    /// A cell is looked up before the SSA environment, so a `var` shadows
    /// a `val` of the same name exactly as the source says it should.
    cells: HashMap<String, Cell>,
    /// The exit label of each enclosing loop, innermost last.
    ///
    /// `$break` needs to know where to go, and only the loop knows.
    /// Keeping a stack rather than a single label is what makes a
    /// `$break` inside a nested loop leave the *inner* one, which is
    /// what every language with the construct means by it.
    loop_exits: Vec<String>,
    /// Every `alloca`, collected separately from the instruction stream.
    ///
    /// LLVM permits an `alloca` anywhere, but one that sits inside a loop
    /// body allocates afresh on every turn and grows the stack without
    /// bound.  Hoisting them all into the entry block is the standard
    /// remedy and costs nothing: the storage a function needs is known
    /// once, on entry.
    allocas: Vec<String>,
}

/// A `var` cell: the pointer its storage lives behind, and the type of
/// the value inside it.
#[derive(Debug, Clone)]
struct Cell {
    ptr: String,
    ty: LlvmType,
}

impl FnBuilder {
    fn new() -> Self {
        Self {
            lines: Vec::new(),
            temps: 0,
            block_ids: 0,
            env: HashMap::new(),
            cur_block: "entry".to_string(),
            cells: HashMap::new(),
            loop_exits: Vec::new(),
            allocas: Vec::new(),
        }
    }

    /// Reserve storage for a `var`, returning the pointer to it.
    fn alloca(&mut self, name: &str, ty: LlvmType) -> String {
        let mut ptr = format!("%{}.cell", sanitize(name));
        let mut k = 0;
        while self.allocas.iter().any(|a| a.starts_with(&format!("{ptr} "))) {
            k += 1;
            ptr = format!("%{}.cell.{k}", sanitize(name));
        }
        self.allocas.push(format!("{ptr} = alloca {}", llvm_ty_str(ty)));
        ptr
    }

    /// Open a new basic block, and remember that it is now the open one.
    fn label(&mut self, name: &str) {
        self.lines.push(format!("{name}:"));
        self.cur_block = name.to_string();
    }

    fn line(&mut self, s: impl Into<String>) {
        self.lines.push(s.into());
    }

    fn fresh_temp(&mut self) -> String {
        let r = format!("%t.{}", self.temps);
        self.temps += 1;
        r
    }

    /// One id shared by the whole branch trio of a construct.
    fn fresh_block_id(&mut self) -> usize {
        let id = self.block_ids;
        self.block_ids += 1;
        id
    }
}

/// Append one emitted line to a function's text.
///
/// Block labels sit flush against the left margin and instructions are
/// indented under them, which is how every LLVM tool prints IR and how a
/// reader expects to see the block structure.
fn push_line(text: &mut String, line: &str) {
    if is_label(line) {
        text.push('\n');
    } else {
        text.push_str("\n  ");
    }
    text.push_str(line);
}

/// Whether an emitted line opens a basic block rather than doing work.
fn is_label(line: &str) -> bool {
    line.ends_with(':') && !line.contains(char::is_whitespace)
}

/// Emit one `fun` definition as an LLVM function.
fn emit_function(f: &ats2_domain::ast::FunDef, registry: &Registry, module: &mut ModuleBuilder) -> Result<(), CompileError> {
    let sig = &registry.fns[&f.name];
    let by_ref = registry.by_ref.get(&f.name).cloned().unwrap_or_default();
    let is_by_ref = |i: usize| by_ref.get(i).copied().unwrap_or(false);
    let mut fb = FnBuilder::new();
    for (i, (p, ty)) in f.params.iter().zip(&sig.params).enumerate() {
        let reg = format!("%{}", sanitize(&p.name));
        // An out parameter arrives as the address of the caller's cell,
        // so it *is* a cell here: reading the name loads through it and
        // assigning to it stores through it, which is what makes the
        // write visible to the caller.
        if is_by_ref(i) {
            fb.cells.insert(p.name.clone(), Cell { ptr: reg, ty: *ty });
        } else {
            fb.env.insert(p.name.clone(), FnValue { reg, ty: *ty });
        }
    }
    let value = LlvmIrEmitter.emit_expr_expecting(&f.body, Some(sig.ret), &mut fb, registry, module)?;
    if value.ty != sig.ret && sig.ret != LlvmType::Void && value.ty != LlvmType::Never {
        return Err(CompileError::emit(format!("function `{}` body has type {}, annotation says {}", f.name, llvm_ty_str(value.ty), llvm_ty_str(sig.ret))));
    }
    let params: Vec<String> = f.params.iter().zip(&sig.params).enumerate()
        .map(|(i, (p, ty))| {
            let ty = if is_by_ref(i) { "ptr" } else { llvm_ty_str(*ty) };
            format!("{ty} %{}", sanitize(&p.name))
        })
        .collect();
    let mut text = format!("define {} @{}({}) {{", llvm_ty_str(sig.ret), sanitize(&f.name), params.join(", "));
    text.push_str("\nentry:");
    for line in fb.allocas.iter().chain(&fb.lines) {
        push_line(&mut text, line);
    }
    text.push_str(&ret_instruction(sig.ret, &value));
    module.lines.push(text);
    Ok(())
}

/// The terminator for a function body.  `void` returns carry no operand,
/// which is the one place the empty register of a void value shows.
fn ret_instruction(ret: LlvmType, value: &FnValue) -> String {
    // The body already ended in `unreachable`; a `ret` after it would be
    // dead code that LLVM rejects as a second terminator.
    if value.ty == LlvmType::Never {
        return "\n}".to_string();
    }
    if ret == LlvmType::Void {
        "\n  ret void\n}".to_string()
    } else {
        format!("\n  ret {} {}\n}}", llvm_ty_str(ret), value.reg)
    }
}

/// Emit the `implement main0() = ...` clause as the program entry `@main`.
fn emit_main(im: &ats2_domain::ast::ImplementDef, inits: &[&ats2_domain::ast::ValDef], registry: &Registry, module: &mut ModuleBuilder) -> Result<(), CompileError> {
    let mut fb = FnBuilder::new();
    // A top-level `val` is worked out once, here, before the program's own
    // body runs.  There is nowhere else it could go: its right-hand side
    // is an arbitrary expression, and LLVM's global initializers are
    // constants.
    for v in inits {
        // A top-level statement is run for its effect and stored nowhere.
        let Some(&ty) = registry.globals.get(&v.name) else {
            LlvmIrEmitter.emit_expr(&v.value, &mut fb, registry, module)?;
            continue;
        };
        let value = LlvmIrEmitter.emit_expr_expecting(&v.value, Some(ty), &mut fb, registry, module)?;
        if value.ty != ty {
            return Err(CompileError::emit(format!(
                "`{}` is declared as {} but its value is {}",
                v.name,
                llvm_ty_str(ty),
                llvm_ty_str(value.ty)
            )));
        }
        fb.line(format!("store {} {}, ptr @{}", llvm_ty_str(ty), value.reg, sanitize(&v.name)));
    }
    // C hands `main` an `i32` argument count; every `int` in the subset is
    // an `i64`, so the count is widened once on entry and the ATS name is
    // bound to the widened value.
    let takes_argv = im.params.len() == 2;
    if takes_argv {
        fb.env.insert(im.params[0].name.clone(), FnValue { reg: format!("%{}", sanitize(&im.params[0].name)), ty: LlvmType::I64 });
        fb.env.insert(im.params[1].name.clone(), FnValue { reg: format!("%{}", sanitize(&im.params[1].name)), ty: LlvmType::Argv });
    }
    let value = LlvmIrEmitter.emit_expr(&im.body, &mut fb, registry, module)?;
    // `main0` throws its result away; `main` hands it back as the exit
    // code, narrowed from the subset's `i64` to the `i32` C expects.
    let exit_code = if im.name == "main" {
        if value.ty != LlvmType::I64 {
            return Err(CompileError::emit(format!(
                "`main` must produce an int to use as the exit code, got {}",
                llvm_ty_str(value.ty)
            )));
        }
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = trunc i64 {} to i32", value.reg));
        reg
    } else {
        "0".to_string()
    };
    let mut text = if takes_argv {
        format!(
            "define i32 @main(i32 %{0}.raw, ptr %{1}) {{",
            sanitize(&im.params[0].name),
            sanitize(&im.params[1].name)
        )
    } else {
        "define i32 @main() {".to_string()
    };
    text.push_str("\nentry:");
    if takes_argv {
        text.push_str(&format!(
            "\n  %{0} = sext i32 %{0}.raw to i64",
            sanitize(&im.params[0].name)
        ));
    }
    for line in fb.allocas.iter().chain(&fb.lines) {
        push_line(&mut text, line);
    }
    // Hand back whatever the arena grew by.  Nothing reads a datatype
    // value after `main` returns, and releasing here is what lets the
    // samples be checked under valgrind without every long-running one
    // reporting a leak.
    if module.needs_heap {
        text.push_str("\n  call void @.ats_heap_release()");
    }
    text.push_str(&format!("\n  ret i32 {exit_code}\n}}"));
    module.lines.push(text);
    Ok(())
}

impl LlvmIrEmitter {
    /// Lower one expression, appending its instructions to `fb`.
    fn emit_expr(&self, expr: &Expr, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        self.emit_expr_expecting(expr, None, fb, registry, module)
    }

    /// Lower one expression, knowing what type the context wants.
    ///
    /// Most expressions say what they are: `1` is an int whatever is
    /// expected of it.  A few do not — a bare `None()` names a
    /// constructor that several datatype instances share, and nothing in
    /// the expression itself settles which — and for those the expected
    /// type is the only thing that can decide.  This is the *checking*
    /// direction of bidirectional typing, added exactly where inference
    /// runs out rather than as a whole type checker.
    fn emit_expr_expecting(&self, expr: &Expr, expected: Option<LlvmType>, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        match expr {
            Expr::Unit => Ok(FnValue { reg: String::new(), ty: LlvmType::Void }),
            // `'{ x= 1, y= 2 }` — a record.  Its slots are laid out in
            // the order written, which is what fixes each name to one.
            Expr::RecordLit(fields) => {
                // An annotation says what each field should be, which is
                // how a field holding `nil()` or a bare lambda knows
                // which type it is.
                let want: Vec<Option<LlvmType>> = match expected {
                    Some(LlvmType::Record(i)) => {
                        let declared = registry.record_fields(i);
                        fields
                            .iter()
                            .map(|(n, _)| declared.iter().find(|(d, _)| d == n).map(|(_, t)| *t))
                            .collect()
                    }
                    _ => vec![None; fields.len()],
                };
                let mut values = Vec::new();
                for ((name, value), w) in fields.iter().zip(want) {
                    let v = self.emit_expr_expecting(value, w, fb, registry, module)?;
                    values.push((name.clone(), v));
                }
                let ptr = self.emit_alloc(WORD * values.len(), fb, module);
                for (slot, (_, v)) in values.iter().enumerate() {
                    let addr = self.emit_slot_address(&ptr, slot, fb);
                    fb.line(format!("store {} {}, ptr {addr}", llvm_ty_str(v.ty), v.reg));
                }
                let shape: Vec<(String, LlvmType)> =
                    values.into_iter().map(|(n, v)| (n, v.ty)).collect();
                Ok(FnValue { reg: ptr, ty: LlvmType::Record(registry.intern_record(shape)) })
            }
            // `r.cmp` — one field, or, when the left-hand side is not a
            // record with that field, ATS's dot notation for a call with
            // the receiver first.
            Expr::Field(base, name) => {
                if !self.is_a_record_field(base, name, fb, registry) {
                    // Dot notation: `s.tail()` is `tail(s)`.
                    return self.emit_call(
                        &Expr::Var(name.clone()),
                        std::slice::from_ref(&**base),
                        expected,
                        fb,
                        registry,
                        module,
                    );
                }
                let v = self.emit_expr(base, fb, registry, module)?;
                let Some((slot, ty)) = self.record_slot(&v, name, registry) else {
                    return Err(CompileError::emit(format!("this record has no field `{name}`")));
                };
                let addr = self.emit_slot_address(&v.reg, slot, fb);
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = load {}, ptr {addr}", llvm_ty_str(ty)));
                Ok(FnValue { reg, ty })
            }
            Expr::TupleLit(items) => {
                let want: Vec<Option<LlvmType>> = match expected {
                    Some(LlvmType::Tuple(i)) => registry.tuple_parts(i).into_iter().map(Some).collect(),
                    _ => vec![None; items.len()],
                };
                let mut values = Vec::new();
                for (item, w) in items.iter().zip(want.into_iter().chain(std::iter::repeat(None))) {
                    values.push(self.emit_expr_expecting(item, w, fb, registry, module)?);
                }
                let parts: Vec<LlvmType> = values.iter().map(|v| v.ty).collect();
                let ptr = self.emit_alloc(WORD * values.len(), fb, module);
                for (i, v) in values.iter().enumerate() {
                    let addr = self.emit_slot_address(&ptr, i, fb);
                    fb.line(format!("store {} {}, ptr {addr}", llvm_ty_str(v.ty), v.reg));
                }
                Ok(FnValue { reg: ptr, ty: LlvmType::Tuple(registry.intern_tuple(parts)) })
            }
            Expr::Wildcard => Err(CompileError::emit("`_` stands for a value the compiler must infer, which this one cannot")),
            // An uninitialized `var`.  The annotation is the only thing
            // that says what the cell holds, so without one there is
            // nothing to start it from.
            Expr::Uninit => match expected {
                Some(ty) => Ok(FnValue { reg: zero_literal(ty).to_string(), ty }),
                None => Err(CompileError::emit(
                    "an uninitialized `var` needs a type annotation to say what its cell holds",
                )),
            },
            Expr::Inst(name, _) => Err(CompileError::emit(format!("internal: the template `{name}` was not expanded"))),
            Expr::IntLit(n) => Ok(FnValue { reg: n.to_string(), ty: LlvmType::I64 }),
            Expr::CharLit(b) => Ok(FnValue { reg: b.to_string(), ty: LlvmType::I8 }),
            // LLVM wants a float constant to look like one, so a whole
            // number still carries its point: `1` would be an integer.
            Expr::FloatLit(v) => {
                let x = v.value();
                let text = if x == x.trunc() && x.is_finite() {
                    format!("{x:.1}")
                } else {
                    format!("{x}")
                };
                Ok(FnValue { reg: text, ty: LlvmType::F64 })
            }
            Expr::BoolLit(b) => Ok(FnValue { reg: if *b { "true".into() } else { "false".into() }, ty: LlvmType::I1 }),
            Expr::StrLit(s) => {
                // With opaque pointers, a constant's address is the global
                // itself: `ptr @.str.k`.  No GEP is needed for whole
                // constants (modern LLVM style).
                let reg = module.add_string(s);
                Ok(FnValue { reg, ty: LlvmType::I8Ptr })
            }
            // A `var` is storage, so reading it is a load; a `val` is an
            // SSA value already in hand.
            // `$break` — leave the innermost loop.  It produces no
            // value and control never returns from it, which is exactly
            // the bottom type.
            Expr::Var(name) if name == "$break" => {
                let Some(exit) = fb.loop_exits.last().cloned() else {
                    return Err(CompileError::emit("`$break` outside a loop"));
                };
                fb.line(format!("br label %{exit}"));
                // Anything written after a `$break` is unreachable, but
                // LLVM still wants the block it would live in to have a
                // terminator — and `unreachable` is the one that says so.
                let id = fb.fresh_block_id();
                fb.label(&format!("break.after.{id}"));
                fb.line("unreachable");
                Ok(FnValue { reg: String::new(), ty: LlvmType::Never })
            }
            Expr::Var(name) if fb.cells.contains_key(name) => {
                let cell = fb.cells[name].clone();
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = load {}, ptr {}", llvm_ty_str(cell.ty), cell.ptr));
                Ok(FnValue { reg, ty: cell.ty })
            }
            // A top-level `val` lives in storage, so reading it is a load.
            Expr::Var(name)
                if !fb.env.contains_key(name)
                    && !fb.cells.contains_key(name)
                    && registry.globals.contains_key(name) =>
            {
                let ty = registry.globals[name];
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = load {}, ptr @{}", llvm_ty_str(ty), sanitize(name)));
                Ok(FnValue { reg, ty })
            }
            // `stdin_ref` and friends: C keeps the streams in globals, so
            // naming one is a load rather than a constant.
            Expr::Var(name) if !fb.env.contains_key(name) && standard_stream(name).is_some() => {
                let c_name = standard_stream(name).expect("just checked");
                module.externs.insert(match c_name {
                    "stdin" => "@stdin = external global ptr",
                    "stdout" => "@stdout = external global ptr",
                    _ => "@stderr = external global ptr",
                });
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = load ptr, ptr @{c_name}"));
                Ok(FnValue { reg, ty: LlvmType::FileRef })
            }
            // `file_mode_r` / `file_mode_w` are the C mode strings.
            Expr::Var(name) if !fb.env.contains_key(name) && file_mode(name).is_some() => {
                let reg = module.add_string(file_mode(name).expect("just checked"));
                Ok(FnValue { reg, ty: LlvmType::I8Ptr })
            }
            // `Nil` without parentheses still builds the value.
            Expr::Var(name)
                if !fb.env.contains_key(name)
                    && registry.ctors.get(name).is_some_and(|c| c.iter().all(|i| i.fields.is_empty())) =>
            {
                let info = resolve_ctor(name, &[], expected, registry)?;
                self.emit_ctor(name, &info, &[], fb, registry, module)
            }
            Expr::Var(name) => match fb.env.get(name) {
                Some(v) => Ok(v.clone()),
                // Not a local: it may be a `#define` constant, whose
                // right-hand side is emitted here, at the point of use.
                None if registry.consts.contains_key(name) => {
                    let value = registry.consts[name].clone();
                    self.emit_expr(&value, fb, registry, module)
                }
                None if registry.fns.contains_key(name) => {
                    Err(CompileError::emit(format!("function `{name}` used as a value; higher-order functions are not supported yet")))
                }
                None => Err(CompileError::emit(format!("undefined variable `{name}`"))),
            },
            Expr::UnaryNeg(e) => {
                let v = self.emit_expr(e, fb, registry, module)?;
                match v.ty {
                    LlvmType::I64 => {
                        let reg = fb.fresh_temp();
                        fb.line(format!("{reg} = sub i64 0, {}", v.reg));
                        Ok(FnValue { reg, ty: LlvmType::I64 })
                    }
                    LlvmType::F64 => {
                        let reg = fb.fresh_temp();
                        fb.line(format!("{reg} = fneg double {}", v.reg));
                        Ok(FnValue { reg, ty: LlvmType::F64 })
                    }
                    // `~xs` on anything else *consumes* it: ATS spells
                    // "negate" and "free this linear value" with the same
                    // character, and only the operand's type tells them
                    // apart.  The operand is still evaluated — it may be
                    // a call that does the real work — and then there is
                    // nothing to free, because the arena frees
                    // everything at once.
                    _ => Ok(FnValue { reg: String::new(), ty: LlvmType::Void }),
                }
            }
            Expr::BinOp(op, l, r) => self.emit_binop(*op, l, r, fb, registry, module),
            Expr::Call(callee, args) => self.emit_call(callee, args, expected, fb, registry, module),
            Expr::Index(base, index) => self.emit_index(base, index, fb, registry, module),
            Expr::Proj(base, slot) => self.emit_proj(base, *slot, fb, registry, module),
            Expr::Deref(inner) => self.emit_deref(inner, fb, registry, module),
            Expr::Store(place, value) => self.emit_store(place, value, fb, registry, module),
            Expr::IfThenElse(c, t, e) => self.emit_if(c, t, e, expected, fb, registry, module),
            Expr::Let(binds, body) => {
                for bind in binds {
                    let annotated = bind.ty.as_ref().map(|t| llvm_type_in(t, registry)).transpose()?;
                    let v = self.emit_expr_expecting(&bind.value, annotated, fb, registry, module)?;
                    if let Some(ann) = &bind.ty {
                        let expected = llvm_type_in(ann, registry)?;
                        if v.ty != expected {
                            return Err(CompileError::emit(format!("binding `{}` has type {}, annotation says {}", bind.name.as_deref().unwrap_or("()"), llvm_ty_str(v.ty), llvm_ty_str(expected))));
                        }
                    }
                    if let Some(name) = &bind.name {
                        if bind.mutable {
                            let ptr = fb.alloca(name, v.ty);
                            fb.line(format!("store {} {}, ptr {}", llvm_ty_str(v.ty), v.reg, ptr));
                            fb.cells.insert(name.clone(), Cell { ptr, ty: v.ty });
                            // A cell shadows any value of the same name.
                            fb.env.remove(name);
                        } else {
                            fb.cells.remove(name);
                            fb.env.insert(name.clone(), v);
                        }
                    }
                }
                self.emit_expr_expecting(body, expected, fb, registry, module)
            }
            Expr::Lam(params, ret, body) => self.emit_lambda(params, ret.as_ref(), body, expected, fb, registry, module),
            Expr::LetFun(_, _) => Err(CompileError::emit("internal: a nested function survived lambda lifting")),
            Expr::Assign(name, value) => self.emit_assign(name, value, fb, registry, module),
            Expr::While(c, b) => self.emit_while(c, b, fb, registry, module),
            Expr::For(i, c, st, b) => self.emit_for(i, c, st, b, fb, registry, module),
            Expr::Case(scrutinee, arms) => self.emit_case(scrutinee, arms, expected, fb, registry, module),
            Expr::MacroCall(name, args) => self.emit_macro(name, args, fb, registry, module),
        }
    }

    fn emit_binop(&self, op: BinOp, l: &Expr, r: &Expr, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        let (lv, rv) = (self.emit_expr(l, fb, registry, module)?, self.emit_expr(r, fb, registry, module)?);
        // The connectives are not value operations: the right operand may
        // never be evaluated, so it is handed over unevaluated.
        if matches!(op, BinOp::Andalso | BinOp::Orelse) {
            if lv.ty != LlvmType::I1 {
                return Err(CompileError::emit("andalso/orelse require bool operands"));
            }
            return self.emit_short_circuit(op, lv.reg, r, fb, registry, module);
        }
        match self.emit_binop_values(op, lv.clone(), rv.clone(), fb) {
            Ok(v) => Ok(v),
            // The operands do not fit the operator.  If the program named
            // a function to fall back on, that is what it is for.
            Err(e) => match registry.overloads.get(operator_symbol(op)) {
                Some(func) => {
                    let saved = fb.lines.len();
                    let _ = saved;
                    self.emit_overload(func, op, lv, rv, fb, registry, module)
                }
                None => Err(e),
            },
        }
    }

    /// Apply an operator to two values already in hand.
    fn emit_binop_values(&self, op: BinOp, lv: FnValue, rv: FnValue, fb: &mut FnBuilder) -> Result<FnValue, CompileError> {
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                if lv.ty == LlvmType::F64 && rv.ty == LlvmType::F64 {
                    let instr = match op {
                        BinOp::Add => "fadd", BinOp::Sub => "fsub", BinOp::Mul => "fmul",
                        BinOp::Div => "fdiv", _ => "frem",
                    };
                    let reg = fb.fresh_temp();
                    fb.line(format!("{reg} = {instr} double {}, {}", lv.reg, rv.reg));
                    return Ok(FnValue { reg, ty: LlvmType::F64 });
                }
                let instr = match op {
                    BinOp::Add => "add", BinOp::Sub => "sub", BinOp::Mul => "mul", BinOp::Div => "sdiv", _ => "srem",
                };
                self.emit_arithmetic(instr, lv, rv, fb)
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                self.emit_comparison(op, lv, rv, fb)
            }
            BinOp::Andalso | BinOp::Orelse => {
                Err(CompileError::emit("andalso/orelse are not value operations"))
            }
        }
    }

    /// Apply the function an `overload` named for this operator.
    ///
    /// Only the generic numeric shims are reachable this way so far, which
    /// is what the samples declare; a user function of the right shape
    /// would need its arguments passed rather than its meaning inlined.
    fn emit_overload(&self, func: &str, op: BinOp, lv: FnValue, rv: FnValue, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        if func.starts_with('g') && (func.contains("_int_val") || func.contains("_val_int")) {
            return self.emit_promoted(op, lv, rv, fb);
        }
        let sig = registry.fns.get(func).ok_or_else(|| {
            CompileError::emit(format!("`{func}` is named by an `overload` but is not defined"))
        })?;
        if sig.params.len() != 2 {
            return Err(CompileError::emit(format!("`{func}` is an overload, so it must take two arguments")));
        }
        let _ = module;
        let operands = [
            format!("{} {}", llvm_ty_str(lv.ty), lv.reg),
            format!("{} {}", llvm_ty_str(rv.ty), rv.reg),
        ];
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = call {} @{}({})", llvm_ty_str(sig.ret), sanitize(func), operands.join(", ")));
        Ok(FnValue { reg, ty: sig.ret })
    }

    /// `+ - * / mod` on ints.
    fn emit_arithmetic(&self, instr: &str, lv: FnValue, rv: FnValue, fb: &mut FnBuilder) -> Result<FnValue, CompileError> {
        // A character is a small integer, and ATS treats it as one:
        // `c - '0'` is the idiom every digit-parsing loop is built on.
        // Widening here keeps that spelling working without making
        // `char` and `int` the same type everywhere else.
        let (lv, rv) = match (lv.ty, rv.ty) {
            (LlvmType::I8, _) | (_, LlvmType::I8) => (
                self.emit_numeric_cast(lv, LlvmType::I64, fb)?,
                self.emit_numeric_cast(rv, LlvmType::I64, fb)?,
            ),
            _ => (lv, rv),
        };
        // `10 * env` where `env` is a double: ATS resolves this through
        // the overloaded operator, and the overload widens.  Doing the
        // same here means a literal need not be written `10.0` in code
        // that is otherwise unambiguous.
        if lv.ty == LlvmType::F64 || rv.ty == LlvmType::F64 {
            let lv = self.emit_numeric_cast(lv, LlvmType::F64, fb)?;
            let rv = self.emit_numeric_cast(rv, LlvmType::F64, fb)?;
            let fop = match instr {
                "add" => "fadd",
                "sub" => "fsub",
                "mul" => "fmul",
                "sdiv" => "fdiv",
                _ => "frem",
            };
            let reg = fb.fresh_temp();
            fb.line(format!("{reg} = {fop} double {}, {}", lv.reg, rv.reg));
            return Ok(FnValue { reg, ty: LlvmType::F64 });
        }
        if lv.ty != LlvmType::I64 || rv.ty != LlvmType::I64 {
            return Err(CompileError::emit("arithmetic requires int operands"));
        }
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = {instr} i64 {}, {}", lv.reg, rv.reg));
        Ok(FnValue { reg, ty: LlvmType::I64 })
    }

    /// Comparisons, lowered to `icmp` with the code dictated by the
    /// operand type (`slt` for ints; `eq`/`ne` for bools; ordering a bool
    /// is an error).
    fn emit_comparison(&self, op: BinOp, lv: FnValue, rv: FnValue, fb: &mut FnBuilder) -> Result<FnValue, CompileError> {
        // `p > 0`, `p = 0` — ATS's way of asking whether a call handed
        // back anything.  A pointer is not a number, so the only reading
        // that means something is the null test, and that is what is
        // emitted rather than an ordering on addresses.
        if let Some(v) = self.emit_null_test(op, &lv, &rv, fb) {
            return Ok(v);
        }
        if lv.ty != rv.ty {
            return Err(CompileError::emit("cannot compare values of different types"));
        }
        if lv.ty == LlvmType::I8Ptr {
            return Err(CompileError::emit("string comparison is not supported yet"));
        }
        let code = match (op, lv.ty) {
            (BinOp::Eq, _) => "eq",
            (BinOp::Ne, _) => "ne",
            (BinOp::Lt, LlvmType::I1) => return Err(CompileError::emit("cannot order booleans")),
            (BinOp::Lt, _) => "slt",
            (BinOp::Le, LlvmType::I1) => return Err(CompileError::emit("cannot order booleans")),
            (BinOp::Le, _) => "sle",
            (BinOp::Gt, LlvmType::I1) => return Err(CompileError::emit("cannot order booleans")),
            (BinOp::Gt, _) => "sgt",
            (BinOp::Ge, LlvmType::I1) => return Err(CompileError::emit("cannot order booleans")),
            (BinOp::Ge, _) => "sge",
            _ => unreachable!(),
        };
        // Ordered predicates: a comparison involving NaN is false, which
        // is what `o` selects and what every other language means by `<`.
        if lv.ty == LlvmType::F64 {
            let fcode = match op {
                BinOp::Eq => "oeq", BinOp::Ne => "one", BinOp::Lt => "olt",
                BinOp::Le => "ole", BinOp::Gt => "ogt", _ => "oge",
            };
            let reg = fb.fresh_temp();
            fb.line(format!("{reg} = fcmp {fcode} double {}, {}", lv.reg, rv.reg));
            return Ok(FnValue { reg, ty: LlvmType::I1 });
        }
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = icmp {code} {} {}, {}", llvm_ty_str(lv.ty), lv.reg, rv.reg));
        Ok(FnValue { reg, ty: LlvmType::I1 })
    }

    /// A comparison of a pointer against the literal zero, as the null
    /// test it means.  `None` when this is not that comparison.
    fn emit_null_test(&self, op: BinOp, lv: &FnValue, rv: &FnValue, fb: &mut FnBuilder) -> Option<FnValue> {
        let pointerish = |t: LlvmType| {
            matches!(t, LlvmType::I8Ptr | LlvmType::Data(_) | LlvmType::Tuple(_)
                | LlvmType::Array(_) | LlvmType::Closure(_) | LlvmType::Lazy(_)
                | LlvmType::Record(_) | LlvmType::FileRef)
        };
        let (ptr, zero) = match (pointerish(lv.ty), pointerish(rv.ty)) {
            (true, false) if rv.reg == "0" => (lv, rv),
            (false, true) if lv.reg == "0" => (rv, lv),
            _ => return None,
        };
        let _ = zero;
        let code = match op {
            // "there is something there" and "there is nothing there"
            // are the only two questions a null test can answer.
            BinOp::Gt | BinOp::Ge | BinOp::Ne => "ne",
            BinOp::Eq | BinOp::Le | BinOp::Lt => "eq",
            _ => return None,
        };
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = icmp {code} ptr {}, null", ptr.reg));
        Some(FnValue { reg, ty: LlvmType::I1 })
    }

    /// `a andalso b` / `a orelse b` with ATS short-circuit semantics:
    /// evaluate `b` only when the first operand decides the outcome.
    fn emit_short_circuit(&self, op: BinOp, cond: String, r: &Expr, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        let id = fb.fresh_block_id();
        let prefix = if op == BinOp::Andalso { "and" } else { "or" };
        let t = format!("{prefix}.t.{id}");
        let f = format!("{prefix}.f.{id}");
        let m = format!("{prefix}.m.{id}");
        fb.line(format!("br i1 {cond}, label %{t}, label %{f}"));
        fb.label(&t);
        let then_done = if op == BinOp::Andalso {
            let rv = self.emit_expr(r, fb, registry, module)?;
            fb.line(format!("br label %{m}"));
            rv
        } else {
            fb.line(format!("br label %{m}"));
            FnValue { reg: "true".into(), ty: LlvmType::I1 }
        };
        // As in `emit_if`: the right operand may itself branch, so the
        // block reaching the merge is the one open now, not `t`/`f`.
        let tpred = fb.cur_block.clone();
        fb.label(&f);
        let else_done = if op == BinOp::Orelse {
            let rv = self.emit_expr(r, fb, registry, module)?;
            fb.line(format!("br label %{m}"));
            rv
        } else {
            fb.line(format!("br label %{m}"));
            FnValue { reg: "false".into(), ty: LlvmType::I1 }
        };
        let epred = fb.cur_block.clone();
        for v in [&then_done, &else_done] {
            if v.ty != LlvmType::I1 {
                return Err(CompileError::emit("andalso/orelse require bool operands"));
            }
        }
        fb.label(&m);
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = phi i1 [ {}, %{tpred} ], [ {}, %{epred} ]", then_done.reg, else_done.reg));
        Ok(FnValue { reg, ty: LlvmType::I1 })
    }

    fn emit_call(&self, callee: &Expr, args: &[Expr], expected: Option<LlvmType>, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        // `f(a)(b)` has two readings.  It is a *curried* call when `f`
        // is one function of two parameters, and an application of the
        // *result* when `f` returns a closure.  Which one it is depends on
        // how many parameters `f` actually has, so the spine is flattened
        // only when the count comes out right; otherwise the inner call is
        // evaluated and its result applied.
        if let Expr::Call(..) = callee {
            let mut spine: Vec<&[Expr]> = vec![args];
            let mut inner = callee;
            while let Expr::Call(next, next_args) = inner {
                spine.push(next_args);
                inner = next;
            }
            let mut flat: Vec<Expr> = Vec::new();
            for part in spine.iter().rev() {
                flat.extend(part.iter().cloned());
            }
            let head = match inner {
                Expr::Var(n) => Some(n),
                Expr::Inst(n, _) => Some(n),
                _ => None,
            };
            let fits = head
                .and_then(|n| registry.fns.get(n))
                .is_some_and(|sig| sig.params.len() == flat.len());
            if fits {
                return self.emit_call(inner, &flat, expected, fb, registry, module);
            }
            let value = self.emit_expr(callee, fb, registry, module)?;
            return self.emit_closure_call(value, args, fb, registry, module);
        }

        // `r.f(a, b)` — either the record field `f` applied, or ATS's
        // dot notation for `f(r, a, b)`.  The same rule decides as for a
        // field read on its own, and it decides before the receiver is
        // emitted so that it is emitted exactly once.
        if let Expr::Field(base, field) = callee {
            if self.is_a_record_field(base, field, fb, registry) {
                let f = self.emit_expr(callee, fb, registry, module)?;
                return self.emit_closure_call(f, args, fb, registry, module);
            }
            let mut all: Vec<Expr> = vec![(**base).clone()];
            all.extend(args.iter().cloned());
            return self.emit_call(&Expr::Var(field.clone()), &all, expected, fb, registry, module);
        }

        // `f<t>(x)` reaches here when `f` is a shim rather than a
        // template: the type arguments choose which shim is meant.
        let (name, ty_args) = match &*callee {
            Expr::Var(n) => (n, Vec::new()),
            Expr::Inst(n, tys) => (n, tys.clone()),
            _ => return Err(CompileError::emit("only named functions can be called (no higher-order calls)")),
        };
        if name == "main0" || name == "main" {
            return Err(CompileError::emit(format!("`{name}` is the program entry and cannot be called")));
        }
        // `assertloc` looks like a call but lowers to a branch, so it is
        // intercepted before the ordinary call path.
        if name == "assertloc" || name == "assert" || name == "assertexn" {
            return self.emit_assert(args, fb, registry, module);
        }
        // A constructor looks like a call and is one, but it builds a
        // value rather than transferring control.
        if registry.ctors.contains_key(name.as_str()) {
            let info = resolve_ctor(name, &ty_args, expected, registry)?;
            return self.emit_ctor(name, &info, args, fb, registry, module);
        }
        // A prelude shim shadows nothing: ATS programs `staload` these
        // from the prelude, which this compiler skips, so a definition of
        // the same name in the program itself wins.
        //
        // A *declaration* is not a definition.  `extern fun f (): void =
        // "ext#"` says the body lives outside ATS — often in the C block
        // this compiler skips — so the shim must still get its turn, or
        // the program links against a symbol nobody ever defined.
        if !registry.defined.contains(name) {
            if let Some(v) = self.emit_shim(name, &ty_args, args, fb, registry, module)? {
                return Ok(v);
            }
        }
        // A local holding a closure is applied, not called by name.
        if let Some(v) = fb.env.get(name).cloned() {
            if matches!(v.ty, LlvmType::Closure(_)) {
                return self.emit_closure_call(v, args, fb, registry, module);
            }
        }
        // A cell or a top-level value may hold a closure, and then the
        // name is applied rather than called.
        let indirect = fb.cells.contains_key(name)
            || (!fb.env.contains_key(name)
                && matches!(registry.globals.get(name), Some(LlvmType::Closure(_))));
        if indirect {
            let v = self.emit_expr(&Expr::Var(name.clone()), fb, registry, module)?;
            if matches!(v.ty, LlvmType::Closure(_)) {
                return self.emit_closure_call(v, args, fb, registry, module);
            }
        }
        let sig = registry.fns.get(name).ok_or_else(|| CompileError::emit(format!("unknown function `{name}`")))?;
        // Declared here, defined nowhere and answered by no shim: it is
        // C's, and a declaration is what lets the call reach it.
        if !registry.defined.contains(name) {
            let ps: Vec<&str> = sig.params.iter().map(|p| llvm_ty_str(*p)).collect();
            module.externs.insert(Box::leak(
                format!("declare {} @{}({})", llvm_ty_str(sig.ret), sanitize(name), ps.join(", "))
                    .into_boxed_str(),
            ));
        }
        if args.len() != sig.params.len() {
            return Err(CompileError::emit(format!("function `{name}` expects {} argument(s), got {}", sig.params.len(), args.len())));
        }
        let by_ref = registry.by_ref.get(name).cloned().unwrap_or_default();
        let mut operands = Vec::new();
        for (i, (arg, want)) in args.iter().zip(&sig.params).enumerate() {
            // An out parameter takes the *address* of the caller's cell,
            // so the argument has to be something that has one.
            if by_ref.get(i).copied().unwrap_or(false) {
                let cell = match arg {
                    Expr::Var(n) => fb.cells.get(n).cloned(),
                    _ => None,
                };
                let Some(cell) = cell else {
                    return Err(CompileError::emit(format!(
                        "`{name}` writes back through parameter {}, so it needs something with an address there; declare it with `var`",
                        i + 1
                    )));
                };
                if cell.ty != *want {
                    return Err(CompileError::emit(format!(
                        "argument to `{name}` is a cell of {}, expected {}",
                        llvm_ty_str(cell.ty),
                        llvm_ty_str(*want)
                    )));
                }
                operands.push(format!("ptr {}", cell.ptr));
                continue;
            }
            let v = self.emit_expr_expecting(arg, Some(*want), fb, registry, module)?;
            if v.ty != *want {
                return Err(CompileError::emit(format!("argument to `{name}` has type {}, expected {}", llvm_ty_str(v.ty), llvm_ty_str(*want))));
            }
            operands.push(format!("{} {}", llvm_ty_str(v.ty), v.reg));
        }
        // A void call names no result: `%t = call void @f()` is invalid IR.
        if sig.ret == LlvmType::Void {
            fb.line(format!("call void @{}({})", sanitize(name), operands.join(", ")));
            return Ok(FnValue { reg: String::new(), ty: LlvmType::Void });
        }
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = call {} @{}({})", llvm_ty_str(sig.ret), sanitize(name), operands.join(", ")));
        Ok(FnValue { reg, ty: sig.ret })
    }

    fn emit_if(&self, c: &Expr, t: &Expr, e: &Expr, expected: Option<LlvmType>, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        let cv = self.emit_expr(c, fb, registry, module)?;
        if cv.ty != LlvmType::I1 {
            return Err(CompileError::emit("if condition must be a bool"));
        }
        let id = fb.fresh_block_id();
        let tlab = format!("if.t.{id}");
        let elab = format!("if.e.{id}");
        let mlab = format!("if.m.{id}");
        fb.line(format!("br i1 {}, label %{tlab}, label %{elab}", cv.reg));

        fb.label(&tlab);
        let tv = self.emit_expr_expecting(t, expected, fb, registry, module)?;
        let tpred = fb.cur_block.clone();
        if tv.ty != LlvmType::Never {
            fb.line(format!("br label %{mlab}"));
        }

        fb.label(&elab);
        // The first arm may have settled a type the second can reuse.
        let ev = self.emit_expr_expecting(e, expected.or(Some(tv.ty)), fb, registry, module)?;
        let epred = fb.cur_block.clone();
        if ev.ty != LlvmType::Never {
            fb.line(format!("br label %{mlab}"));
        }

        // A branch of type `Never` ended in `unreachable`, so it does not
        // reach the merge and must not appear among the phi's incoming
        // edges — naming a block that cannot branch here is invalid IR.
        let arms: Vec<(&FnValue, &String)> = [(&tv, &tpred), (&ev, &epred)]
            .into_iter()
            .filter(|(v, _)| v.ty != LlvmType::Never)
            .collect();
        let Some(((first, _), rest)) = arms.split_first().map(|(f, r)| (*f, r)) else {
            // Both branches diverge, so the whole `if` does.
            fb.label(&mlab);
            fb.line("unreachable");
            return Ok(FnValue { reg: String::new(), ty: LlvmType::Never });
        };
        if let Some((other, _)) = rest.first() {
            if first.ty != other.ty {
                return Err(CompileError::emit(format!(
                    "if branches have different types ({} vs {})",
                    llvm_ty_str(first.ty),
                    llvm_ty_str(other.ty)
                )));
            }
        }
        let ty = first.ty;
        fb.label(&mlab);
        // A conditional *statement* merges control but produces no value,
        // so there is nothing for a phi to choose between.
        if ty == LlvmType::Void {
            return Ok(FnValue { reg: String::new(), ty: LlvmType::Void });
        }
        let incoming: Vec<String> = arms.iter().map(|(v, p)| format!("[ {}, %{p} ]", v.reg)).collect();
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = phi {} {}", llvm_ty_str(ty), incoming.join(", ")));
        Ok(FnValue { reg, ty })
    }

    /// The `print` family.  ATS spells the destination and the trailing
    /// newline into the macro's *name*: `print!`/`println!` go to stdout,
    /// `prerr!`/`prerrln!` to stderr, and the `f`-prefixed forms take the
    /// stream as their first argument.  All of them collapse to a single
    /// `printf`/`fprintf` call with one synthesized format string, which
    /// is both the simplest lowering and the fastest one.
    fn emit_macro(&self, name: &str, args: &[Expr], fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        let (stream, newline, takes_stream) = match name {
            "print!" => (Stream::Stdout, false, false),
            "println!" => (Stream::Stdout, true, false),
            "prerr!" => (Stream::Stderr, false, false),
            "prerrln!" => (Stream::Stderr, true, false),
            "fprint!" => (Stream::Stdout, false, true),
            "fprintln!" => (Stream::Stdout, true, true),
            _ => return Err(CompileError::emit(format!("unsupported macro `{name}` (the print family and `assertloc` are what exist)"))),
        };
        // `fprint!(out, ...)`: the stream argument is read from the first
        // position.  It may be any expression of type `FILEref`; the two
        // standard streams are recognised by name only because writing to
        // them needs no stream operand.
        let (stream, args) = if takes_stream {
            let Some((first, rest)) = args.split_first() else {
                return Err(CompileError::emit(format!("`{name}` needs a stream as its first argument")));
            };
            (self.emit_stream_argument(name, first, fb, registry, module)?, rest)
        } else {
            (stream, args)
        };
        self.emit_format(&stream, args, newline, fb, registry, module)?;
        Ok(FnValue { reg: String::new(), ty: LlvmType::Void })
    }

    /// The destination named by a print form's first argument.
    ///
    /// It may be any expression of type `FILEref`; the two standard
    /// streams are recognised by name as well, because writing to those
    /// needs no stream operand at all.
    fn emit_stream_argument(&self, name: &str, first: &Expr, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<Stream, CompileError> {
        match first {
            Expr::Var(v) if v == "stdout_ref" => Ok(Stream::Stdout),
            Expr::Var(v) if v == "stderr_ref" => Ok(Stream::Stderr),
            other => {
                let v = self.emit_expr(other, fb, registry, module)?;
                if v.ty != LlvmType::FileRef {
                    return Err(CompileError::emit(format!(
                        "`{name}` needs a FILEref as its first argument, got {}",
                        llvm_ty_str(v.ty)
                    )));
                }
                Ok(Stream::Ref(v.reg))
            }
        }
    }

    /// Turn the arguments of a print macro into one format string plus the
    /// varargs that fill it.  String *literals* become format text
    /// directly (so `%` in them must be doubled); everything else is
    /// evaluated and placed behind the placeholder its type calls for.
    fn emit_format(&self, stream: &Stream, args: &[Expr], newline: bool, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<(), CompileError> {
        let mut fmt = String::new();
        let mut operands = Vec::new();
        for arg in args {
            match arg {
                Expr::StrLit(s) => fmt.push_str(&s.replace('%', "%%")),
                other => {
                    let v = self.emit_expr(other, fb, registry, module)?;
                    self.format_one(stream, v, &mut fmt, &mut operands, fb, registry, module)?;
                }
            }
        }
        if newline {
            fmt.push('\n');
        }
        if !fmt.is_empty() || !operands.is_empty() {
            self.emit_printf(stream.clone(), &fmt, &operands, fb, module);
        }
        Ok(())
    }

    /// Append the placeholder and varargs operand that print one value.
    ///
    /// Split out of `emit_format` because a tuple prints as its parts do,
    /// with brackets and commas around them — so printing is recursive
    /// even though a print macro's argument list is not.
    fn format_one(&self, stream: &Stream, v: FnValue, fmt: &mut String, operands: &mut Vec<String>, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<(), CompileError> {
        {
            {
                {
                    match v.ty {
                        // ATS writes a tuple as `(a, b)`, and a nested one
                        // the same way — which is why this is the case
                        // that recurses.
                        LlvmType::Tuple(index) => {
                            fmt.push('(');
                            for (slot, part) in registry.tuple_parts(index).into_iter().enumerate() {
                                if slot > 0 {
                                    fmt.push_str(", ");
                                }
                                let addr = self.emit_slot_address(&v.reg, slot, fb);
                                let reg = fb.fresh_temp();
                                fb.line(format!("{reg} = load {}, ptr {addr}", llvm_ty_str(part)));
                                self.format_one(stream, FnValue { reg, ty: part }, fmt, operands, fb, registry, module)?;
                            }
                            fmt.push(')');
                        }
                        LlvmType::I64 => { fmt.push_str("%ld"); operands.push(format!("i64 {}", v.reg)); }
                        LlvmType::I8Ptr => { fmt.push_str("%s"); operands.push(format!("ptr {}", v.reg)); }
                        // ATS prints a bool as the word; a `select` picks
                        // between two constants, so no branch is needed.
                        LlvmType::I1 => {
                            let t = module.add_string("true");
                            let f = module.add_string("false");
                            let reg = fb.fresh_temp();
                            fb.line(format!("{reg} = select i1 {}, ptr {t}, ptr {f}", v.reg));
                            fmt.push_str("%s");
                            operands.push(format!("ptr {reg}"));
                        }
                        LlvmType::I32 => { fmt.push_str("%d"); operands.push(format!("i32 {}", v.reg)); }
                        // varargs promote a byte to an int, so the
                        // operand must be widened to match.
                        LlvmType::F64 => { fmt.push_str("%f"); operands.push(format!("double {}", v.reg)); }
                        LlvmType::I8 => {
                            let reg = fb.fresh_temp();
                            fb.line(format!("{reg} = sext i8 {} to i32", v.reg));
                            fmt.push_str("%c");
                            operands.push(format!("i32 {reg}"));
                        }
                        LlvmType::Argv => return Err(CompileError::emit("cannot print `argv` itself; index it first")),
                        LlvmType::Never => return Err(CompileError::emit("cannot print the result of an expression that never returns")),
                        // A list prints as its elements, comma-separated.
                        // That cannot be a placeholder — how many there
                        // are is not known until the list is walked — so
                        // whatever format is pending is flushed and the
                        // walk emitted in its place.
                        LlvmType::Data(index) if self.list_element(index, registry).is_some() => {
                            if !fmt.is_empty() || !operands.is_empty() {
                                self.emit_printf(stream.clone(), fmt, operands, fb, module);
                                fmt.clear();
                                operands.clear();
                            }
                            self.emit_list_print(stream, &v, index, fb, registry, module)?;
                        }
                        LlvmType::Data(_) => return Err(CompileError::emit("cannot print a datatype value; match on it first")),

                        LlvmType::Array(_) => return Err(CompileError::emit("cannot print an array; index it first")),
                        LlvmType::Closure(_) => return Err(CompileError::emit("cannot print a function")),
                        LlvmType::Lazy(_) => return Err(CompileError::emit("cannot print a stream; force it with `!` first")),
                        LlvmType::Record(_) => return Err(CompileError::emit("cannot print a record; name a field of it")),
                        LlvmType::FileRef => return Err(CompileError::emit("cannot print a FILEref; it names a stream, it is not data")),
                        LlvmType::Void => return Err(CompileError::emit("cannot print a void value")),
                    }
                }
            }
        }
        Ok(())
    }

    /// Emit the call itself.  Writing to stderr costs one extra load,
    /// because `stderr` is a libc *variable* holding the stream.
    fn emit_printf(&self, stream: Stream, fmt: &str, operands: &[String], fb: &mut FnBuilder, module: &mut ModuleBuilder) {
        let fmt_reg = module.add_format(fmt);
        let mut tail = String::new();
        if !operands.is_empty() {
            tail.push_str(", ");
            tail.push_str(&operands.join(", "));
        }
        let reg = fb.fresh_temp();
        match stream {
            Stream::Stdout => {
                fb.line(format!("{reg} = call i32 (ptr, ...) @printf(ptr {fmt_reg}{tail})"));
            }
            Stream::Stderr => {
                let s = fb.fresh_temp();
                fb.line(format!("{s} = load ptr, ptr @stderr"));
                fb.line(format!("{reg} = call i32 (ptr, ptr, ...) @fprintf(ptr {s}, ptr {fmt_reg}{tail})"));
            }
            Stream::Ref(stream_reg) => {
                fb.line(format!("{reg} = call i32 (ptr, ptr, ...) @fprintf(ptr {stream_reg}, ptr {fmt_reg}{tail})"));
            }
        }
    }

    /// The prelude functions the samples actually call.
    ///
    /// A real ATS program reaches these through `staload`, which pulls in
    /// prelude sources this compiler cannot yet read.  Rather than fail on
    /// a name every program uses, the handful that matter are implemented
    /// directly: some as calls to their libc equivalent, some as nothing
    /// at all.
    ///
    /// `Ok(None)` means "not a shim" — the caller falls through to the
    /// ordinary call path so the error stays "unknown function".
    fn emit_shim(&self, name: &str, ty_args: &[Ty], args: &[Expr], fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<Option<FnValue>, CompileError> {
        match name {
            // --- arrays ------------------------------------------------
            //
            // ATS's array library is a family of names over one machine
            // value: a pointer to cells.  The names differ in the *view*
            // each carries — who owns the cells, who may free them, who
            // may still read them — and views are erased before
            // emission.  So the shims below are short by construction:
            // what the library spends its vocabulary on is precisely
            // what the machine does not represent.
            "arrayptr_make_elt" | "array_ptr_alloc" | "arrayref_make_elt" => {
                let elem = match ty_args.first() {
                    Some(t) => llvm_type_in(t, registry)?,
                    None => LlvmType::I64,
                };
                let n = self.emit_expr(&args[0], fb, registry, module)?;
                self.require(n.ty, LlvmType::I64, "the length given to an array constructor")?;
                let ptr = self.emit_alloc_dynamic(&n.reg, fb, module);
                // `array_ptr_alloc` leaves the cells uninitialised; the
                // others fill them.  Uninitialised here still means
                // zeroed, because the arena is.
                if let Some(init) = args.get(1) {
                    let v = self.emit_expr_expecting(init, Some(elem), fb, registry, module)?;
                    self.emit_fill(&ptr, &n.reg, &v, fb);
                }
                Ok(Some(FnValue { reg: ptr, ty: LlvmType::Array(registry.intern_array(elem)) }))
            }
            // `arrayptr_foreach_env<a><env>(A, n, env)` — run the hole
            // `array_foreach$fwork` over every cell.
            "arrayptr_foreach_env" | "array_foreach_env" | "arrayref_foreach_env"
            | "arrayptr_foreach" | "array_foreach" | "arrayref_foreach" => {
                let a = self.emit_expr(&args[0], fb, registry, module)?;
                let LlvmType::Array(elem) = a.ty else {
                    return Err(CompileError::emit(format!(
                        "`{name}` takes an array, but its first argument has type {}",
                        llvm_ty_str(a.ty)
                    )));
                };
                let elem_ty = registry.array_elem(elem);
                let n = self.emit_expr(&args[1], fb, registry, module)?;
                self.require(n.ty, LlvmType::I64, "an array length")?;
                let hole = self.require_hole("array_foreach$fwork", registry)?;
                let id = fb.fresh_block_id();
                let (head, body, done) = (
                    format!("foreach.head.{id}"),
                    format!("foreach.body.{id}"),
                    format!("foreach.done.{id}"),
                );
                let cell = fb.alloca(&format!("foreach.i.{id}"), LlvmType::I64);
                fb.line("store i64 0, ptr ".to_string() + &cell);
                fb.line(format!("br label %{head}"));
                fb.label(&head);
                let i = fb.fresh_temp();
                fb.line(format!("{i} = load i64, ptr {cell}"));
                let more = fb.fresh_temp();
                fb.line(format!("{more} = icmp slt i64 {i}, {}", n.reg));
                fb.line(format!("br i1 {more}, label %{body}, label %{done}"));
                fb.label(&body);
                let off = fb.fresh_temp();
                fb.line(format!("{off} = mul i64 {i}, {WORD}"));
                let addr = fb.fresh_temp();
                fb.line(format!("{addr} = getelementptr i8, ptr {}, i64 {off}", a.reg));
                let x = fb.fresh_temp();
                fb.line(format!("{x} = load {}, ptr {addr}", llvm_ty_str(elem_ty)));
                let bound = FnValue { reg: x, ty: elem_ty };
                self.inline_hole(&hole, &[bound], args.get(2), fb, registry, module)?;
                let next = fb.fresh_temp();
                fb.line(format!("{next} = add i64 {i}, 1"));
                fb.line(format!("store i64 {next}, ptr {cell}"));
                fb.line(format!("br label %{head}"));
                fb.label(&done);
                // The library's `foreach` reports how many elements it
                // handled; a caller that does not care writes `val _ =`.
                let processed = fb.fresh_temp();
                fb.line(format!("{processed} = load i64, ptr {cell}"));
                Ok(Some(FnValue { reg: processed, ty: LlvmType::I64 }))
            }
            // `intrange_foreach(lo, hi)` — run the hole
            // `intrange_foreach$fwork` on each integer in the range.
            "intrange_foreach" | "intrange_foreach_env" => {
                let lo = self.emit_expr(&args[0], fb, registry, module)?;
                let hi = self.emit_expr(&args[1], fb, registry, module)?;
                self.require(lo.ty, LlvmType::I64, name)?;
                self.require(hi.ty, LlvmType::I64, name)?;
                let hole = self.require_hole("intrange_foreach$fwork", registry)?;
                let id = fb.fresh_block_id();
                let (head, body, done) = (
                    format!("irange.head.{id}"),
                    format!("irange.body.{id}"),
                    format!("irange.done.{id}"),
                );
                let cell = fb.alloca(&format!("irange.i.{id}"), LlvmType::I64);
                fb.line(format!("store i64 {}, ptr {cell}", lo.reg));
                fb.line(format!("br label %{head}"));
                fb.label(&head);
                let i = fb.fresh_temp();
                fb.line(format!("{i} = load i64, ptr {cell}"));
                let more = fb.fresh_temp();
                fb.line(format!("{more} = icmp slt i64 {i}, {}", hi.reg));
                fb.line(format!("br i1 {more}, label %{body}, label %{done}"));
                fb.label(&body);
                let bound = FnValue { reg: i.clone(), ty: LlvmType::I64 };
                self.inline_hole(&hole, &[bound], args.get(2), fb, registry, module)?;
                let next = fb.fresh_temp();
                fb.line(format!("{next} = add i64 {i}, 1"));
                fb.line(format!("store i64 {next}, ptr {cell}"));
                fb.line(format!("br label %{head}"));
                fb.label(&done);
                let processed = fb.fresh_temp();
                fb.line(format!("{processed} = sub i64 {}, {}", hi.reg, lo.reg));
                Ok(Some(FnValue { reg: processed, ty: LlvmType::I64 }))
            }
            // `string_foreach_env<env>(s, env)` — the same over a
            // string's characters, with an optional `$cont` hole deciding
            // whether to keep going.
            "string_foreach_env" | "string_foreach" => {
                let s = self.emit_expr(&args[0], fb, registry, module)?;
                self.require(s.ty, LlvmType::I8Ptr, "the string given to `string_foreach`")?;
                let hole = self.require_hole("string_foreach$fwork", registry)?;
                let cont = registry.holes.get("string_foreach$cont").cloned();
                let id = fb.fresh_block_id();
                let (head, body, done) = (
                    format!("sforeach.head.{id}"),
                    format!("sforeach.body.{id}"),
                    format!("sforeach.done.{id}"),
                );
                let cell = fb.alloca(&format!("sforeach.i.{id}"), LlvmType::I64);
                fb.line("store i64 0, ptr ".to_string() + &cell);
                fb.line(format!("br label %{head}"));
                fb.label(&head);
                let i = fb.fresh_temp();
                fb.line(format!("{i} = load i64, ptr {cell}"));
                let addr = fb.fresh_temp();
                fb.line(format!("{addr} = getelementptr i8, ptr {}, i64 {i}", s.reg));
                let c = fb.fresh_temp();
                fb.line(format!("{c} = load i8, ptr {addr}"));
                let more = fb.fresh_temp();
                fb.line(format!("{more} = icmp ne i8 {c}, 0"));
                // The `$cont` hole runs before the character is
                // processed: it is the loop's condition, not its body.
                let more = match &cont {
                    None => more,
                    Some(k) => {
                        let keep = format!("sforeach.cont.{id}");
                        fb.line(format!("br i1 {more}, label %{keep}, label %{done}"));
                        fb.label(&keep);
                        let bound = FnValue { reg: c.clone(), ty: LlvmType::I8 };
                        let v = self.inline_hole(k, &[bound], args.get(1), fb, registry, module)?;
                        self.require(v.ty, LlvmType::I1, "`string_foreach$cont`")?;
                        v.reg
                    }
                };
                fb.line(format!("br i1 {more}, label %{body}, label %{done}"));
                fb.label(&body);
                let bound = FnValue { reg: c, ty: LlvmType::I8 };
                self.inline_hole(&hole, &[bound], args.get(1), fb, registry, module)?;
                let next = fb.fresh_temp();
                fb.line(format!("{next} = add i64 {i}, 1"));
                fb.line(format!("store i64 {next}, ptr {cell}"));
                fb.line(format!("br label %{head}"));
                fb.label(&done);
                // The library's `foreach` reports how many elements it
                // handled; a caller that does not care writes `val _ =`.
                let processed = fb.fresh_temp();
                fb.line(format!("{processed} = load i64, ptr {cell}"));
                Ok(Some(FnValue { reg: processed, ty: LlvmType::I64 }))
            }
            // --- strings as pointers ---------------------------------
            //
            // ATS's string library works on a `string(n)` — a pointer
            // whose length is a static index.  With the index erased,
            // every one of these is pointer arithmetic on a NUL-
            // terminated run of bytes, which is what a `string` already
            // is here.
            "string_test_at" | "string_get_at" | "string_get_at_size" => {
                let [s, i] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes a string and an index")));
                };
                let sv = self.emit_expr(s, fb, registry, module)?;
                self.require(sv.ty, LlvmType::I8Ptr, name)?;
                let iv = self.emit_expr(i, fb, registry, module)?;
                let iv = self.emit_numeric_cast(iv, LlvmType::I64, fb)?;
                let addr = fb.fresh_temp();
                fb.line(format!("{addr} = getelementptr i8, ptr {}, i64 {}", sv.reg, iv.reg));
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = load i8, ptr {addr}"));
                Ok(Some(FnValue { reg, ty: LlvmType::I8 }))
            }
            // `s.tail()` — the string starting one character later.
            "string_tail" | "string1_tail" | "tail" => {
                let [s] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one string")));
                };
                let sv = self.emit_expr(s, fb, registry, module)?;
                self.require(sv.ty, LlvmType::I8Ptr, name)?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = getelementptr i8, ptr {}, i64 1", sv.reg));
                Ok(Some(FnValue { reg, ty: LlvmType::I8Ptr }))
            }
            // `ptr_add<char>(p, n)` / `ptr_succ<char>(p)` — move a
            // pointer by whole elements.
            "ptr_add" | "ptr_succ" | "ptr_pred" | "ptr0_add" => {
                let elem = match ty_args.first() {
                    Some(t) => llvm_type_in(t, registry)?,
                    None => LlvmType::I8,
                };
                let width = if elem == LlvmType::I8 { 1 } else { WORD as i64 };
                let pv = self.emit_expr(&args[0], fb, registry, module)?;
                let step = match args.get(1) {
                    Some(e) => {
                        let v = self.emit_expr(e, fb, registry, module)?;
                        self.emit_numeric_cast(v, LlvmType::I64, fb)?.reg
                    }
                    None => if name.ends_with("pred") { "-1".into() } else { "1".into() },
                };
                let off = fb.fresh_temp();
                fb.line(format!("{off} = mul i64 {step}, {width}"));
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = getelementptr i8, ptr {}, i64 {off}", pv.reg));
                Ok(Some(FnValue { reg, ty: pv.ty }))
            }
            // `$UN.ptr0_get<char>(p)` — read what a pointer points at.
            "ptr0_get" | "ptr_get" | "ptrget" => {
                let elem = match ty_args.first() {
                    Some(t) => llvm_type_in(t, registry)?,
                    None => LlvmType::I8,
                };
                let pv = self.emit_expr(&args[0], fb, registry, module)?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = load {}, ptr {}", llvm_ty_str(elem), pv.reg));
                Ok(Some(FnValue { reg, ty: elem }))
            }
            // `$UN.cast{t}(e)` — an assertion to the type checker that
            // this value may be read as a `t`.  Every type here that a
            // cast is written between shares one machine representation,
            // so the cast moves no bits; where it does not, the type
            // arguments say which conversion is meant.
            "cast" | "cast2int" | "castvwtp0" | "castvwtp1" | "string2ptr" | "ptr2string"
            | "g1ofg0_string" | "g0ofg1_string" | "string1_of_string0" | "string_of_strptr" => {
                let [x] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one value")));
                };
                let v = self.emit_expr(x, fb, registry, module)?;
                match ty_args.first().map(|t| llvm_type_in(t, registry)).transpose()? {
                    Some(want) if want != v.ty => {
                        let reinterpreted = FnValue { reg: v.reg.clone(), ty: want };
                        // A numeric conversion is a real instruction; a
                        // cast between two pointer-shaped types is not.
                        Ok(Some(self.emit_numeric_cast(v, want, fb).unwrap_or(reinterpreted)))
                    }
                    _ => Ok(Some(v)),
                }
            }
            // `double(n)`, `int2double(n)` — a number as a float, and
            // back.
            "double" | "int2double" | "g0int2float" | "g1int2float" | "double_of_int"
            | "g0int2float_int_double" | "g1int2float_int_double" | "g0i2f" | "g1i2f" => {
                let [x] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one number")));
                };
                let v = self.emit_expr(x, fb, registry, module)?;
                Ok(Some(self.emit_numeric_cast(v, LlvmType::F64, fb)?))
            }
            "int_of_double" | "double2int" | "g0float2int" | "g1float2int" => {
                let [x] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one number")));
                };
                let v = self.emit_expr(x, fb, registry, module)?;
                if v.ty == LlvmType::F64 {
                    let reg = fb.fresh_temp();
                    fb.line(format!("{reg} = fptosi double {} to i64", v.reg));
                    return Ok(Some(FnValue { reg, ty: LlvmType::I64 }));
                }
                Ok(Some(self.emit_numeric_cast(v, LlvmType::I64, fb)?))
            }
            // --- references ------------------------------------------
            //
            // A `ref` is one cell, which is a one-slot tuple: sharing
            // that representation is what makes `!r` and `!r := v` fall
            // out of the slot machinery tuples already needed.
            "ref" | "ref_make_elt" | "ref_make_viewptr" | "refc_make_elt" => {
                let [x] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one value")));
                };
                let v = self.emit_expr(x, fb, registry, module)?;
                // `ref_make_viewptr (pf | p)` is handed a pointer to
                // storage that already exists; with the proof erased,
                // that pointer *is* the reference.
                if matches!(v.ty, LlvmType::Tuple(_)) && name == "ref_make_viewptr" {
                    return Ok(Some(v));
                }
                let ptr = self.emit_alloc(WORD, fb, module);
                fb.line(format!("store {} {}, ptr {ptr}", llvm_ty_str(v.ty), v.reg));
                Ok(Some(FnValue { reg: ptr, ty: LlvmType::Tuple(registry.intern_tuple(vec![v.ty])) }))
            }
            // `addr@ x` — where `x` lives.  A top-level `var` already
            // *is* its cell, so its address is itself; a proof of the
            // view is erased and never reaches here.
            "addr@" | "view@" | "ptrof" => {
                let [x] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one variable")));
                };
                Ok(Some(self.emit_expr(x, fb, registry, module)?))
            }
            // The arithmetic ATS spells out when it wants to be explicit
            // about *which* integer sort is meant.  `g0` is unindexed and
            // `g1` indexed, `n` means the operands are non-negative — all
            // of it static, and all of it one machine instruction.
            "g0int_add" | "g1int_add" | "g0int_sub" | "g1int_sub" | "g0int_mul"
            | "g1int_mul" | "g0int_div" | "g1int_div" | "g0int_mod" | "g1int_mod"
            | "g0int_nmod" | "g1int_nmod" | "g0int_ndiv" | "g1int_ndiv" => {
                let [a, b] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes two numbers")));
                };
                let op = match &name[name.len() - 3..] {
                    "add" => BinOp::Add,
                    "sub" => BinOp::Sub,
                    "mul" => BinOp::Mul,
                    "div" => BinOp::Div,
                    _ => BinOp::Mod,
                };
                Ok(Some(self.emit_binop(op, a, b, fb, registry, module)?))
            }
            // `list_is_nil (xs)` / `list_is_cons (xs)` — the two questions
            // a program asks a list without taking it apart.
            //
            // Emitted here rather than written in the prelude because
            // the answer does not depend on what the list holds: it is
            // the tag, and every instance of the datatype tags its
            // constructors the same way.  A prelude version would be a
            // template, and a template needs an instance the caller
            // often has no way to name.
            "list_is_nil" | "list_is_cons" | "list0_is_nil" | "list0_is_cons"
            | "list_vt_is_nil" | "list_vt_is_cons" => {
                let [xs] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one list")));
                };
                let v = self.emit_expr(xs, fb, registry, module)?;
                let LlvmType::Data(index) = v.ty else {
                    return Err(CompileError::emit(format!(
                        "`{name}` takes a list, but this value has type {}",
                        llvm_ty_str(v.ty)
                    )));
                };
                let nil = registry
                    .ctors
                    .get("list0_nil")
                    .and_then(|cs| cs.iter().find(|c| c.datatype == index))
                    .ok_or_else(|| {
                        CompileError::emit(format!("`{name}` takes a list, and this is not one"))
                    })?;
                let tag = fb.fresh_temp();
                fb.line(format!("{tag} = load i64, ptr {}", v.reg));
                let reg = fb.fresh_temp();
                let test = if name.ends_with("is_nil") { "eq" } else { "ne" };
                fb.line(format!("{reg} = icmp {test} i64 {tag}, {}", nil.tag));
                Ok(Some(FnValue { reg, ty: LlvmType::I1 }))
            }
            // `fprint_val (out, x)` — the default of ATS's printing
            // protocol, for the types the compiler already knows how to
            // write.  A program supplies its own instances, and one of
            // those wins over this: monomorphisation only leaves the
            // call here when nothing was supplied.
            "fprint_val" | "print_val" | "prerr_val" => {
                let (stream, value) = match (name, args) {
                    ("fprint_val", [out, x]) => {
                        (self.emit_stream_argument(name, out, fb, registry, module)?, x)
                    }
                    ("print_val", [x]) => (Stream::Stdout, x),
                    ("prerr_val", [x]) => (Stream::Stderr, x),
                    _ => {
                        return Err(CompileError::emit(format!(
                            "`{name}` takes a value to print"
                        )))
                    }
                };
                self.emit_format(&stream, std::slice::from_ref(value), false, fb, registry, module)?;
                Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Void }))
            }
            // `malloc_gc (n)` — `n` bytes of storage.  It comes from the
            // arena like everything else: the `_gc` in the name says the
            // caller need not free it, which is exactly the arena's
            // promise, and `mfree_gc` is then nothing to do.
            "malloc_gc" | "malloc" | "malloc_ext" => {
                let [n] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes a size")));
                };
                let v = self.emit_expr(n, fb, registry, module)?;
                self.require(v.ty, LlvmType::I64, name)?;
                let ptr = self.emit_alloc_bytes(&v.reg, fb, module);
                Ok(Some(FnValue { reg: ptr, ty: LlvmType::I8Ptr }))
            }
            "mfree_gc" | "free_gc" | "mfree" => {
                for a in args {
                    self.emit_expr(a, fb, registry, module)?;
                }
                Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Void }))
            }
            // `fgets (buf, n, filr)` — a line into the caller's buffer,
            // or null at end of input.
            "fgets" => {
                let [buf, n, filr] = args else {
                    return Err(CompileError::emit("`fgets` takes a buffer, a size and a stream"));
                };
                let b = self.emit_expr(buf, fb, registry, module)?;
                let count = self.emit_expr(n, fb, registry, module)?;
                self.require(count.ty, LlvmType::I64, "`fgets`")?;
                let f = self.emit_expr(filr, fb, registry, module)?;
                self.require(f.ty, LlvmType::FileRef, "`fgets`")?;
                module.externs.insert("declare ptr @fgets(ptr, i32, ptr)");
                let narrowed = fb.fresh_temp();
                fb.line(format!("{narrowed} = trunc i64 {} to i32", count.reg));
                let reg = fb.fresh_temp();
                fb.line(format!(
                    "{reg} = call ptr @fgets(ptr {}, i32 {narrowed}, ptr {})",
                    b.reg, f.reg
                ));
                Ok(Some(FnValue { reg, ty: LlvmType::I8Ptr }))
            }
            "fputs" | "fputs_exn" => {
                let [s, filr] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes a string and a stream")));
                };
                let sv = self.emit_expr(s, fb, registry, module)?;
                self.require(sv.ty, LlvmType::I8Ptr, name)?;
                let stream = self.emit_stream_argument(name, filr, fb, registry, module)?;
                self.emit_printf(stream, "%s", &[format!("ptr {}", sv.reg)], fb, module);
                Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Void }))
            }
            // The libc random numbers ATS reaches for.  Seeding from the
            // clock is one call in C and three here, which is why ATS
            // programs write it as a `%{ ... %}` block — and why that
            // block, being C this compiler never sees, has to be
            // answered by name.
            "drand48" | "srand48_with_time" | "srand48" | "rand" | "srand" | "random" => {
                for a in args {
                    self.emit_expr(a, fb, registry, module)?;
                }
                match name {
                    "drand48" => {
                        module.externs.insert("declare double @drand48()");
                        let reg = fb.fresh_temp();
                        fb.line(format!("{reg} = call double @drand48()"));
                        Ok(Some(FnValue { reg, ty: LlvmType::F64 }))
                    }
                    "rand" | "random" => {
                        module.externs.insert("declare i32 @rand()");
                        let raw = fb.fresh_temp();
                        let reg = fb.fresh_temp();
                        fb.line(format!("{raw} = call i32 @rand()"));
                        fb.line(format!("{reg} = sext i32 {raw} to i64"));
                        Ok(Some(FnValue { reg, ty: LlvmType::I64 }))
                    }
                    // Seeded from the clock: `srand48(time(0))`.
                    _ => {
                        module.externs.insert("declare i64 @time(ptr)");
                        module.externs.insert("declare void @srand48(i64)");
                        module.externs.insert("declare void @srand(i32)");
                        let now = fb.fresh_temp();
                        fb.line(format!("{now} = call i64 @time(ptr null)"));
                        if name == "srand" {
                            let narrowed = fb.fresh_temp();
                            fb.line(format!("{narrowed} = trunc i64 {now} to i32"));
                            fb.line(format!("call void @srand(i32 {narrowed})"));
                        } else {
                            fb.line(format!("call void @srand48(i64 {now})"));
                        }
                        Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Void }))
                    }
                }
            }
            // `compare (x, y)` — the *sign* of the ordering, as an int.
            // Subtracting would overflow; two comparisons cannot.
            "compare" | "g0int_compare" | "g1int_compare" | "gcompare_val_val" => {
                let [a, b] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes two values")));
                };
                let av = self.emit_expr(a, fb, registry, module)?;
                let bv = self.emit_expr(b, fb, registry, module)?;
                if av.ty != bv.ty {
                    return Err(CompileError::emit(format!("`{name}` compares two values of one type")));
                }
                let (gt, lt) = (fb.fresh_temp(), fb.fresh_temp());
                let (gtn, ltn) = (fb.fresh_temp(), fb.fresh_temp());
                let ty = llvm_ty_str(av.ty);
                let (ord_gt, ord_lt) = match av.ty {
                    LlvmType::F64 => ("fcmp ogt", "fcmp olt"),
                    _ => ("icmp sgt", "icmp slt"),
                };
                fb.line(format!("{gt} = {ord_gt} {ty} {}, {}", av.reg, bv.reg));
                fb.line(format!("{lt} = {ord_lt} {ty} {}, {}", av.reg, bv.reg));
                fb.line(format!("{gtn} = zext i1 {gt} to i64"));
                fb.line(format!("{ltn} = zext i1 {lt} to i64"));
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = sub i64 {gtn}, {ltn}"));
                Ok(Some(FnValue { reg, ty: LlvmType::I64 }))
            }
            // `min`/`max` on two numbers.
            "min" | "max" | "g0int_min" | "g0int_max" | "g1int_min" | "g1int_max" => {
                let [a, b] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes two numbers")));
                };
                let av = self.emit_expr(a, fb, registry, module)?;
                let bv = self.emit_expr(b, fb, registry, module)?;
                self.require(av.ty, LlvmType::I64, name)?;
                self.require(bv.ty, LlvmType::I64, name)?;
                let pick = if name.contains("min") { "slt" } else { "sgt" };
                let c = fb.fresh_temp();
                fb.line(format!("{c} = icmp {pick} i64 {}, {}", av.reg, bv.reg));
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = select i1 {c}, i64 {}, i64 {}", av.reg, bv.reg));
                Ok(Some(FnValue { reg, ty: LlvmType::I64 }))
            }
            // `succ`/`pred` — one more, one less.  ATS uses them
            // wherever a *static* index must move by exactly one, so
            // they appear far more often than `+ 1` does.
            "succ" | "pred" | "isucc" | "ipred" | "succ1" | "pred1" | "g1int_succ" | "g1int_pred" => {
                let [x] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one number")));
                };
                let v = self.emit_expr(x, fb, registry, module)?;
                self.require(v.ty, LlvmType::I64, name)?;
                let op = if name.contains("succ") { "add" } else { "sub" };
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = {op} i64 {}, 1", v.reg));
                Ok(Some(FnValue { reg, ty: LlvmType::I64 }))
            }
            // The character classifications.  Emitted as comparisons
            // rather than calls to libc's: `isdigit` and friends are
            // locale-dependent there, and ATS's are not.
            "isdigit" | "isalpha" | "isalnum" | "isspace" | "isupper" | "islower"
            | "ispunct" | "isxdigit" | "char_isdigit" | "char_isalpha" | "char_isspace" => {
                let [c] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one character")));
                };
                let v = self.emit_expr(c, fb, registry, module)?;
                let c = self.emit_numeric_cast(v, LlvmType::I64, fb)?;
                let reg = self.emit_char_class(name.trim_start_matches("char_"), &c.reg, fb);
                Ok(Some(FnValue { reg, ty: LlvmType::I1 }))
            }
            "toupper" | "tolower" | "char_toupper" | "char_tolower" => {
                let [c] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one character")));
                };
                let v = self.emit_expr(c, fb, registry, module)?;
                let (lo, hi, delta) =
                    if name.ends_with("upper") { ('a', 'z', -32) } else { ('A', 'Z', 32) };
                let ge = fb.fresh_temp();
                fb.line(format!("{ge} = icmp sge i8 {}, {}", v.reg, lo as u8));
                let le = fb.fresh_temp();
                fb.line(format!("{le} = icmp sle i8 {}, {}", v.reg, hi as u8));
                let both = fb.fresh_temp();
                fb.line(format!("{both} = and i1 {ge}, {le}"));
                let shifted = fb.fresh_temp();
                fb.line(format!("{shifted} = add i8 {}, {delta}", v.reg));
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = select i1 {both}, i8 {shifted}, i8 {}", v.reg));
                Ok(Some(FnValue { reg, ty: LlvmType::I8 }))
            }
            // `arrayptr_make_intrange(lo, hi)` — the cells `lo..hi-1`.
            "arrayptr_make_intrange" | "arrayref_make_intrange" => {
                let lo = self.emit_expr(&args[0], fb, registry, module)?;
                let hi = self.emit_expr(&args[1], fb, registry, module)?;
                let n = fb.fresh_temp();
                fb.line(format!("{n} = sub i64 {}, {}", hi.reg, lo.reg));
                let ptr = self.emit_alloc_dynamic(&n, fb, module);
                self.emit_fill_intrange(&ptr, &lo.reg, &n, fb);
                Ok(Some(FnValue { reg: ptr, ty: LlvmType::Array(registry.intern_array(LlvmType::I64)) }))
            }
            // The arena owns every cell and outlives every program, so
            // freeing is a promise already kept.
            "arrayptr_free" | "array_ptr_free" | "arrayptr_addback" | "arrayref_free" => {
                for a in args {
                    self.emit_expr(a, fb, registry, module)?;
                }
                Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Void }))
            }
            // `fprint_tupval2<a,b>(out, @(x, y))` — print a tuple.  The
            // arity is in the name because ATS has no variadic template,
            // but the *shape* is in the value, so one arm serves them
            // all: the format is read off the tuple's own components.
            name if name.starts_with("fprint_tupval") => {
                let Some((first, rest)) = args.split_first() else {
                    return Err(CompileError::emit(format!("`{name}` takes a stream and a tuple")));
                };
                let [tuple] = rest else {
                    return Err(CompileError::emit(format!("`{name}` takes a stream and a tuple")));
                };
                let stream = self.emit_stream_argument(name, first, fb, registry, module)?;
                let v = self.emit_expr(tuple, fb, registry, module)?;
                if !matches!(v.ty, LlvmType::Tuple(_)) {
                    return Err(CompileError::emit(format!(
                        "`{name}` prints a tuple, but this value has type {}",
                        llvm_ty_str(v.ty)
                    )));
                }
                let mut fmt = String::new();
                let mut operands = Vec::new();
                self.format_one(&stream, v, &mut fmt, &mut operands, fb, registry, module)?;
                self.emit_printf(stream, &fmt, &operands, fb, module);
                Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Void }))
            }
            // `$raise E` — throw.  With no handler anywhere in the
            // subset, the whole of what a raise can do is say which
            // exception it was and stop; its type is `Never`, so it
            // still fits wherever a value was wanted.
            "$raise" => {
                let name = match args.first() {
                    Some(Expr::StrLit(s)) => s.clone(),
                    _ => "exception".to_string(),
                };
                self.emit_printf(Stream::Stderr, &format!("exit(ATS): uncaught {name}\n"), &[], fb, module);
                fb.line("call void @exit(i32 1)");
                // `unreachable` terminates the block, exactly as `exit`
                // does.  No label follows: a raise is the end of its
                // block, and an empty block after it would have no
                // terminator of its own.
                fb.line("unreachable");
                Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Never }))
            }
            // `$delay(e)` — suspend `e`.  The parser has already wrapped
            // the body in a nullary lambda, because suspending is what a
            // lambda does; what is built here is the one thing a lambda
            // cannot express, the cell that remembers the answer.
            "$delay" => {
                let [thunk] = args else {
                    return Err(CompileError::emit("`$delay` suspends exactly one expression"));
                };
                let f = self.emit_expr(thunk, fb, registry, module)?;
                let LlvmType::Closure(index) = f.ty else {
                    return Err(CompileError::emit("internal: `$delay` was not given a thunk"));
                };
                let sig = registry.closure_sig(index);
                if !sig.params.is_empty() {
                    return Err(CompileError::emit("internal: a delayed thunk takes no arguments"));
                }
                let cell = self.emit_alloc(WORD * 2, fb, module);
                fb.line(format!("store ptr {}, ptr {cell}", f.reg));
                let answer = self.emit_slot_address(&cell, 1, fb);
                fb.line(format!("store ptr null, ptr {answer}"));
                Ok(Some(FnValue { reg: cell, ty: LlvmType::Lazy(registry.intern_lazy(sig.ret)) }))
            }
            // Handing out the pointer inside an `arrayptr`, and taking it
            // back, are proof steps: the value does not move.
            "arrayptr_takeout_viewptr" | "arrayptr_takeout" | "arrayptr2ptr"
            | "arrayptr_refize" | "ptr2arrayptr" | "ptrcast" | "arrayptr_addback"
            | "list_vt2t" | "list_t2vt" | "unsafe_cast" | "ignoret" => {
                let v = self.emit_expr(&args[0], fb, registry, module)?;
                Ok(Some(v))
            }
            // The integer conversions ATS uses to move between its signed
            // and unsigned *static* sorts.  One machine word throughout.
            "g1i2u" | "g0i2u" | "g1int2uint" | "g0int2uint" | "g1u2i" | "g0u2i"
            | "g1uint2int" | "g0uint2int" | "i2sz" | "sz2i" | "g1i2sz" | "g0i2sz"
            | "sz2u" | "u2sz" | "g1sz2i" | "g0sz2i" => {
                let v = self.emit_expr(&args[0], fb, registry, module)?;
                Ok(Some(v))
            }
            // `gnumber_int<t>(n)` — the number `n` as a `t`.  ATS uses it
            // to write a literal in code that is generic over the numeric
            // type, which is exactly what a template body cannot do.
            "gnumber_int" | "gnumber_int_int" => {
                let [n] = args else { return Err(CompileError::emit("`gnumber_int` takes one int")) };
                let v = self.emit_expr(n, fb, registry, module)?;
                self.require(v.ty, LlvmType::I64, "`gnumber_int`")?;
                let want = match ty_args.first() {
                    Some(t) => llvm_type_in(t, registry)?,
                    None => LlvmType::I64,
                };
                Ok(Some(self.emit_numeric_cast(v, want, fb)?))
            }
            // The generic arithmetic an `overload` reaches for: one side
            // is an int, the other whatever the caller is generic over.
            "gmul_int_val" | "gadd_int_val" | "gsub_int_val" | "gdiv_int_val"
            | "gmul_val_int" | "gadd_val_int" | "gsub_val_int" | "gdiv_val_int" => {
                let [l, r] = args else { return Err(CompileError::emit(format!("`{name}` takes two arguments"))) };
                let lv = self.emit_expr(l, fb, registry, module)?;
                let rv = self.emit_expr(r, fb, registry, module)?;
                let op = match &name[1..4] {
                    "mul" => BinOp::Mul,
                    "add" => BinOp::Add,
                    "sub" => BinOp::Sub,
                    _ => BinOp::Div,
                };
                Ok(Some(self.emit_promoted(op, lv, rv, fb)?))
            }
            "ggt_val_int" | "glt_val_int" | "gge_val_int" | "gle_val_int"
            | "geq_val_int" | "gneq_val_int" => {
                let [l, r] = args else { return Err(CompileError::emit(format!("`{name}` takes two arguments"))) };
                let lv = self.emit_expr(l, fb, registry, module)?;
                let rv = self.emit_expr(r, fb, registry, module)?;
                let op = match &name[1..3] {
                    "gt" => BinOp::Gt,
                    "lt" => BinOp::Lt,
                    "ge" => BinOp::Ge,
                    "le" => BinOp::Le,
                    "eq" => BinOp::Eq,
                    _ => BinOp::Ne,
                };
                Ok(Some(self.emit_promoted(op, lv, rv, fb)?))
            }
            // ATS's integers come in two *sorts*: `g0int`, which the type
            // checker knows nothing about, and `g1int`, which it tracks.
            // The distinction is entirely static, so moving between them
            // changes no machine value and emits no instruction.
            "g1ofg0" | "g0ofg1" | "g1int2int" | "g0int2int" | "int2int"
            | "g1ofg0_int" | "g0ofg1_int" => {
                let [arg] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes exactly one argument")));
                };
                Ok(Some(self.emit_expr(arg, fb, registry, module)?))
            }
            // `exit` does not return, so it has no result type to check
            // against: it ends the block with `unreachable`.
            "exit" | "exit_errmsg" => {
                let [code] = args else {
                    return Err(CompileError::emit("`exit` takes exactly one argument"));
                };
                let v = self.emit_expr(code, fb, registry, module)?;
                if v.ty != LlvmType::I64 {
                    return Err(CompileError::emit(format!(
                        "`exit` expects an int status, got {}",
                        llvm_ty_str(v.ty)
                    )));
                }
                let narrowed = fb.fresh_temp();
                fb.line(format!("{narrowed} = trunc i64 {} to i32", v.reg));
                fb.line(format!("call void @exit(i32 {narrowed})"));
                fb.line("unreachable");
                Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Never }))
            }
            // --- files ------------------------------------------------
            "fileref_getc" | "fileref_get_char" => {
                let [f] = args else {
                    return Err(CompileError::emit("`fileref_getc` takes one stream"));
                };
                let fv = self.emit_expr(f, fb, registry, module)?;
                self.require(fv.ty, LlvmType::FileRef, "`fileref_getc`")?;
                module.externs.insert("declare i32 @fgetc(ptr)");
                let raw = fb.fresh_temp();
                fb.line(format!("{raw} = call i32 @fgetc(ptr {})", fv.reg));
                // EOF is -1, so the widening must keep the sign.
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = sext i32 {raw} to i64"));
                Ok(Some(FnValue { reg, ty: LlvmType::I64 }))
            }
            "fileref_putc" | "fileref_put_char" => {
                let [f, c] = args else {
                    return Err(CompileError::emit("`fileref_putc` takes a stream and a character"));
                };
                let fv = self.emit_expr(f, fb, registry, module)?;
                self.require(fv.ty, LlvmType::FileRef, "`fileref_putc`")?;
                let cv = self.emit_expr(c, fb, registry, module)?;
                self.require(cv.ty, LlvmType::I64, "`fileref_putc`")?;
                module.externs.insert("declare i32 @fputc(i32, ptr)");
                let narrowed = fb.fresh_temp();
                fb.line(format!("{narrowed} = trunc i64 {} to i32", cv.reg));
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = call i32 @fputc(i32 {narrowed}, ptr {})", fv.reg));
                Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Void }))
            }
            "fileref_open_exn" | "fileref_open" => {
                let [path, mode] = args else {
                    return Err(CompileError::emit("`fileref_open_exn` takes a path and a mode"));
                };
                let pv = self.emit_expr(path, fb, registry, module)?;
                self.require(pv.ty, LlvmType::I8Ptr, "the path given to `fileref_open_exn`")?;
                let mv = self.emit_expr(mode, fb, registry, module)?;
                self.require(mv.ty, LlvmType::I8Ptr, "the mode given to `fileref_open_exn`")?;
                module.externs.insert("declare ptr @fopen(ptr, ptr)");
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = call ptr @fopen(ptr {}, ptr {})", pv.reg, mv.reg));
                // The `_exn` spelling promises to raise rather than return
                // a null stream, so the check belongs here.
                let id = fb.fresh_block_id();
                let (bad, ok) = (format!("open.fail.{id}"), format!("open.ok.{id}"));
                let failed = fb.fresh_temp();
                fb.line(format!("{failed} = icmp eq ptr {reg}, null"));
                fb.line(format!("br i1 {failed}, label %{bad}, label %{ok}"));
                fb.label(&bad);
                self.emit_printf(Stream::Stderr, "exit(ATS): cannot open the file\n", &[], fb, module);
                fb.line("call void @exit(i32 1)");
                fb.line("unreachable");
                fb.label(&ok);
                Ok(Some(FnValue { reg, ty: LlvmType::FileRef }))
            }
            // `fileref_load<t>(f, x)` reads one value *into* `x`, so `x`
            // must be a `var` — a cell with an address — rather than a
            // `val`, which is a value with none.
            "fileref_load" | "fileref_load_int" => {
                let [f, target] = args else {
                    return Err(CompileError::emit("`fileref_load` takes a stream and a destination"));
                };
                let fv = self.emit_expr(f, fb, registry, module)?;
                self.require(fv.ty, LlvmType::FileRef, "`fileref_load`")?;
                let Expr::Var(name) = target else {
                    return Err(CompileError::emit("`fileref_load` must be given a `var` to read into"));
                };
                let Some(cell) = fb.cells.get(name).cloned() else {
                    return Err(CompileError::emit(format!(
                        "`fileref_load` reads into `{name}`, so it must be declared with `var`, not `val`"
                    )));
                };
                if cell.ty != LlvmType::I64 {
                    return Err(CompileError::emit("`fileref_load` can only read an int so far"));
                }
                module.externs.insert("declare i32 @fscanf(ptr, ptr, ...)");
                let fmt = module.add_format("%ld");
                let count = fb.fresh_temp();
                fb.line(format!(
                    "{count} = call i32 (ptr, ptr, ...) @fscanf(ptr {}, ptr {fmt}, ptr {})",
                    fv.reg, cell.ptr
                ));
                // `fscanf` reports how many items it converted; one means
                // the read succeeded.
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = icmp eq i32 {count}, 1"));
                Ok(Some(FnValue { reg, ty: LlvmType::I1 }))
            }
            "string_is_null" => {
                let [x] = args else { return Err(CompileError::emit("`string_is_null` takes one string")) };
                let v = self.emit_expr(x, fb, registry, module)?;
                self.require(v.ty, LlvmType::I8Ptr, "`string_is_null`")?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = icmp eq ptr {}, null", v.reg));
                Ok(Some(FnValue { reg, ty: LlvmType::I1 }))
            }
            // Read one line into the arena, without its newline.  A null
            // result means the stream had nothing left.
            //
            // It is built a character at a time rather than with
            // `getline`, which would allocate with `malloc` and leave the
            // caller holding memory nothing in the subset can free.  The
            // arena has no such problem.
            "fileref_get_line_string" | "fileref_get_line" => {
                let [f] = args else { return Err(CompileError::emit("`fileref_get_line_string` takes one stream")) };
                let fv = self.emit_expr(f, fb, registry, module)?;
                self.require(fv.ty, LlvmType::FileRef, "`fileref_get_line_string`")?;
                module.externs.insert("declare i32 @fgetc(ptr)");
                module.needs_heap = true;

                let id = fb.fresh_block_id();
                let (test, body, store, done, empty, finish) = (
                    format!("line.test.{id}"),
                    format!("line.body.{id}"),
                    format!("line.store.{id}"),
                    format!("line.done.{id}"),
                    format!("line.empty.{id}"),
                    format!("line.finish.{id}"),
                );
                // The line starts wherever the arena has got to; each
                // character extends it, so nothing needs to be moved.
                let start = fb.fresh_temp();
                fb.line(format!("{start} = load i64, ptr @.heap.off"));
                let entry = fb.cur_block.clone();
                fb.line(format!("br label %{test}"));

                fb.label(&test);
                let off = fb.fresh_temp();
                fb.line(format!("{off} = phi i64 [ {start}, %{entry} ], [ {next_off}, %{store} ]", next_off = format!("%t.next.{id}")));
                let ch = fb.fresh_temp();
                fb.line(format!("{ch} = call i32 @fgetc(ptr {})", fv.reg));
                let is_eof = fb.fresh_temp();
                fb.line(format!("{is_eof} = icmp eq i32 {ch}, -1"));
                fb.line(format!("br i1 {is_eof}, label %{done}, label %{body}"));

                fb.label(&body);
                let is_nl = fb.fresh_temp();
                fb.line(format!("{is_nl} = icmp eq i32 {ch}, 10"));
                fb.line(format!("br i1 {is_nl}, label %{finish}, label %{store}"));

                fb.label(&store);
                let addr = fb.fresh_temp();
                fb.line(format!("{addr} = getelementptr i8, ptr @.heap, i64 {off}"));
                let byte = fb.fresh_temp();
                fb.line(format!("{byte} = trunc i32 {ch} to i8"));
                fb.line(format!("store i8 {byte}, ptr {addr}"));
                fb.line(format!("%t.next.{id} = add i64 {off}, 1"));
                fb.line(format!("br label %{test}"));

                // End of file: a line was read only if anything came in.
                fb.label(&done);
                let nothing = fb.fresh_temp();
                fb.line(format!("{nothing} = icmp eq i64 {off}, {start}"));
                fb.line(format!("br i1 {nothing}, label %{empty}, label %{finish}"));

                fb.label(&empty);
                fb.line(format!("br label %{finish}"));

                fb.label(&finish);
                let ended = fb.fresh_temp();
                fb.line(format!("{ended} = phi i64 [ {off}, %{body} ], [ {off}, %{done} ], [ {off}, %{empty} ]"));
                let was_empty = fb.fresh_temp();
                fb.line(format!("{was_empty} = phi i1 [ false, %{body} ], [ false, %{done} ], [ true, %{empty} ]"));
                // Terminate the string and hand the arena back its space.
                let term = fb.fresh_temp();
                fb.line(format!("{term} = getelementptr i8, ptr @.heap, i64 {ended}"));
                fb.line(format!("store i8 0, ptr {term}"));
                let after = fb.fresh_temp();
                fb.line(format!("{after} = add i64 {ended}, 1"));
                fb.line(format!("store i64 {after}, ptr @.heap.off"));
                let text = fb.fresh_temp();
                fb.line(format!("{text} = getelementptr i8, ptr @.heap, i64 {start}"));
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = select i1 {was_empty}, ptr null, ptr {text}"));
                Ok(Some(FnValue { reg, ty: LlvmType::I8Ptr }))
            }
            "fileref_close" => {
                let [f] = args else {
                    return Err(CompileError::emit("`fileref_close` takes one stream"));
                };
                let fv = self.emit_expr(f, fb, registry, module)?;
                self.require(fv.ty, LlvmType::FileRef, "`fileref_close`")?;
                module.externs.insert("declare i32 @fclose(ptr)");
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = call i32 @fclose(ptr {})", fv.reg));
                Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Void }))
            }
            // --- the print shims, and characters ----------------------
            "print_char" | "prerr_char" => {
                let [c] = args else { return Err(CompileError::emit("`print_char` takes one character")) };
                let v = self.emit_expr(c, fb, registry, module)?;
                self.require(v.ty, LlvmType::I8, "`print_char`")?;
                let stream = if name.starts_with("prerr") { Stream::Stderr } else { Stream::Stdout };
                let widened = fb.fresh_temp();
                fb.line(format!("{widened} = sext i8 {} to i32", v.reg));
                self.emit_printf(stream, "%c", &[format!("i32 {widened}")], fb, module);
                Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Void }))
            }
            "print_int" | "print_string" | "print_bool" | "prerr_int" | "prerr_string" => {
                let [x] = args else { return Err(CompileError::emit(format!("`{name}` takes one argument"))) };
                let stream = if name.starts_with("prerr") { Stream::Stderr } else { Stream::Stdout };
                self.emit_format(&stream, std::slice::from_ref(x), false, fb, registry, module)?;
                Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Void }))
            }
            "print_newline" | "prerr_newline" => {
                let stream = if name.starts_with("prerr") { Stream::Stderr } else { Stream::Stdout };
                self.emit_printf(stream, "\n", &[], fb, module);
                Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Void }))
            }
            // The same, to a stream the caller names.
            "fprint_newline" => {
                let [out] = args else {
                    return Err(CompileError::emit("`fprint_newline` takes one stream"));
                };
                let stream = self.emit_stream_argument(name, out, fb, registry, module)?;
                self.emit_printf(stream, "\n", &[], fb, module);
                Ok(Some(FnValue { reg: String::new(), ty: LlvmType::Void }))
            }
            "g0int2float_double" | "int2float" | "i2d" => {
                let [n] = args else { return Err(CompileError::emit("`int2double` takes one int")) };
                let v = self.emit_expr(n, fb, registry, module)?;
                self.require(v.ty, LlvmType::I64, "`int2double`")?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = sitofp i64 {} to double", v.reg));
                Ok(Some(FnValue { reg, ty: LlvmType::F64 }))
            }
            "d2i" => {
                let [x] = args else { return Err(CompileError::emit("`double2int` takes one double")) };
                let v = self.emit_expr(x, fb, registry, module)?;
                self.require(v.ty, LlvmType::F64, "`double2int`")?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = fptosi double {} to i64", v.reg));
                Ok(Some(FnValue { reg, ty: LlvmType::I64 }))
            }
            "char2int" | "char2int0" | "c2i" => {
                let [c] = args else { return Err(CompileError::emit("`char2int` takes one character")) };
                let v = self.emit_expr(c, fb, registry, module)?;
                self.require(v.ty, LlvmType::I8, "`char2int`")?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = sext i8 {} to i64", v.reg));
                Ok(Some(FnValue { reg, ty: LlvmType::I64 }))
            }
            "int2char" | "int2char0" | "i2c" => {
                let [n] = args else { return Err(CompileError::emit("`int2char` takes one int")) };
                let v = self.emit_expr(n, fb, registry, module)?;
                self.require(v.ty, LlvmType::I64, "`int2char`")?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = trunc i64 {} to i8", v.reg));
                Ok(Some(FnValue { reg, ty: LlvmType::I8 }))
            }
            "g0string2int" | "g0string2int_int" | "g1string2int" | "string2int" | "atoi" => {
                Ok(Some(self.emit_libc_shim(name, "atoi", "declare i64 @atoi(ptr)", LlvmType::I8Ptr, LlvmType::I64, args, fb, registry, module)?))
            }
            "string_length" | "string0_length" | "string1_length" | "strlen" => {
                Ok(Some(self.emit_libc_shim(name, "strlen", "declare i64 @strlen(ptr)", LlvmType::I8Ptr, LlvmType::I64, args, fb, registry, module)?))
            }
            _ => Ok(None),
        }
    }

    /// Widen a number to the numeric type asked for.
    fn emit_numeric_cast(&self, v: FnValue, want: LlvmType, fb: &mut FnBuilder) -> Result<FnValue, CompileError> {
        if v.ty == want {
            return Ok(v);
        }
        match (v.ty, want) {
            (LlvmType::I64, LlvmType::F64) => {
                // A literal converts at compile time: `gnumber_int<double>(1)`
                // should read as the constant it is, not as a conversion
                // the reader has to perform in their head.
                if let Ok(n) = v.reg.parse::<i64>() {
                    return Ok(FnValue { reg: format!("{:.1}", n as f64), ty: LlvmType::F64 });
                }
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = sitofp i64 {} to double", v.reg));
                Ok(FnValue { reg, ty: LlvmType::F64 })
            }
            // A character *is* a small integer in ATS: `c - '0'` is
            // arithmetic, not a conversion the programmer writes.
            (LlvmType::I8, LlvmType::I64) => {
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = sext i8 {} to i64", v.reg));
                Ok(FnValue { reg, ty: LlvmType::I64 })
            }
            (LlvmType::I64, LlvmType::I8) => {
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = trunc i64 {} to i8", v.reg));
                Ok(FnValue { reg, ty: LlvmType::I8 })
            }
            (LlvmType::I8, LlvmType::F64) => {
                let widened = self.emit_numeric_cast(v, LlvmType::I64, fb)?;
                self.emit_numeric_cast(widened, LlvmType::F64, fb)
            }
            _ => Err(CompileError::emit(format!(
                "cannot make a {} out of a {}",
                llvm_ty_str(want),
                llvm_ty_str(v.ty)
            ))),
        }
    }

    /// Apply an operator to two numbers of different types by widening the
    /// narrower one.
    ///
    /// This is what the generic arithmetic shims do, and it happens only
    /// where the program asked for it — through an `overload`, or by
    /// naming the shim outright.  Ordinary arithmetic still refuses to mix
    /// the two, which is what ATS itself does.
    fn emit_promoted(&self, op: BinOp, lv: FnValue, rv: FnValue, fb: &mut FnBuilder) -> Result<FnValue, CompileError> {
        let want = if lv.ty == LlvmType::F64 || rv.ty == LlvmType::F64 { LlvmType::F64 } else { LlvmType::I64 };
        let lv = self.emit_numeric_cast(lv, want, fb)?;
        let rv = self.emit_numeric_cast(rv, want, fb)?;
        self.emit_binop_values(op, lv, rv, fb)
    }

    /// One-argument shims that are a call to a libc function.
    #[allow(clippy::too_many_arguments)]
    fn emit_libc_shim(&self, ats_name: &str, c_name: &str, decl: &'static str, want: LlvmType, ret: LlvmType, args: &[Expr], fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        let [arg] = args else {
            return Err(CompileError::emit(format!("`{ats_name}` takes exactly one argument")));
        };
        let v = self.emit_expr(arg, fb, registry, module)?;
        if v.ty != want {
            return Err(CompileError::emit(format!(
                "`{ats_name}` expects a {} argument, got {}",
                llvm_ty_str(want),
                llvm_ty_str(v.ty)
            )));
        }
        module.externs.insert(decl);
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = call {} @{c_name}({} {})", llvm_ty_str(ret), llvm_ty_str(want), v.reg));
        Ok(FnValue { reg, ty: ret })
    }

    /// Reserve `bytes` from the arena, returning the pointer.
    ///
    /// Overflow is checked rather than assumed: running out of arena ends
    /// the program with a message, which is a far better failure than
    /// quietly writing past the buffer.
    fn emit_alloc(&self, bytes: usize, fb: &mut FnBuilder, module: &mut ModuleBuilder) -> String {
        self.emit_alloc_bytes(&bytes.to_string(), fb, module)
    }

    /// As `emit_alloc`, but for a size only known at run time.
    fn emit_alloc_bytes(&self, bytes: &str, fb: &mut FnBuilder, module: &mut ModuleBuilder) -> String {
        module.needs_heap = true;
        module.externs.insert("declare ptr @malloc(i64)");
        module.externs.insert("declare void @free(ptr)");
        let ptr = fb.fresh_temp();
        fb.line(format!("{ptr} = call ptr @.ats_alloc(i64 {bytes})"));
        ptr
    }

    /// Build a datatype value: one allocation, the tag, then the fields.
    fn emit_ctor(&self, name: &str, info: &CtorInfo, args: &[Expr], fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        if args.len() != info.fields.len() {
            return Err(CompileError::emit(format!(
                "constructor `{name}` takes {} field(s), got {}",
                info.fields.len(),
                args.len()
            )));
        }
        // Every field is one machine word: an int, a bool widened to a
        // word, or a pointer.  A uniform width keeps the offset of field
        // `i` the same for every constructor, which is what lets a
        // pattern read a field without a per-constructor struct type.
        let mut values = Vec::new();
        for (arg, want) in args.iter().zip(&info.fields) {
            // `list_vt_cons(m, _)` — a field left to be filled in.  The
            // recursion writes it through the cell the match hands back,
            // and ATS's linear types are what promise nothing reads it
            // first; all that is owed here is a well-defined slot rather
            // than whatever the arena last held.
            if matches!(arg, Expr::Wildcard) {
                values.push(FnValue { reg: zero_literal(*want).to_string(), ty: *want });
                continue;
            }
            // The field's declared type is what a nested constructor in
            // this position needs in order to know which instance it
            // builds — `Cons(x, Nil())` settles the `Nil` from here.
            let v = self.emit_expr_expecting(arg, Some(*want), fb, registry, module)?;
            if v.ty != *want {
                return Err(CompileError::emit(format!(
                    "field of `{name}` has type {}, expected {}",
                    llvm_ty_str(v.ty),
                    llvm_ty_str(*want)
                )));
            }
            values.push(v);
        }
        let ptr = self.emit_alloc(WORD * (1 + info.width), fb, module);
        fb.line(format!("store i64 {}, ptr {ptr}", info.tag));
        for (i, v) in values.iter().enumerate() {
            let addr = self.emit_field_address(&ptr, i, fb);
            fb.line(format!("store {} {}, ptr {addr}", llvm_ty_str(v.ty), v.reg));
        }
        Ok(FnValue { reg: ptr, ty: LlvmType::Data(info.datatype) })
    }

    /// The address of field `i` of a datatype value: past the tag, then
    /// `i` words in.
    fn emit_field_address(&self, base: &str, i: usize, fb: &mut FnBuilder) -> String {
        self.emit_slot_address(base, i + 1, fb)
    }

    /// The address of word `i` of a record.  A tuple has no tag, so its
    /// first component is word zero.
    fn emit_slot_address(&self, base: &str, i: usize, fb: &mut FnBuilder) -> String {
        if i == 0 {
            return base.to_string();
        }
        let addr = fb.fresh_temp();
        fb.line(format!("{addr} = getelementptr i8, ptr {base}, i64 {}", WORD * i));
        addr
    }

    /// `case e of | p => e | ...`
    ///
    /// The arms are tried in order, each in its own block, which is the
    /// shape the source already has.  A decision tree would test each tag
    /// once instead of once per arm; this compiler leaves that to LLVM,
    /// which turns the chain of equality tests back into a switch.
    fn emit_case(&self, scrutinee: &Expr, arms: &[(Pattern, Expr)], expected: Option<LlvmType>, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        if arms.is_empty() {
            return Err(CompileError::emit("a `case` needs at least one arm"));
        }
        // Taking apart a value the function holds *by reference* gives
        // references to its parts: `val Box (_, rest) = b` on a `&box`
        // makes `rest` the cell of that field, so writing to it writes
        // into `b`.  No `@` is written — in ATS it is the linearity of
        // the value that says so, and here it is that the scrutinee is
        // a cell rather than a value.
        let in_place = matches!(scrutinee, Expr::Var(n) if fb.cells.contains_key(n));
        let value = self.emit_expr(scrutinee, fb, registry, module)?;
        let id = fb.fresh_block_id();
        let merge = format!("case.done.{id}");
        let mut results: Vec<(FnValue, String)> = Vec::new();

        for (i, (pattern, body)) in arms.iter().enumerate() {
            let body_label = format!("case.arm.{id}.{i}");
            let next_label = format!("case.next.{id}.{i}");
            let saved_env = fb.env.clone();
            let saved_cells = fb.cells.clone();

            // The matcher lands control in a block where the pattern has
            // matched, so the body follows it directly.
            let irrefutable = is_irrefutable(pattern);
            self.emit_pattern_match_at(pattern, &value, &next_label, in_place, fb, registry)?;
            fb.line(format!("br label %{body_label}"));
            fb.label(&body_label);
            let settled = expected.or_else(|| results.first().map(|(v, _): &(FnValue, String)| v.ty));
            let r = self.emit_expr_expecting(body, settled, fb, registry, module)?;
            let pred = fb.cur_block.clone();
            if r.ty != LlvmType::Never {
                fb.line(format!("br label %{merge}"));
                results.push((r, pred));
            }
            fb.env = saved_env;
            fb.cells = saved_cells;

            if irrefutable {
                // The remaining arms are unreachable; stop here.
                break;
            }
            fb.label(&next_label);
            if i + 1 == arms.len() {
                // Every arm refused the value.  ATS would have proved this
                // impossible; without that proof, say so and stop.
                self.emit_printf(Stream::Stderr, "exit(ATS): no matching case\n", &[], fb, module);
                fb.line("call void @exit(i32 2)");
                fb.line("unreachable");
            }
        }

        fb.label(&merge);
        let Some(((first, _), rest)) = results.split_first() else {
            fb.line("unreachable");
            return Ok(FnValue { reg: String::new(), ty: LlvmType::Never });
        };
        for (other, _) in rest {
            if other.ty != first.ty {
                return Err(CompileError::emit(format!(
                    "case arms have different types ({} vs {})",
                    llvm_ty_str(first.ty),
                    llvm_ty_str(other.ty)
                )));
            }
        }
        let ty = first.ty;
        if ty == LlvmType::Void {
            return Ok(FnValue { reg: String::new(), ty });
        }
        let incoming: Vec<String> = results.iter().map(|(v, p)| format!("[ {}, %{p} ]", v.reg)).collect();
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = phi {} {}", llvm_ty_str(ty), incoming.join(", ")));
        Ok(FnValue { reg, ty })
    }

    /// Match one pattern against a value, jumping to `on_fail` if it does
    /// not fit, and binding whatever it names if it does.
    ///
    /// Testing and binding are done together, and both are done *in
    /// order*, because a nested pattern is only safe to look at once the
    /// pattern around it has matched: the tail of a list is a pointer
    /// only when the value really was a `Cons`, and following whatever a
    /// `Nil` left in that slot would be a wild read.  Emitting each test
    /// with its own early exit is what enforces that.
    ///
    /// On return, control is in a block where the whole pattern has
    /// matched.
    fn emit_pattern_match(&self, pattern: &Pattern, value: &FnValue, on_fail: &str, fb: &mut FnBuilder, registry: &Registry) -> Result<(), CompileError> {
        self.emit_pattern_match_at(pattern, value, on_fail, false, fb, registry)
    }

    /// As `emit_pattern_match`, but `in_place` says whether the names a
    /// constructor pattern binds are the value's own cells.
    ///
    /// An ordinary match *loads* each field, so the name is a copy and
    /// assigning to it would write nowhere.  A `@` match binds the
    /// address instead, and then `xs := ys` writes into the value that
    /// was matched — which is how ATS builds a list by filling in its
    /// own tail.
    fn emit_pattern_match_at(&self, pattern: &Pattern, value: &FnValue, on_fail: &str, in_place: bool, fb: &mut FnBuilder, registry: &Registry) -> Result<(), CompileError> {
        match pattern {
            Pattern::InPlace(inner) => {
                self.emit_pattern_match_at(inner, value, on_fail, true, fb, registry)
            }
            Pattern::Wildcard => Ok(()),
            Pattern::Var(name) => {
                fb.cells.remove(name);
                fb.env.insert(name.clone(), value.clone());
                Ok(())
            }
            Pattern::Char(b) => {
                self.require(value.ty, LlvmType::I8, "a character pattern")?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = icmp eq i8 {}, {b}", value.reg));
                self.emit_guard(&reg, on_fail, fb);
                Ok(())
            }
            Pattern::Int(n) => {
                self.require(value.ty, LlvmType::I64, "an integer pattern")?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = icmp eq i64 {}, {n}", value.reg));
                self.emit_guard(&reg, on_fail, fb);
                Ok(())
            }
            Pattern::Bool(b) => {
                self.require(value.ty, LlvmType::I1, "a boolean pattern")?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = icmp eq i1 {}, {b}", value.reg));
                self.emit_guard(&reg, on_fail, fb);
                Ok(())
            }
            Pattern::Str(_) => Err(CompileError::emit("string patterns are not supported yet")),
            Pattern::Tuple(items) if items.is_empty() => Ok(()),
            Pattern::Tuple(items) => {
                let LlvmType::Tuple(index) = value.ty else {
                    return Err(CompileError::emit(format!(
                        "a tuple pattern needs a tuple, but the value being matched has type {}",
                        llvm_ty_str(value.ty)
                    )));
                };
                let parts = registry.tuple_parts(index);
                if parts.len() != items.len() {
                    return Err(CompileError::emit(format!(
                        "this tuple has width {}, but the pattern names {}",
                        parts.len(),
                        items.len()
                    )));
                }
                for (i, (sub, ty)) in items.iter().zip(parts).enumerate() {
                    let addr = self.emit_slot_address(&value.reg, i, fb);
                    let reg = fb.fresh_temp();
                    fb.line(format!("{reg} = load {}, ptr {addr}", llvm_ty_str(ty)));
                    self.emit_pattern_match_at(sub, &FnValue { reg, ty }, on_fail, in_place, fb, registry)?;
                }
                Ok(())
            }
            Pattern::Ctor(name, fields) => {
                if !registry.ctors.contains_key(name) {
                    return Err(CompileError::emit(format!("unknown constructor `{name}`")));
                }
                let LlvmType::Data(index) = value.ty else {
                    return Err(CompileError::emit(format!(
                        "`{name}` is a constructor, but the value being matched has type {}",
                        llvm_ty_str(value.ty)
                    )));
                };
                // In a pattern the scrutinee already fixes the datatype,
                // so there is never any ambiguity to resolve.
                let Some(info) = registry.ctors[name].iter().find(|c| c.datatype == index).cloned() else {
                    return Err(CompileError::emit(format!(
                        "`{name}` does not build a `{}`, which is what is being matched",
                        registry.datatypes[index]
                    )));
                };
                if fields.len() != info.fields.len() {
                    return Err(CompileError::emit(format!(
                        "pattern `{name}` names {} field(s), but it has {}",
                        fields.len(),
                        info.fields.len()
                    )));
                }
                let tag = fb.fresh_temp();
                fb.line(format!("{tag} = load i64, ptr {}", value.reg));
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = icmp eq i64 {tag}, {}", info.tag));
                self.emit_guard(&reg, on_fail, fb);
                // Past the guard the value is known to be this
                // constructor, so its fields may be read.
                for (i, (sub, ty)) in fields.iter().zip(info.fields.iter().copied()).enumerate() {
                    if matches!(sub, Pattern::Wildcard) {
                        continue;
                    }
                    let addr = self.emit_field_address(&value.reg, i, fb);
                    // Under `@`, a field named by a plain variable *is*
                    // that field: the name becomes a cell at its address
                    // rather than a copy of what it held.  A field the
                    // pattern looks further into is still loaded — there
                    // is nothing to write to inside it.
                    if in_place {
                        if let Pattern::Var(n) = sub {
                            fb.env.remove(n);
                            fb.cells.insert(n.clone(), Cell { ptr: addr, ty });
                            continue;
                        }
                    }
                    let reg = fb.fresh_temp();
                    fb.line(format!("{reg} = load {}, ptr {addr}", llvm_ty_str(ty)));
                    self.emit_pattern_match_at(sub, &FnValue { reg, ty }, on_fail, in_place, fb, registry)?;
                }
                Ok(())
            }
        }
    }

    /// Continue when `cond` holds, and leave for `on_fail` when it does
    /// not.  The continuation gets a block of its own, which is what
    /// keeps the tests after it from running too early.
    fn emit_guard(&self, cond: &str, on_fail: &str, fb: &mut FnBuilder) {
        let id = fb.fresh_block_id();
        let ok = format!("pat.ok.{id}");
        fb.line(format!("br i1 {cond}, label %{ok}, label %{on_fail}"));
        fb.label(&ok);
    }

    /// Insist that a value has the type a construct requires.
    fn require(&self, got: LlvmType, want: LlvmType, what: &str) -> Result<(), CompileError> {
        if got == want {
            Ok(())
        } else {
            Err(CompileError::emit(format!(
                "{what} needs a {} value, got {}",
                llvm_ty_str(want),
                llvm_ty_str(got)
            )))
        }
    }

    /// `lam (x: t): u => e` — build a closure.
    ///
    /// The body becomes a top-level function whose first parameter is the
    /// environment, and the values it reads from the enclosing scope are
    /// copied into a record alongside a pointer to that function.  Lambda
    /// *lifting* handled named nested functions by adding parameters; a
    /// lambda cannot do that, because it may outlive the scope it was
    /// written in and its callers do not know what it captured.
    fn emit_lambda(&self, params: &[Param], ret: Option<&Ty>, body: &Expr, expected: Option<LlvmType>, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        // `lam x => x > 0` says nothing about `x`.  Where the lambda is
        // *going* does, and nothing else can: the body cannot be read
        // for it without a type inference this compiler has no room for.
        // So an unannotated parameter takes the type the context asks
        // for, and only a lambda with nowhere to go is an error.
        let wanted = match expected {
            Some(LlvmType::Closure(i)) => Some(registry.closure_sig(i)),
            _ => None,
        };
        let wanted = wanted.filter(|s| s.params.len() == params.len());
        let param_tys = params
            .iter()
            .enumerate()
            .map(|(i, p)| match (&p.ty, &wanted) {
                (Ty::Name(n), Some(sig)) if n == "_" => Ok(sig.params[i]),
                _ => llvm_type_in(&p.ty, registry),
            })
            .collect::<Result<Vec<_>, _>>()?;

        // What does the body read that is neither a parameter nor global?
        let mut bound: std::collections::HashSet<String> =
            params.iter().map(|p| p.name.clone()).collect();
        let mut free = std::collections::BTreeSet::new();
        crate::lift::free_variables(body, &mut bound, &mut free);
        let mut captures = Vec::new();
        for name in free {
            if let Some(v) = fb.env.get(&name) {
                captures.push((name, v.clone()));
            } else if fb.cells.contains_key(&name) {
                // A `var` is storage; a closure captures the *value* it
                // held when the closure was made.
                let cell = fb.cells[&name].clone();
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = load {}, ptr {}", llvm_ty_str(cell.ty), cell.ptr));
                captures.push((name, FnValue { reg, ty: cell.ty }));
            }
        }

        // Emit the body as its own function, in its own builder.
        let id = module.next_lambda();
        let fname = format!("lam.{id}");
        let mut inner = FnBuilder::new();
        for (p, ty) in params.iter().zip(&param_tys) {
            inner.env.insert(p.name.clone(), FnValue { reg: format!("%{}", sanitize(&p.name)), ty: *ty });
        }
        for (i, (name, v)) in captures.iter().enumerate() {
            let addr = self.emit_slot_address("%env", i + 1, &mut inner);
            let reg = inner.fresh_temp();
            inner.line(format!("{reg} = load {}, ptr {addr}", llvm_ty_str(v.ty)));
            inner.env.insert(name.clone(), FnValue { reg, ty: v.ty });
        }
        let value = self.emit_expr(body, &mut inner, registry, module)?;
        let ret_ty = match ret {
            Some(t) => llvm_type_in(t, registry)?,
            None => value.ty,
        };
        if value.ty != ret_ty && value.ty != LlvmType::Never {
            return Err(CompileError::emit(format!(
                "this lambda returns {}, but says it returns {}",
                llvm_ty_str(value.ty),
                llvm_ty_str(ret_ty)
            )));
        }

        let mut decl = format!("define {} @{fname}(ptr %env", llvm_ty_str(ret_ty));
        for (p, ty) in params.iter().zip(&param_tys) {
            decl.push_str(&format!(", {} %{}", llvm_ty_str(*ty), sanitize(&p.name)));
        }
        decl.push_str(") {\nentry:");
        for line in inner.allocas.iter().chain(&inner.lines) {
            push_line(&mut decl, line);
        }
        decl.push_str(&ret_instruction(ret_ty, &value));
        module.lines.push(decl);

        // The record: the code, then everything it captured.
        let ptr = self.emit_alloc(WORD * (1 + captures.len()), fb, module);
        fb.line(format!("store ptr @{fname}, ptr {ptr}"));
        for (i, (_, v)) in captures.iter().enumerate() {
            let addr = self.emit_slot_address(&ptr, i + 1, fb);
            fb.line(format!("store {} {}, ptr {addr}", llvm_ty_str(v.ty), v.reg));
        }
        let index = registry.intern_closure(FnSig { params: param_tys, ret: ret_ty });
        Ok(FnValue { reg: ptr, ty: LlvmType::Closure(index) })
    }

    /// Call a closure: load the code out of the record and jump through
    /// it, handing the record itself back as the environment.
    fn emit_closure_call(&self, callee: FnValue, args: &[Expr], fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        let LlvmType::Closure(index) = callee.ty else {
            return Err(CompileError::emit(format!(
                "cannot call a value of type {}",
                llvm_ty_str(callee.ty)
            )));
        };
        let sig = registry.closure_sig(index);
        if args.len() != sig.params.len() {
            return Err(CompileError::emit(format!(
                "this function takes {} argument(s), got {}",
                sig.params.len(),
                args.len()
            )));
        }
        let mut operands = vec![format!("ptr {}", callee.reg)];
        for (arg, want) in args.iter().zip(&sig.params) {
            let v = self.emit_expr_expecting(arg, Some(*want), fb, registry, module)?;
            if v.ty != *want {
                return Err(CompileError::emit(format!(
                    "argument has type {}, expected {}",
                    llvm_ty_str(v.ty),
                    llvm_ty_str(*want)
                )));
            }
            operands.push(format!("{} {}", llvm_ty_str(v.ty), v.reg));
        }
        let code = fb.fresh_temp();
        fb.line(format!("{code} = load ptr, ptr {}", callee.reg));
        let types: Vec<&str> = std::iter::once("ptr")
            .chain(sig.params.iter().map(|p| llvm_ty_str(*p)))
            .collect();
        if sig.ret == LlvmType::Void {
            fb.line(format!("call void {code}({})", operands.join(", ")));
            return Ok(FnValue { reg: String::new(), ty: LlvmType::Void });
        }
        let reg = fb.fresh_temp();
        fb.line(format!(
            "{reg} = call {} {code}({})",
            llvm_ty_str(sig.ret),
            operands.join(", ")
        ));
        let _ = types;
        Ok(FnValue { reg, ty: sig.ret })
    }

    /// `xs[i]` — load the element at an index.
    ///
    /// Only `argv` is indexable so far.  It is an array of pointers, so
    /// the address of element `i` is one `getelementptr` and the element
    /// itself is one load; the result is a `string`.
    fn emit_index(&self, base: &Expr, index: &Expr, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        let b = self.emit_expr(base, fb, registry, module)?;
        if matches!(b.ty, LlvmType::Array(_)) {
            return self.emit_array_index(&b, index, fb, registry, module);
        }
        if b.ty != LlvmType::Argv {
            return Err(CompileError::emit(format!(
                "cannot index a value of type {}; only arrays and `argv` can be indexed",
                llvm_ty_str(b.ty)
            )));
        }
        let i = self.emit_expr(index, fb, registry, module)?;
        if i.ty != LlvmType::I64 {
            return Err(CompileError::emit("an index must be an int"));
        }
        let addr = fb.fresh_temp();
        fb.line(format!("{addr} = getelementptr ptr, ptr {}, i64 {}", b.reg, i.reg));
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = load ptr, ptr {addr}"));
        Ok(FnValue { reg, ty: LlvmType::I8Ptr })
    }

    /// `c >= lo && c <= hi`, possibly several ranges joined by `or`.
    fn emit_char_class(&self, class: &str, c: &str, fb: &mut FnBuilder) -> String {
        let ranges: &[(char, char)] = match class {
            "isdigit" => &[('0', '9')],
            "isalpha" => &[('a', 'z'), ('A', 'Z')],
            "isalnum" => &[('a', 'z'), ('A', 'Z'), ('0', '9')],
            "isupper" => &[('A', 'Z')],
            "islower" => &[('a', 'z')],
            "isxdigit" => &[('0', '9'), ('a', 'f'), ('A', 'F')],
            "isspace" => &[(' ', ' '), ('\t', '\r')],
            _ => &[('!', '/'), (':', '@'), ('[', '`'), ('{', '~')],
        };
        let mut acc: Option<String> = None;
        for (lo, hi) in ranges {
            let ge = fb.fresh_temp();
            fb.line(format!("{ge} = icmp sge i64 {c}, {}", *lo as u8));
            let le = fb.fresh_temp();
            fb.line(format!("{le} = icmp sle i64 {c}, {}", *hi as u8));
            let both = fb.fresh_temp();
            fb.line(format!("{both} = and i1 {ge}, {le}"));
            acc = Some(match acc {
                None => both,
                Some(prev) => {
                    let joined = fb.fresh_temp();
                    fb.line(format!("{joined} = or i1 {prev}, {both}"));
                    joined
                }
            });
        }
        acc.expect("at least one range")
    }

    /// The hole a library routine needs, or a diagnostic naming it.
    fn require_hole(&self, name: &str, registry: &Registry) -> Result<ats2_domain::ast::ImplementDef, CompileError> {
        registry.holes.get(name).cloned().ok_or_else(|| {
            CompileError::emit(format!(
                "this needs `implement {name} (...)` to say what to do with each element"
            ))
        })
    }

    /// Emit a template hole's body here, with its parameters bound.
    ///
    /// The last parameter is the *environment*, which ATS passes by
    /// reference: the hole assigns to it and the caller sees the result.
    /// Binding the hole's name for it directly to the caller's cell is
    /// what makes that true, and it is only possible because the body is
    /// inlined rather than called.
    fn inline_hole(
        &self,
        hole: &ats2_domain::ast::ImplementDef,
        bound: &[FnValue],
        env_arg: Option<&Expr>,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
        let saved_env = fb.env.clone();
        let saved_cells = fb.cells.clone();
        for (p, v) in hole.params.iter().zip(bound) {
            fb.env.insert(p.name.clone(), v.clone());
            fb.cells.remove(&p.name);
        }
        if let (Some(p), Some(Expr::Var(outer))) = (hole.params.get(bound.len()), env_arg) {
            match fb.cells.get(outer).cloned() {
                // The caller's `var` — alias the hole's name to the same
                // storage, so a write inside is a write outside.
                Some(cell) => {
                    fb.cells.insert(p.name.clone(), cell);
                    fb.env.remove(&p.name);
                }
                None => {
                    if let Some(v) = fb.env.get(outer).cloned() {
                        fb.env.insert(p.name.clone(), v);
                        fb.cells.remove(&p.name);
                    }
                }
            }
        }
        let result = self.emit_expr(&hole.body, fb, registry, module);
        fb.env = saved_env;
        fb.cells = saved_cells;
        result
    }

    /// Reserve `n` words in the arena at run time.
    ///
    /// The static form takes a constant because most allocations know
    /// their size; an array's length is a static index, and static
    /// indices are erased, so this one has to compute it.
    fn emit_alloc_dynamic(&self, count: &str, fb: &mut FnBuilder, module: &mut ModuleBuilder) -> String {
        let bytes = fb.fresh_temp();
        fb.line(format!("{bytes} = mul i64 {count}, {WORD}"));
        self.emit_alloc_bytes(&bytes, fb, module)
    }

    /// Write one value into every cell of a fresh array.
    fn emit_fill(&self, ptr: &str, count: &str, value: &FnValue, fb: &mut FnBuilder) {
        let id = fb.fresh_block_id();
        let (head, body, done) =
            (format!("fill.head.{id}"), format!("fill.body.{id}"), format!("fill.done.{id}"));
        let cell = fb.alloca(&format!("fill.i.{id}"), LlvmType::I64);
        fb.line(format!("store i64 0, ptr {cell}"));
        fb.line(format!("br label %{head}"));
        fb.label(&head);
        let i = fb.fresh_temp();
        fb.line(format!("{i} = load i64, ptr {cell}"));
        let more = fb.fresh_temp();
        fb.line(format!("{more} = icmp slt i64 {i}, {count}"));
        fb.line(format!("br i1 {more}, label %{body}, label %{done}"));
        fb.label(&body);
        let off = fb.fresh_temp();
        fb.line(format!("{off} = mul i64 {i}, {WORD}"));
        let addr = fb.fresh_temp();
        fb.line(format!("{addr} = getelementptr i8, ptr {ptr}, i64 {off}"));
        fb.line(format!("store {} {}, ptr {addr}", llvm_ty_str(value.ty), value.reg));
        let next = fb.fresh_temp();
        fb.line(format!("{next} = add i64 {i}, 1"));
        fb.line(format!("store i64 {next}, ptr {cell}"));
        fb.line(format!("br label %{head}"));
        fb.label(&done);
    }

    /// Fill an array with `lo, lo+1, ...`.
    fn emit_fill_intrange(&self, ptr: &str, lo: &str, count: &str, fb: &mut FnBuilder) {
        let id = fb.fresh_block_id();
        let (head, body, done) =
            (format!("range.head.{id}"), format!("range.body.{id}"), format!("range.done.{id}"));
        let cell = fb.alloca(&format!("range.i.{id}"), LlvmType::I64);
        fb.line(format!("store i64 0, ptr {cell}"));
        fb.line(format!("br label %{head}"));
        fb.label(&head);
        let i = fb.fresh_temp();
        fb.line(format!("{i} = load i64, ptr {cell}"));
        let more = fb.fresh_temp();
        fb.line(format!("{more} = icmp slt i64 {i}, {count}"));
        fb.line(format!("br i1 {more}, label %{body}, label %{done}"));
        fb.label(&body);
        let off = fb.fresh_temp();
        fb.line(format!("{off} = mul i64 {i}, {WORD}"));
        let addr = fb.fresh_temp();
        fb.line(format!("{addr} = getelementptr i8, ptr {ptr}, i64 {off}"));
        let v = fb.fresh_temp();
        fb.line(format!("{v} = add i64 {lo}, {i}"));
        fb.line(format!("store i64 {v}, ptr {addr}"));
        let next = fb.fresh_temp();
        fb.line(format!("{next} = add i64 {i}, 1"));
        fb.line(format!("store i64 {next}, ptr {cell}"));
        fb.line(format!("br label %{head}"));
        fb.label(&done);
    }

    /// `xs.0` — one component of a tuple.
    ///
    /// A tuple is a run of word-sized slots, so the address is the slot
    /// and the type is the slot's, which is why this cannot be folded
    /// into `emit_index`: sibling slots need not agree.
    fn emit_proj(&self, base: &Expr, slot: usize, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        let b = self.emit_expr(base, fb, registry, module)?;
        let LlvmType::Tuple(index) = b.ty else {
            // `(pf | v).1` — a proof pair.  The proof half was erased
            // before emission, so the pair collapsed to its value and
            // `.1` now names the whole thing.  Only slot 1 gets this
            // reading: `.0` was the proof, and asking for a proof at run
            // time is a mistake worth reporting.
            if slot == 1 {
                return Ok(b);
            }
            return Err(CompileError::emit(format!(
                "`.{slot}` projects out of a tuple, but this value has type {}",
                llvm_ty_str(b.ty)
            )));
        };
        let parts = registry.tuple_parts(index);
        let Some(&ty) = parts.get(slot) else {
            return Err(CompileError::emit(format!(
                "this tuple has width {}, so it has no component `.{slot}`",
                parts.len()
            )));
        };
        let addr = self.emit_slot_address(&b.reg, slot, fb);
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = load {}, ptr {addr}", llvm_ty_str(ty)));
        Ok(FnValue { reg, ty })
    }

    /// `!p` — read through a pointer.
    ///
    /// What that costs depends on what the pointer leads to.  An array
    /// pointer and the array it names are the same machine word, so
    /// dereferencing one is free; a `ref` cell holds its value in its
    /// single slot, so reading one is a load.
    fn emit_deref(&self, inner: &Expr, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        let v = self.emit_expr(inner, fb, registry, module)?;
        match v.ty {
            // `!s` on a stream *forces* it.  Reading through a pointer is
            // what the syntax says and what this does — the answer is
            // one word away — but the first read has to produce the
            // answer before it can be read.
            LlvmType::Lazy(index) => self.emit_force(v, index, fb, registry),
            // A raw pointer leads to bytes with no element type, so
            // there is nothing to load: `!p` *views* the memory as
            // whatever the context says it is, exactly as it does for an
            // array pointer.
            LlvmType::Array(_) | LlvmType::I8Ptr => Ok(v),
            LlvmType::Tuple(i) if registry.tuple_parts(i).len() == 1 => {
                let ty = registry.tuple_parts(i)[0];
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = load {}, ptr {}", llvm_ty_str(ty), v.reg));
                Ok(FnValue { reg, ty })
            }
            other => Err(CompileError::emit(format!(
                "`!` reads through a pointer, but this value has type {}",
                llvm_ty_str(other)
            ))),
        }
    }

    /// What a list of this datatype holds, if it is a list at all.
    ///
    /// Every instance of the prelude's `list0` declares the same two
    /// constructors; what separates one instance from another is the
    /// type of the element, which is exactly what printing one needs.
    fn list_element(&self, datatype: usize, registry: &Registry) -> Option<LlvmType> {
        let cons = registry
            .ctors
            .get("list0_cons")?
            .iter()
            .find(|c| c.datatype == datatype)?;
        cons.fields.first().copied()
    }

    /// Print a list as ATS does: its elements, separated by `", "`.
    ///
    /// A loop rather than a format string, because how many elements
    /// there are is not known until the list is walked.  The cursor and
    /// the "is this the first one" flag live in cells rather than in
    /// phis: the loop body may itself branch — printing an element can
    /// be a walk over another list — and a phi would then name the wrong
    /// predecessor.
    fn emit_list_print(&self, stream: &Stream, list: &FnValue, datatype: usize, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<(), CompileError> {
        let element = self
            .list_element(datatype, registry)
            .ok_or_else(|| CompileError::emit("internal: not a list"))?;
        let nil = registry
            .ctors
            .get("list0_nil")
            .and_then(|cs| cs.iter().find(|c| c.datatype == datatype))
            .ok_or_else(|| CompileError::emit("internal: a list with no nil"))?
            .tag;

        let id = fb.fresh_block_id();
        let (head, body, sep, item, done) = (
            format!("print.list.head.{id}"),
            format!("print.list.body.{id}"),
            format!("print.list.sep.{id}"),
            format!("print.list.item.{id}"),
            format!("print.list.done.{id}"),
        );
        let cursor = fb.alloca(&format!("print.cursor.{id}"), LlvmType::I8Ptr);
        let first = fb.alloca(&format!("print.first.{id}"), LlvmType::I1);
        fb.line(format!("store ptr {}, ptr {cursor}", list.reg));
        fb.line(format!("store i1 true, ptr {first}"));
        fb.line(format!("br label %{head}"));

        fb.label(&head);
        let cur = fb.fresh_temp();
        let tag = fb.fresh_temp();
        let at_end = fb.fresh_temp();
        fb.line(format!("{cur} = load ptr, ptr {cursor}"));
        fb.line(format!("{tag} = load i64, ptr {cur}"));
        fb.line(format!("{at_end} = icmp eq i64 {tag}, {nil}"));
        fb.line(format!("br i1 {at_end}, label %{done}, label %{body}"));

        fb.label(&body);
        let is_first = fb.fresh_temp();
        fb.line(format!("{is_first} = load i1, ptr {first}"));
        fb.line(format!("br i1 {is_first}, label %{item}, label %{sep}"));

        fb.label(&sep);
        self.emit_printf(stream.clone(), ", ", &[], fb, module);
        fb.line(format!("br label %{item}"));

        fb.label(&item);
        fb.line(format!("store i1 false, ptr {first}"));
        let cur2 = fb.fresh_temp();
        fb.line(format!("{cur2} = load ptr, ptr {cursor}"));
        let addr = self.emit_field_address(&cur2, 0, fb);
        let value = fb.fresh_temp();
        fb.line(format!("{value} = load {}, ptr {addr}", llvm_ty_str(element)));
        let mut fmt = String::new();
        let mut operands = Vec::new();
        self.format_one(
            stream,
            FnValue { reg: value, ty: element },
            &mut fmt,
            &mut operands,
            fb,
            registry,
            module,
        )?;
        if !fmt.is_empty() || !operands.is_empty() {
            self.emit_printf(stream.clone(), &fmt, &operands, fb, module);
        }
        let cur3 = fb.fresh_temp();
        fb.line(format!("{cur3} = load ptr, ptr {cursor}"));
        let tail_addr = self.emit_field_address(&cur3, 1, fb);
        let tail = fb.fresh_temp();
        fb.line(format!("{tail} = load ptr, ptr {tail_addr}"));
        fb.line(format!("store ptr {tail}, ptr {cursor}"));
        fb.line(format!("br label %{head}"));

        fb.label(&done);
        Ok(())
    }

    /// The slot and type of a record's field, if this value is a record
    /// that has one by that name.
    fn record_slot(&self, v: &FnValue, name: &str, registry: &Registry) -> Option<(usize, LlvmType)> {
        let LlvmType::Record(index) = v.ty else { return None };
        registry
            .record_fields(index)
            .into_iter()
            .enumerate()
            .find(|(_, (n, _))| n == name)
            .map(|(slot, (_, ty))| (slot, ty))
    }

    /// The type of an expression that can be typed without emitting it.
    ///
    /// `r.f` is a field when `r` is a record with one by that name and
    /// ATS's dot notation for `f(r)` otherwise, and the choice has to be
    /// made *before* the receiver is emitted: emitting it and then
    /// discovering it was a call's argument would evaluate it twice.
    /// A receiver is a name or a chain of fields off one in every case
    /// the language actually writes, and those need no code to type.
    fn type_without_emitting(&self, expr: &Expr, fb: &FnBuilder, registry: &Registry) -> Option<LlvmType> {
        match expr {
            Expr::Var(n) => fb
                .env
                .get(n)
                .map(|v| v.ty)
                .or_else(|| fb.cells.get(n).map(|c| c.ty))
                .or_else(|| registry.globals.get(n).copied()),
            Expr::Field(base, name) => {
                let base = self.type_without_emitting(base, fb, registry)?;
                let LlvmType::Record(index) = base else { return None };
                registry
                    .record_fields(index)
                    .into_iter()
                    .find(|(n, _)| n == name)
                    .map(|(_, ty)| ty)
            }
            _ => None,
        }
    }

    /// Whether `base.name` names a record field rather than a call.
    fn is_a_record_field(&self, base: &Expr, name: &str, fb: &FnBuilder, registry: &Registry) -> bool {
        match self.type_without_emitting(base, fb, registry) {
            Some(LlvmType::Record(index)) => {
                registry.record_fields(index).iter().any(|(n, _)| n == name)
            }
            _ => false,
        }
    }

    /// Force a suspended value, remembering the answer.
    ///
    /// The thunk slot doubles as the flag: it holds the closure until it
    /// has run and null afterwards, so "has this been forced" is one
    /// comparison and needs no extra word.  Nulling it is also what
    /// releases the closure's captures — a forced stream no longer
    /// refers to whatever it was built from, which for the sieve is the
    /// difference between a bounded and an unbounded amount of live
    /// memory.
    fn emit_force(&self, cell: FnValue, index: usize, fb: &mut FnBuilder, registry: &Registry) -> Result<FnValue, CompileError> {
        let forced = registry.lazy_forced(index);
        let id = fb.fresh_block_id();
        let (run, done) = (format!("stream.force.{id}"), format!("stream.forced.{id}"));
        let thunk = fb.fresh_temp();
        let already = fb.fresh_temp();
        fb.line(format!("{thunk} = load ptr, ptr {}", cell.reg));
        fb.line(format!("{already} = icmp eq ptr {thunk}, null"));
        fb.line(format!("br i1 {already}, label %{done}, label %{run}"));

        fb.label(&run);
        let code = fb.fresh_temp();
        fb.line(format!("{code} = load ptr, ptr {thunk}"));
        let value = fb.fresh_temp();
        fb.line(format!("{value} = call {} {code}(ptr {thunk})", llvm_ty_str(forced)));
        let answer = self.emit_slot_address(&cell.reg, 1, fb);
        fb.line(format!("store {} {value}, ptr {answer}", llvm_ty_str(forced)));
        fb.line(format!("store ptr null, ptr {}", cell.reg));
        fb.line(format!("br label %{done}"));

        fb.label(&done);
        let addr = self.emit_slot_address(&cell.reg, 1, fb);
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = load {}, ptr {addr}", llvm_ty_str(forced)));
        Ok(FnValue { reg, ty: forced })
    }

    /// `A.[i]` — one cell of an array.
    fn emit_array_index(&self, base: &FnValue, index: &Expr, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        let LlvmType::Array(elem) = base.ty else {
            return Err(CompileError::emit("internal: not an array"));
        };
        let ty = registry.array_elem(elem);
        let addr = self.emit_cell_address(base, index, fb, registry, module)?;
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = load {}, ptr {addr}", llvm_ty_str(ty)));
        Ok(FnValue { reg, ty })
    }

    /// The address of `A.[i]`.
    ///
    /// Every cell is one word wide, which is what lets the arena hand
    /// out arrays of any element type from one bump pointer.
    fn emit_cell_address(&self, base: &FnValue, index: &Expr, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<String, CompileError> {
        let i = self.emit_expr(index, fb, registry, module)?;
        self.require(i.ty, LlvmType::I64, "an array index")?;
        let byte = fb.fresh_temp();
        fb.line(format!("{byte} = mul i64 {}, {WORD}", i.reg));
        let addr = fb.fresh_temp();
        fb.line(format!("{addr} = getelementptr i8, ptr {}, i64 {byte}", base.reg));
        Ok(addr)
    }

    /// `xs.0 := e` — a store into a place the left-hand side computes.
    ///
    /// The place is evaluated for its *address*, so the value written is
    /// visible through every other name for the same aggregate.  That is
    /// what makes a tuple passed to a function mutable by it.
    fn emit_store(&self, place: &Expr, value: &Expr, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        // `A.[i] := e` — a cell of an array.
        if let Expr::Index(base, index) = place {
            let b = self.emit_expr(base, fb, registry, module)?;
            let LlvmType::Array(elem) = b.ty else {
                return Err(CompileError::emit(format!(
                    "`.[i] :=` assigns into an array, but this value has type {}",
                    llvm_ty_str(b.ty)
                )));
            };
            let want = registry.array_elem(elem);
            let addr = self.emit_cell_address(&b, index, fb, registry, module)?;
            let v = self.emit_expr_expecting(value, Some(want), fb, registry, module)?;
            if v.ty != want {
                return Err(CompileError::emit(format!(
                    "this array holds {}, but the value assigned is {}",
                    llvm_ty_str(want),
                    llvm_ty_str(v.ty)
                )));
            }
            fb.line(format!("store {} {}, ptr {addr}", llvm_ty_str(want), v.reg));
            return Ok(FnValue { reg: String::new(), ty: LlvmType::Void });
        }
        // `!r := e` — the single cell a reference names.
        if let Expr::Deref(inner) = place {
            let b = self.emit_expr(inner, fb, registry, module)?;
            let LlvmType::Tuple(i) = b.ty else {
                return Err(CompileError::emit(format!(
                    "`! :=` writes through a pointer, but this value has type {}",
                    llvm_ty_str(b.ty)
                )));
            };
            let parts = registry.tuple_parts(i);
            let [want] = parts[..] else {
                return Err(CompileError::emit("`! :=` needs a one-cell reference"));
            };
            let v = self.emit_expr_expecting(value, Some(want), fb, registry, module)?;
            let addr = self.emit_slot_address(&b.reg, 0, fb);
            fb.line(format!("store {} {}, ptr {addr}", llvm_ty_str(v.ty), v.reg));
            return Ok(FnValue { reg: String::new(), ty: LlvmType::Void });
        }
        let Expr::Proj(base, slot) = place else {
            return Err(CompileError::emit("this is not something that can be assigned to"));
        };
        let b = self.emit_expr(base, fb, registry, module)?;
        let LlvmType::Tuple(index) = b.ty else {
            return Err(CompileError::emit(format!(
                "`.{slot}` assigns into a tuple, but this value has type {}",
                llvm_ty_str(b.ty)
            )));
        };
        let parts = registry.tuple_parts(index);
        let Some(&want) = parts.get(*slot) else {
            return Err(CompileError::emit(format!(
                "this tuple has width {}, so it has no component `.{slot}`",
                parts.len()
            )));
        };
        let v = self.emit_expr_expecting(value, Some(want), fb, registry, module)?;
        if v.ty != want {
            return Err(CompileError::emit(format!(
                "component `.{slot}` holds {}, but the value assigned is {}",
                llvm_ty_str(want),
                llvm_ty_str(v.ty)
            )));
        }
        let addr = self.emit_slot_address(&b.reg, *slot, fb);
        fb.line(format!("store {} {}, ptr {addr}", llvm_ty_str(want), v.reg));
        Ok(FnValue { reg: String::new(), ty: LlvmType::Void })
    }

    /// `x := e` — a store into the cell `x` names.
    fn emit_assign(&self, name: &str, value: &Expr, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        if !fb.cells.contains_key(name) {
            if registry.globals.contains_key(name) {
                return Err(CompileError::emit(format!(
                    "`{name}` is a top-level `val`, which never changes; it cannot be assigned to"
                )));
            }
            return Err(if fb.env.contains_key(name) {
                CompileError::emit(format!("`{name}` is bound by `val` and cannot be assigned to; declare it with `var`"))
            } else {
                CompileError::emit(format!("cannot assign to `{name}`: no such variable"))
            });
        }
        let v = self.emit_expr(value, fb, registry, module)?;
        let cell = fb.cells[name].clone();
        if v.ty != cell.ty {
            return Err(CompileError::emit(format!(
                "cannot assign a value of type {} to `{name}`, whose type is {}",
                llvm_ty_str(v.ty),
                llvm_ty_str(cell.ty)
            )));
        }
        fb.line(format!("store {} {}, ptr {}", llvm_ty_str(v.ty), v.reg, cell.ptr));
        Ok(FnValue { reg: String::new(), ty: LlvmType::Void })
    }

    /// `while (cond) body`.
    ///
    /// The condition gets a block of its own.  That is not a stylistic
    /// choice: the instructions computing it must be re-executed on every
    /// turn, and instructions emitted into the entry block would run once.
    fn emit_while(&self, cond: &Expr, body: &Expr, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        let id = fb.fresh_block_id();
        let (chead, cbody, cend) = (format!("while.cond.{id}"), format!("while.body.{id}"), format!("while.end.{id}"));

        fb.line(format!("br label %{chead}"));
        fb.label(&chead);
        let cv = self.emit_expr(cond, fb, registry, module)?;
        if cv.ty != LlvmType::I1 {
            return Err(CompileError::emit("a `while` condition must be a bool"));
        }
        fb.line(format!("br i1 {}, label %{cbody}, label %{cend}", cv.reg));

        fb.label(&cbody);
        fb.loop_exits.push(cend.clone());
        let body_result = self.emit_expr(body, fb, registry, module);
        fb.loop_exits.pop();
        body_result?;
        fb.line(format!("br label %{chead}"));

        fb.label(&cend);
        Ok(FnValue { reg: String::new(), ty: LlvmType::Void })
    }

    /// `for (init; cond; step) body`.
    ///
    /// The step gets its own block rather than being appended to the body.
    /// Both lower to the same machine code, but keeping them apart means
    /// the loop's three parts are still legible in the IR — and it is
    /// where a `continue` would land if the subset ever grows one.
    fn emit_for(&self, init: &Expr, cond: &Expr, step: &Expr, body: &Expr, fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        let id = fb.fresh_block_id();
        let (chead, cbody, cstep, cend) = (
            format!("for.cond.{id}"),
            format!("for.body.{id}"),
            format!("for.step.{id}"),
            format!("for.end.{id}"),
        );

        self.emit_expr(init, fb, registry, module)?;
        fb.line(format!("br label %{chead}"));

        fb.label(&chead);
        let cv = self.emit_expr(cond, fb, registry, module)?;
        if cv.ty != LlvmType::I1 {
            return Err(CompileError::emit("a `for` condition must be a bool"));
        }
        fb.line(format!("br i1 {}, label %{cbody}, label %{cend}", cv.reg));

        fb.label(&cbody);
        fb.loop_exits.push(cend.clone());
        let body_result = self.emit_expr(body, fb, registry, module);
        fb.loop_exits.pop();
        body_result?;
        fb.line(format!("br label %{cstep}"));

        fb.label(&cstep);
        self.emit_expr(step, fb, registry, module)?;
        fb.line(format!("br label %{chead}"));

        fb.label(&cend);
        Ok(FnValue { reg: String::new(), ty: LlvmType::Void })
    }

    /// `assertloc(cond)` — ATS's located assertion.  It is not a function
    /// call but a *branch*: on failure it reports where it stood and
    /// leaves through `exit(1)`, so the success path costs one test and a
    /// perfectly predicted jump.
    fn emit_assert(&self, args: &[Expr], fb: &mut FnBuilder, registry: &Registry, module: &mut ModuleBuilder) -> Result<FnValue, CompileError> {
        let [cond] = args else {
            return Err(CompileError::emit("`assertloc` takes exactly one argument"));
        };
        let c = self.emit_expr(cond, fb, registry, module)?;
        if c.ty != LlvmType::I1 {
            return Err(CompileError::emit("`assertloc` requires a bool argument"));
        }
        let id = fb.fresh_block_id();
        let (fail, ok) = (format!("assert.fail.{id}"), format!("assert.ok.{id}"));
        fb.line(format!("br i1 {}, label %{ok}, label %{fail}", c.reg));
        fb.label(&fail);
        self.emit_printf(Stream::Stderr, "exit(ATS): assertion failed\n", &[], fb, module);
        fb.line("call void @exit(i32 1)");
        fb.line("unreachable");
        fb.label(&ok);
        Ok(FnValue { reg: String::new(), ty: LlvmType::Void })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    fn emit(source: &str) -> Result<String, CompileError> {
        let program = Parser::parse(source).expect("parse");
        LlvmIrEmitter::emit(&program)
    }

    fn emit_err(source: &str) -> CompileError {
        emit(source).expect_err("should fail")
    }

    // --- module shape ---------------------------------------------

    #[test]
    fn module_starts_with_identifier_and_printf_declaration() {
        let ir = emit("").expect("emit");
        assert!(ir.starts_with("; ModuleID = 'ats2llvm'"), "got:\n{ir}");
        assert!(ir.contains("declare i32 @printf(ptr, ...)"), "got:\n{ir}");
    }

    #[test]
    fn emits_a_simple_function_exactly() {
        let ir = emit("fun f(x: int): int = x + 1").expect("emit");
        let expected = "define i64 @f(i64 %x) {\nentry:\n  %t.0 = add i64 %x, 1\n  ret i64 %t.0\n}";
        assert!(ir.contains(expected), "got:\n{ir}");
    }

    // --- functions and recursion ----------------------------------

    #[test]
    fn emits_recursive_calls_to_functions_defined_anywhere() {
        let ir = emit("fun fact(n: int): int = if n = 0 then 1 else n * fact(n - 1)").expect("emit");
        assert!(ir.contains("define i64 @fact(i64 %n)"), "got:\n{ir}");
        assert!(ir.contains("call i64 @fact(i64 %t."), "got:\n{ir}");
        assert!(ir.contains("icmp eq i64 %n, 0"), "got:\n{ir}");
        assert!(ir.contains("phi i64"), "got:\n{ir}");
    }

    #[test]
    fn emits_multiple_functions_in_source_order() {
        let ir = emit("fun a(): int = 1\nfun b(): int = 2").expect("emit");
        let ia = ir.find("define i64 @a").expect("a");
        let ib = ir.find("define i64 @b").expect("b");
        assert!(ia < ib, "got:\n{ir}");
    }

    // --- top-level `var` (statically allocated references) ---------

    #[test]
    fn a_top_level_var_is_a_dereferenceable_reference() {
        // `var x: int = 0` outside any body is storage whose address
        // outlives every call: `!x` must read it back.
        let ir = emit(
            "var _count_: int = 0\nfun get(): int = !_count_\nimplement main0 () = ()",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @get()"), "got:\n{ir}");
    }

    #[test]
    fn a_top_level_var_reads_its_type_off_the_annotation() {
        // The initializer here (`if`) is not one of the shapes the
        // emitter can type on its own, so only the annotation can say
        // what the cell holds.
        let ir = emit(
            "var flag: int = if true then 1 else 0\nfun get(): int = !flag\nimplement main0 () = ()",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @get()"), "got:\n{ir}");
    }

    #[test]
    fn a_global_ref_gets_its_type_from_the_value_it_wraps() {
        // `val r = ref(0)` — the type is the one-slot tuple of the
        // wrapped value's type, read off the call itself.
        let ir = emit(
            "val r = ref(0)\nfun get(): int = !r\nimplement main0 () = ()",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @get()"), "got:\n{ir}");
    }

    #[test]
    fn ref_make_viewptr_takes_the_type_of_the_storage_it_wraps() {
        // `ref_make_viewptr (view@ x | addr@ x)` hands back the cell `x`
        // already is, so its type is `x`'s.
        let ir = emit(
            "var cell: int = 0\nval r = ref_make_viewptr (view@ cell | addr@ cell)\nfun get(): int = !r\nimplement main0 () = ()",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @get()"), "got:\n{ir}");
    }

    #[test]
    fn unknown_function_calls_are_errors() {
        let err = emit_err("fun f(x: int): int = g(x)");
        assert!(err.message().contains("unknown function"), "{}", err);
    }

    #[test]
    fn wrong_argument_count_is_an_error() {
        let err = emit_err("fun f(x: int): int = f()");
        assert!(err.message().contains("argument"), "{}", err);
    }

    // --- if / short-circuit ---------------------------------------

    #[test]
    fn emits_if_as_branches_and_a_phi() {
        let ir = emit("fun f(x: int): int = if x = 0 then 1 else 2").expect("emit");
        assert!(ir.contains("br i1 %t.0, label %if.t.0, label %if.e.0"), "got:\n{ir}");
        assert!(ir.contains("if.t.0:"), "got:\n{ir}");
        assert!(ir.contains("if.e.0:"), "got:\n{ir}");
        assert!(ir.contains("if.m.0:"), "got:\n{ir}");
        assert!(ir.contains("phi i64 [ 1, %if.t.0 ], [ 2, %if.e.0 ]"), "got:\n{ir}");
    }

    #[test]
    fn emits_short_circuit_andalso_and_orelse() {
        let ir = emit("fun f(a: bool, b: bool): bool = a andalso b").expect("emit");
        assert!(ir.contains("br i1 %a, label %and.t.0, label %and.f.0"), "got:\n{ir}");
        assert!(ir.contains("phi i1 [ %b, %and.t.0 ], [ false, %and.f.0 ]"), "got:\n{ir}");

        let ir = emit("fun f(a: bool, b: bool): bool = a orelse b").expect("emit");
        assert!(ir.contains("phi i1 [ true, %or.t.0 ], [ %b, %or.f.0 ]"), "got:\n{ir}");
    }

    #[test]
    fn if_condition_must_be_a_bool() {
        let err = emit_err("fun f(x: int): int = if x then 1 else 2");
        assert!(err.message().contains("bool"), "{}", err);
    }

    #[test]
    fn if_branches_must_agree_on_a_type() {
        let err = emit_err("fun f(x: int): int = if true then 1 else true");
        assert!(err.message().contains("types"), "{}", err);
    }

    // --- let bindings ---------------------------------------------

    #[test]
    fn emits_let_bindings_in_order() {
        let ir = emit("fun f(x: int): int = let val y = x + 1 in y * 2 end").expect("emit");
        assert!(ir.contains("%t.0 = add i64 %x, 1"), "got:\n{ir}");
        assert!(ir.contains("%t.1 = mul i64 %t.0, 2"), "got:\n{ir}");
    }

    #[test]
    fn let_bind_type_annotations_are_checked() {
        let err = emit_err("fun f(x: int): int = let val y: bool = x in 0 end");
        assert!(err.message().contains("type"), "{}", err);
    }

    #[test]
    fn discard_bindings_evaluate_but_are_ignored() {
        let ir = emit("implement main0() = { val () = f(1); println!(\"ok\") }\nfun f(x: int): int = x").expect("emit");
        assert!(ir.contains("call i64 @f(i64 1)"), "got:\n{ir}");
        assert!(ir.contains("ret i32 0"), "got:\n{ir}");
    }

    // --- literals and strings -------------------------------------

    #[test]
    fn emits_string_constants_and_returns_their_addresses() {
        let ir = emit("fun f(): string = \"hi\"").expect("emit");
        assert!(ir.contains("@.str.0 = private unnamed_addr constant [3 x i8] c\"hi\\00\""), "got:\n{ir}");
        // With opaque pointers, the global's address is the value itself.
        assert!(ir.contains("ret ptr @.str.0"), "got:\n{ir}");
    }

    #[test]
    fn string_constants_are_deduplicated() {
        let ir = emit("fun f(): string = \"hi\"\nfun g(): string = \"hi\"").expect("emit");
        assert_eq!(ir.matches("@.str.0 = private").count(), 1, "got:\n{ir}");
        assert!(!ir.contains("@.str.1"), "got:\n{ir}");
    }

    #[test]
    fn emits_escaped_string_bytes() {
        let ir = emit("fun f(): string = \"a\\tb\"").expect("emit");
        assert!(ir.contains("a\\09b"), "got:\n{ir}");
    }

    #[test]
    fn emits_bool_and_int_literals() {
        let ir = emit("fun t(): bool = true\nfun f(): int = 42").expect("emit");
        assert!(ir.contains("ret i1 true"), "got:\n{ir}");
        assert!(ir.contains("ret i64 42"), "got:\n{ir}");
    }

    // --- main0 ----------------------------------------------------

    #[test]
    fn implements_main0_as_the_entry_point() {
        let ir = emit("implement main0() = println!(\"ok\")").expect("emit");
        assert!(ir.contains("define i32 @main()"), "got:\n{ir}");
        assert!(ir.contains("ret i32 0"), "got:\n{ir}");
    }

    #[test]
    fn main0_cannot_be_called_like_a_function() {
        let err = emit_err("fun f(): int = main0()");
        assert!(err.message().contains("main0"), "{}", err);
    }

    #[test]
    fn implementing_an_undeclared_name_is_rejected() {
        // Any name may be implemented now, but only if something declared
        // it: the declaration is where the parameter types come from.
        let err = emit_err("implement something() = println!(\"hi\")");
        assert!(err.message().contains("never declared"), "{}", err);
    }

    // --- println! -------------------------------------------------

    #[test]
    fn println_builds_a_printf_call_from_the_literal() {
        let ir = emit("implement main0() = println!(\"fact(5) = \", fact(5))\nfun fact(n: int): int = 1").expect("emit");
        assert!(ir.contains("@.fmt.0 = private unnamed_addr constant [15 x i8] c\"fact(5) = %ld\\0A\\00\""), "got:\n{ir}");
        assert!(ir.contains("call i32 (ptr, ...) @printf"), "got:\n{ir}");
        assert!(ir.contains("call i64 @fact(i64 5)"), "got:\n{ir}");
    }

    #[test]
    fn println_mixes_strings_and_values_in_the_format() {
        let ir = emit(
            "implement main0() = let val s = \"z\" in println!(\"x=\", 1, \" y=\", s) end",
        ).expect("emit");
        // The runtime format is  x=%ld y=%s<newline>
        assert!(ir.contains("x=%ld y=%s"), "got:\n{ir}");
    }

    #[test]
    fn literal_percent_is_doubled_in_printf_formats_but_not_in_strings() {
        let ir = emit(
            "implement main0() = println!(\"100% done\")\nfun s(): string = \"100%\"",
        ).expect("emit");
        // format: 100%% done + newline ; string: 100% unchanged
        assert!(ir.contains("100%% done"), "got:\n{ir}");
        assert!(ir.contains("c\"100%\\00\""), "got:\n{ir}");
    }

    #[test]
    fn unknown_macros_are_errors() {
        let err = emit_err("fun f(): int = magic!(1)");
        assert!(err.message().contains("macro"), "{}", err);
    }

    #[test]
    fn printing_a_bool_selects_between_two_words() {
        // ATS prints a bool as `true`/`false`.  A `select` picks the
        // constant, so printing costs no branch.
        let ir = emit("implement main0() = println!(true)").expect("emit");
        assert!(ir.contains("select i1 true, ptr @.str."), "got:\n{ir}");
        assert!(ir.contains(r#"c"true\00""#), "got:\n{ir}");
        assert!(ir.contains(r#"c"false\00""#), "got:\n{ir}");
    }

    // --- tuples and nested patterns ---------------------------------

    #[test]
    fn a_tuple_is_a_record_of_its_components() {
        let ir = emit("fun pair(): (int, int) = (1, 2) implement main0() = println!(1)").expect("emit");
        assert!(ir.contains("define ptr @pair()"), "got:\n{ir}");
        assert!(ir.contains("store i64 1, ptr"), "got:\n{ir}");
        assert!(ir.contains("store i64 2, ptr"), "got:\n{ir}");
    }

    #[test]
    fn a_flat_tuple_is_written_the_same_way() {
        let ir = emit("fun pair(): @(int, bool) = @(1, true) implement main0() = println!(1)").expect("emit");
        assert!(ir.contains("define ptr @pair()"), "got:\n{ir}");
    }

    #[test]
    fn a_tuple_pattern_binds_each_component() {
        let ir = emit(
            "fun fst(p: (int, int)): int = case p of | (a, b) => a \
             implement main0() = println!(fst((3, 4)))",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @fst(ptr %p)"), "got:\n{ir}");
    }

    #[test]
    fn a_tuple_of_the_wrong_width_is_an_error() {
        let err = emit_err("fun f(p: (int, int)): int = case p of | (a, b, c) => a");
        assert!(err.message().contains("2") || err.message().contains("width"), "{err}");
    }

    #[test]
    fn a_pattern_may_nest_inside_a_constructor() {
        let ir = emit(
            "datatype lst(a) = Nil of () | Cons of (a, lst(a)) \
             fun second(xs: lst(int)): int = case xs of | Cons(_, Cons(y, _)) => y | _ => 0 \
             implement main0() = println!(second(Cons(1, Cons(2, Nil()))))",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @second(ptr %xs)"), "got:\n{ir}");
    }

    #[test]
    fn a_nested_pattern_is_tested_only_after_the_outer_one_matches() {
        // Reading the tail's tag before knowing the value *is* a `Cons`
        // would follow whatever the other constructor left in that slot.
        // So the inner test must sit in its own block, reached only when
        // the outer test succeeded.
        let ir = emit(
            "datatype lst(a) = Nil of () | Cons of (a, lst(a)) \
             fun second(xs: lst(int)): int = case xs of | Cons(_, Cons(y, _)) => y | _ => 0 \
             implement main0() = println!(second(Nil()))",
        )
        .expect("emit");
        let tests = ir.matches("icmp eq i64").count();
        assert!(tests >= 2, "expected an outer and an inner tag test, got {tests}:\n{ir}");
    }

    #[test]
    fn every_constructor_of_a_datatype_reserves_the_same_room() {
        // A `Nil` is allocated as wide as a `Cons`, so that reading a
        // field of one always lands inside the value rather than past it.
        let ir = emit(
            "datatype lst(a) = Nil of () | Cons of (a, lst(a)) \
             implement main0() = let val x: lst(int) = Nil() in println!(1) end",
        )
        .expect("emit");
        // tag + two fields = three words, even for the nullary case.
        assert!(ir.contains("call ptr @.ats_alloc(i64 24)"), "Nil must reserve the full width:\n{ir}");
    }

    #[test]
    fn a_tuple_pattern_may_hold_constructors() {
        let ir = emit(
            "datatype lst(a) = Nil of () | Cons of (a, lst(a)) \
             fun both(p: (lst(int), lst(int))): int = \
               case p of | (Cons(x, _), Cons(y, _)) => x + y | _ => 0 \
             implement main0() = println!(both((Cons(1, Nil()), Cons(2, Nil()))))",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @both(ptr %p)"), "got:\n{ir}");
    }

    // --- floating point ---------------------------------------------

    #[test]
    fn a_double_is_an_llvm_double() {
        let ir = emit("fun f(x: double): double = x").expect("emit");
        assert!(ir.contains("define double @f(double %x)"), "got:\n{ir}");
    }

    #[test]
    fn a_float_literal_keeps_its_value() {
        let ir = emit("fun f(): double = 1.5 implement main0() = println!(1)").expect("emit");
        assert!(ir.contains("ret double 1.5"), "got:\n{ir}");
    }

    #[test]
    fn double_arithmetic_uses_the_floating_instructions() {
        let ir = emit("fun f(x: double, y: double): double = x * y + x").expect("emit");
        assert!(ir.contains("fmul double"), "got:\n{ir}");
        assert!(ir.contains("fadd double"), "got:\n{ir}");
    }

    #[test]
    fn doubles_compare_with_the_ordered_predicates() {
        let ir = emit("fun f(x: double, y: double): bool = x < y").expect("emit");
        assert!(ir.contains("fcmp olt double"), "got:\n{ir}");
    }

    #[test]
    fn printing_a_double_uses_the_float_placeholder() {
        let ir = emit("fun f(x: double): void = println!(x)").expect("emit");
        assert!(ir.contains("%f"), "got:\n{ir}");
    }

    #[test]
    fn an_int_converts_to_a_double_when_asked() {
        let ir = emit("fun f(n: int): double = int2double(n)").expect("emit");
        assert!(ir.contains("sitofp i64"), "got:\n{ir}");
    }

    #[test]
    fn mixing_an_int_and_a_double_widens_the_int() {
        // Changed deliberately: this used to be an error.
        //
        // ATS resolves `x * n` through the prelude's overloads, which
        // are keyed on *both* operand types (`gmul_double_int`).  This
        // compiler's overload table maps an operator to a single
        // function, so it cannot express that, and refusing the
        // expression outright was the wrong half of the trade: it made
        // `10 * env` unwritable in code where `env` is a double, which
        // is how the corpus writes it.  Widening loses the check that
        // the two operands agree; it gains the arithmetic ATS programs
        // actually contain.
        let ir = emit("fun f(x: double, n: int): double = x * n implement main0() = println!(f(1.5, 2))")
            .expect("emit");
        assert!(ir.contains("sitofp i64"), "the int must widen:\n{ir}");
        assert!(ir.contains("fmul double"), "the product must be a float one:\n{ir}");
    }

    // --- macdef, overload, and the generic numeric shims -------------

    #[test]
    fn a_macdef_stands_for_the_expression_it_names() {
        let ir = emit(
            "fun twice (n: int): int = n + n \
             implement main0() = let macdef f = twice in println!(f(21)) end",
        )
        .expect("emit");
        assert!(ir.contains("call i64 @twice(i64 21)"), "got:\n{ir}");
    }

    #[test]
    fn a_macdef_may_name_a_template_instance() {
        let ir = emit(
            "extern fun{a:t@ype} id (x: a): a implement{a} id (x) = x \
             implement main0() = let macdef g = id<int> in println!(g(4)) end",
        )
        .expect("emit");
        assert!(ir.contains("call i64 @id$int(i64 4)"), "got:\n{ir}");
    }

    #[test]
    fn gnumber_int_builds_a_number_of_the_type_asked_for() {
        let ir = emit("fun one(): double = gnumber_int<double>(1)").expect("emit");
        assert!(ir.contains("ret double 1.0"), "got:\n{ir}");

        let ir = emit("fun one(): int = gnumber_int<int>(1)").expect("emit");
        assert!(ir.contains("ret i64 1"), "got:\n{ir}");
    }

    #[test]
    fn an_overload_supplies_an_operator_the_types_do_not_fit() {
        // `int * double` has no native instruction; the program's own
        // `overload` declaration says which function to use instead.
        let ir = emit(
            "overload * with gmul_int_val \
             fun scale (n: int, x: double): double = n * x",
        )
        .expect("emit");
        assert!(ir.contains("sitofp i64"), "the int must be promoted:\n{ir}");
        assert!(ir.contains("fmul double"), "got:\n{ir}");
    }

    #[test]
    fn an_overload_is_not_consulted_when_the_types_already_fit() {
        let ir = emit("overload * with gmul_int_val fun f (a: int, b: int): int = a * b").expect("emit");
        assert!(ir.contains("mul i64"), "got:\n{ir}");
        assert!(!ir.contains("sitofp"), "no promotion should happen:\n{ir}");
    }

    #[test]
    fn a_generic_comparison_shim_accepts_either_numeric_type() {
        let ir = emit(
            "overload > with ggt_val_int \
             fun big (x: double): bool = x > 0",
        )
        .expect("emit");
        assert!(ir.contains("fcmp ogt double"), "got:\n{ir}");
    }

    #[test]
    fn an_unfitting_operator_with_no_overload_is_still_an_error() {
        // Numbers widen (see `mixing_an_int_and_a_double_widens_the_int`);
        // things that are not numbers still do not.
        let err = emit_err("fun f (s: string, x: double): double = s * x");
        assert!(err.message().contains("ptr") || err.message().contains("operand"), "{err}");
    }

    // --- the prelude's functions ------------------------------------

    #[test]
    fn list0_is_nil_comes_from_the_prelude() {
        let ir = emit(
            "fun f(xs: list0(int)): bool = list0_is_nil(xs) implement main0() = println!(1)",
        )
        .expect("emit");
        assert!(ir.contains("@list0_is_nil$int"), "got:\n{ir}");
    }

    #[test]
    fn a_prelude_function_is_left_out_when_nothing_calls_it() {
        let ir = emit("implement main0() = println!(1)").expect("emit");
        assert!(!ir.contains("list0_is_nil"), "got:\n{ir}");
        assert!(!ir.contains("string_isnot_empty"), "got:\n{ir}");
    }

    #[test]
    fn a_prelude_function_may_call_another() {
        // `string_isnot_empty` is written in terms of `string_length`,
        // so pulling the first in must pull the second.
        let ir = emit("fun f(s: string): bool = string_isnot_empty(s)").expect("emit");
        assert!(ir.contains("@strlen"), "got:\n{ir}");
    }

    #[test]
    fn the_program_may_define_a_prelude_name_itself() {
        let ir = emit(
            "fun string_isnot_empty(s: string): bool = false \
             implement main0() = println!(string_isnot_empty(\"x\"))",
        )
        .expect("emit");
        assert_eq!(ir.matches("define i1 @string_isnot_empty").count(), 1, "got:\n{ir}");
    }

    #[test]
    fn reading_a_line_yields_a_string_or_nothing() {
        let ir = emit(
            "implement main0() = let val s = fileref_get_line_string(stdin_ref) in \
             println!(string_is_null(s)) end",
        )
        .expect("emit");
        assert!(ir.contains("@fgetc"), "the line is read a character at a time:\n{ir}");
        assert!(ir.contains("icmp eq ptr"), "the null result must be testable:\n{ir}");
    }

    #[test]
    fn the_lines_of_a_file_come_back_as_a_list() {
        let ir = emit(
            "implement main0() = let val ls = fileref_get_lines_stringlst(stdin_ref) in \
             println!(list0_is_nil(ls)) end",
        )
        .expect("emit");
        assert!(ir.contains("@fileref_get_lines_stringlst"), "got:\n{ir}");
        assert!(ir.contains("; datatype list0$string"), "got:\n{ir}");
    }

    // --- top-level values -------------------------------------------

    #[test]
    fn a_top_level_val_becomes_a_global() {
        let ir = emit("val limit = 10 implement main0() = println!(limit)").expect("emit");
        assert!(ir.contains("@limit = internal global i64"), "got:\n{ir}");
        assert!(ir.contains("load i64, ptr @limit"), "reading it is a load:\n{ir}");
    }

    #[test]
    fn a_top_level_val_is_initialised_before_main_runs() {
        let ir = emit("val limit = 6 * 7 implement main0() = println!(limit)").expect("emit");
        // The arithmetic happens in `main`, before anything else.
        let main = &ir[ir.find("define i32 @main").expect("a main")..];
        let store = main.find("store i64").expect("an initialising store");
        let print = main.find("@printf").expect("the printf");
        assert!(store < print, "the global must be set before it is read:\n{ir}");
    }

    #[test]
    fn a_top_level_val_is_visible_inside_functions() {
        let ir = emit("val limit = 10 fun over(n: int): bool = n > limit implement main0() = println!(over(3))")
            .expect("emit");
        assert!(ir.contains("load i64, ptr @limit"), "got:\n{ir}");
    }

    #[test]
    fn top_level_vals_are_initialised_in_order() {
        let ir = emit("val a = 2 val b = a + 1 implement main0() = println!(b)").expect("emit");
        let main = &ir[ir.find("define i32 @main").expect("a main")..];
        assert!(main.find("@a").expect("a") < main.find("@b").expect("b"), "got:\n{ir}");
    }

    #[test]
    fn a_top_level_val_may_hold_a_closure() {
        let ir = emit("val square = lam (x: int): int => x * x implement main0() = println!(square(5))")
            .expect("emit");
        assert!(ir.contains("@square = internal global ptr"), "got:\n{ir}");
        assert!(ir.contains("call i64 %"), "calling it is indirect:\n{ir}");
    }

    #[test]
    fn a_top_level_val_cannot_be_assigned_to() {
        let err = emit_err("val limit = 10 implement main0() = limit := 3");
        assert!(err.message().contains("limit"), "{err}");
    }

    // --- closures ----------------------------------------------------

    #[test]
    fn a_lambda_becomes_a_function_and_a_record() {
        let ir = emit(
            "fun mk(): (int) -> int = lam (n: int): int => n + 1 \
             implement main0() = println!(1)",
        )
        .expect("emit");
        // The body is lifted to a function of its own, taking the
        // environment as a first parameter.
        assert!(ir.contains("define i64 @lam."), "no lifted body in:\n{ir}");
        assert!(ir.contains("(ptr %env"), "the environment must be passed:\n{ir}");
    }

    #[test]
    fn a_closure_captures_what_it_reads() {
        let ir = emit(
            "fun adder(m: int): (int) -> int = lam (n: int): int => m + n \
             implement main0() = println!(1)",
        )
        .expect("emit");
        // `m` belongs to `adder`, so it is copied into the record and
        // read back out inside the lambda.
        assert!(ir.contains("store i64 %m, ptr"), "the capture must be stored:\n{ir}");
        assert!(ir.contains("load i64, ptr"), "and loaded inside:\n{ir}");
    }

    #[test]
    fn calling_a_closure_goes_through_its_code_pointer() {
        let ir = emit(
            "fun adder(m: int): (int) -> int = lam (n: int): int => m + n \
             implement main0() = println!(adder(1)(2))",
        )
        .expect("emit");
        assert!(ir.contains("load ptr, ptr"), "the code pointer must be loaded:\n{ir}");
        assert!(ir.contains("call i64 %"), "the call must be indirect:\n{ir}");
    }

    #[test]
    fn a_function_may_infer_its_return_type_from_a_lambda_body() {
        // `fun acker (m: int) = lam (n: int): int => ...` writes no return
        // type; the lambda's own annotations say what it is.
        let ir = emit(
            "fun adder(m: int) = lam (n: int): int => m + n \
             implement main0() = println!(adder(1)(2))",
        )
        .expect("emit");
        assert!(ir.contains("define ptr @adder(i64 %m)"), "got:\n{ir}");
    }

    #[test]
    fn the_closure_arrow_annotation_is_accepted() {
        // `=<cloptr1>` says how the closure is allocated, which the arena
        // settles for us.
        let ir = emit(
            "fun adder(m: int) = lam (n: int): int =<cloptr1> m + n \
             implement main0() = println!(adder(1)(2))",
        )
        .expect("emit");
        assert!(ir.contains("define ptr @adder(i64 %m)"), "got:\n{ir}");
    }

    #[test]
    fn a_curried_call_still_flattens_when_the_arity_fits() {
        // Currying without closures must keep working: this `f` takes two
        // parameters, so `f(1)(2)` is one direct call.
        let ir = emit("fun f(a: int)(b: int): int = a + b implement main0() = println!(f(1)(2))")
            .expect("emit");
        assert!(ir.contains("call i64 @f(i64 1, i64 2)"), "got:\n{ir}");
    }

    #[test]
    fn a_closure_may_be_recursive_through_its_maker() {
        let ir = emit(
            "fun countdown(m: int) = lam (n: int): int =<cloptr1> \
               if m <= 0 then n else countdown(m - 1)(n + 1) \
             implement main0() = println!(countdown(3)(0))",
        )
        .expect("emit");
        assert!(ir.contains("call ptr @countdown"), "got:\n{ir}");
    }

    #[test]
    fn calling_a_non_function_is_still_an_error() {
        let err = emit_err("implement main0() = let val x: int = 1 in println!(x(1)) end");
        assert!(err.message().contains("call") || err.message().contains("function"), "{err}");
    }

    // --- characters --------------------------------------------------

    #[test]
    fn a_char_is_a_byte() {
        let ir = emit("fun f(c: char): char = c").expect("emit");
        assert!(ir.contains("define i8 @f(i8 %c)"), "got:\n{ir}");
    }

    #[test]
    fn a_character_literal_is_its_byte_value() {
        let ir = emit("fun nl(): char = '\\n' implement main0() = println!(1)").expect("emit");
        assert!(ir.contains("ret i8 10"), "got:\n{ir}");
    }

    #[test]
    fn printing_a_char_uses_the_character_placeholder() {
        let ir = emit("implement main0() = println!('a')").expect("emit");
        assert!(ir.contains("%c"), "got:\n{ir}");
    }

    #[test]
    fn print_char_writes_one_character() {
        let ir = emit("implement main0() = print_char('x')").expect("emit");
        assert!(ir.contains("@putchar") || ir.contains("%c"), "got:\n{ir}");
    }

    #[test]
    fn print_int_and_print_string_are_the_obvious_shims() {
        let ir = emit("implement main0() = { val () = print_int(7) val () = print_string(\"s\") }")
            .expect("emit");
        assert!(ir.contains("i64 7"), "got:\n{ir}");
        assert!(ir.contains(r#"c"s\00""#), "got:\n{ir}");
    }

    #[test]
    fn a_char_compares_with_a_char() {
        let ir = emit("fun is_nl(c: char): bool = c = '\\n'").expect("emit");
        assert!(ir.contains("icmp eq i8"), "got:\n{ir}");
    }

    #[test]
    fn a_char_converts_to_and_from_an_int() {
        let ir = emit(
            "fun digit(c: char): int = char2int(c) - char2int('0') \
             implement main0() = println!(digit('7'))",
        )
        .expect("emit");
        assert!(ir.contains("sext i8"), "got:\n{ir}");
    }

    #[test]
    fn a_char_widens_to_an_int_in_arithmetic() {
        // Changed deliberately: this used to be an error.  ATS treats a
        // character as a small integer, and `c - '0'` is the idiom every
        // digit-parsing loop in the corpus is built on, so arithmetic
        // widens rather than refusing.
        let ir = emit("fun f(c: char): int = c + 1 implement main0() = println!(f('a'))").expect("emit");
        assert!(ir.contains("sext i8"), "expected the char to widen:\n{ir}");
    }

    #[test]
    fn a_char_is_still_not_an_int_outside_arithmetic() {
        // Widening is confined to arithmetic: the two types stay
        // distinct, so a `char` cannot stand in for an `int` where a
        // signature asks for one.
        let err = emit_err("fun g(n: int): int = n fun f(c: char): int = g(c)");
        assert!(err.message().contains("char") || err.message().contains("i8"), "{err}");
    }

    // --- the prelude's list -----------------------------------------

    #[test]
    fn the_prelude_list_needs_no_declaration() {
        // `list0` comes from the prelude, which real programs reach
        // through `staload`; a program may use it without declaring it.
        let ir = emit(
            "fun ints(): list0(int) = list0_cons(1, list0_nil()) \
             implement main0() = println!(1)",
        )
        .expect("emit");
        assert!(ir.contains("; datatype list0$int"), "got:\n{ir}");
    }

    #[test]
    fn nil_and_cons_are_the_prelude_names_too() {
        let ir = emit("fun ints(): list0(int) = cons(1, nil()) implement main0() = println!(1)")
            .expect("emit");
        assert!(ir.contains("; datatype list0$int"), "got:\n{ir}");
    }

    #[test]
    fn the_capitalised_spelling_names_the_same_type() {
        // `List0(t)` and `list0(t)` are one type, so a value of one may be
        // passed where the other is expected.
        let ir = emit(
            "fun mk(): List0(int) = cons(1, nil()) \
             fun take(xs: list0(int)): int = case xs of | cons(x, _) => x | nil() => 0 \
             implement main0() = println!(take(mk()))",
        )
        .expect("emit");
        assert_eq!(ir.matches("; datatype list0$int").count(), 1, "got:\n{ir}");
    }

    #[test]
    fn the_indexed_list_erases_its_length() {
        // `list(t, n)` is the length-indexed list; the length is static,
        // so it names the same runtime type as `list0(t)`.
        let ir = emit(
            "fun mk(): list(int, n) = cons(1, nil()) \
             fun take(xs: list0(int)): int = case xs of | cons(x, _) => x | nil() => 0 \
             implement main0() = println!(take(mk()))",
        )
        .expect("emit");
        assert_eq!(ir.matches("; datatype list0$int").count(), 1, "got:\n{ir}");
    }

    #[test]
    fn a_program_may_still_declare_its_own_list0() {
        // The prelude must not shadow a declaration the program made.
        let ir = emit(
            "datatype list0(a) = list0_nil of () | list0_cons of (a, list0(a)) \
             fun ints(): list0(int) = list0_cons(1, list0_nil()) \
             implement main0() = println!(1)",
        )
        .expect("emit");
        assert_eq!(ir.matches("; datatype list0$int").count(), 1, "got:\n{ir}");
    }

    #[test]
    fn the_prelude_costs_nothing_when_unused() {
        let ir = emit("implement main0() = println!(1)").expect("emit");
        assert!(!ir.contains("list0"), "got:\n{ir}");
    }

    #[test]
    fn a_template_over_the_prelude_list_infers_its_instance() {
        // This is the shape `listfuns` uses: a template whose parameter is
        // `List0(a)`, called with no instantiation.
        let ir = emit(
            "fun mk(): List0(int) = cons(1, nil()) \
             extern fun{a:t@ype} len (xs: List0(INV(a))): int \
             implement{a} len (xs) = case xs of | cons(_, r) => 1 + len(r) | nil() => 0 \
             implement main0() = println!(len(mk()))",
        )
        .expect("emit");
        assert!(ir.contains("@len$int"), "got:\n{ir}");
    }

    // --- inferring which instance a template call means -------------

    const ID: &str = "extern fun{a:t@ype} id (x: a): a implement{a} id (x) = x ";

    #[test]
    fn a_template_call_infers_its_instance_from_the_argument() {
        // `id(5)` names no instance; the argument's type settles it.
        let ir = emit(&format!("{ID} implement main0() = println!(id(5))")).expect("emit");
        assert!(ir.contains("define i64 @id$int(i64 %x)"), "got:\n{ir}");
        assert!(ir.contains("call i64 @id$int(i64 5)"), "got:\n{ir}");
    }

    #[test]
    fn the_same_template_infers_different_instances() {
        let ir = emit(&format!(
            "{ID} implement main0() = println!(id(5), id(\"s\"), id(true))"
        ))
        .expect("emit");
        assert!(ir.contains("define i64 @id$int"), "got:\n{ir}");
        assert!(ir.contains("define ptr @id$string"), "got:\n{ir}");
        assert!(ir.contains("define i1 @id$bool"), "got:\n{ir}");
    }

    #[test]
    fn inference_sees_through_a_let_binding() {
        let ir = emit(&format!(
            "{ID} implement main0() = let val n = 7 in println!(id(n)) end"
        ))
        .expect("emit");
        assert!(ir.contains("call i64 @id$int"), "got:\n{ir}");
    }

    #[test]
    fn inference_sees_through_a_function_result() {
        let ir = emit(&format!(
            "{ID} fun get(): string = \"x\" implement main0() = println!(id(get()))"
        ))
        .expect("emit");
        assert!(ir.contains("call ptr @id$string"), "got:\n{ir}");
    }

    #[test]
    fn inference_reaches_inside_a_parameterized_datatype() {
        // The interesting case: the template's parameter is `lst(a)` and
        // the argument is a `lst(int)`, so `a` is found by matching the
        // two types against each other rather than by looking at one.
        let ir = emit(
            "datatype lst(a) = Nil of () | Cons of (a, lst(a)) \
             extern fun{a:t@ype} count (xs: lst(a)): int \
             implement{a} count (xs) = case xs of | Nil() => 0 | Cons(_, r) => 1 + count<a>(r) \
             fun ints(): lst(int) = Cons(1, Nil()) \
             implement main0() = println!(count(ints()))",
        )
        .expect("emit");
        assert!(ir.contains("@count$int"), "got:\n{ir}");
    }

    #[test]
    fn an_explicit_instantiation_still_wins() {
        let ir = emit(&format!("{ID} implement main0() = println!(id<int>(5))")).expect("emit");
        assert!(ir.contains("call i64 @id$int"), "got:\n{ir}");
    }

    #[test]
    fn a_template_whose_instance_cannot_be_inferred_says_so() {
        // Nothing here mentions `a` at all, so no argument can reveal it.
        let err = emit_err(
            "extern fun{a:t@ype} mystery (n: int): int implement{a} mystery (n) = n \
             implement main0() = println!(mystery(1))",
        );
        assert!(err.message().contains("mystery"), "{err}");
    }

    // --- parameterized datatypes ------------------------------------

    const OPT: &str = "datatype opt(a) = None of () | Some of a ";

    #[test]
    fn a_parameterized_datatype_is_instantiated_per_element_type() {
        let ir = emit(&format!(
            "{OPT} fun i(): opt(int) = Some(1) fun s(): opt(string) = Some(\"x\") \
             implement main0() = let val a = i() val b = s() in println!(1) end"
        ))
        .expect("emit");
        assert!(ir.contains("; datatype opt$int"), "no int instance in:\n{ir}");
        assert!(ir.contains("; datatype opt$string"), "no string instance in:\n{ir}");
    }

    #[test]
    fn a_bare_constructor_is_resolved_from_the_expected_type() {
        // `None()` says nothing about which `opt` it builds; the
        // function's declared return type does.
        let ir = emit(&format!("{OPT} fun none_int(): opt(int) = None() implement main0() = println!(1)"))
            .expect("emit");
        assert!(ir.contains("define ptr @none_int()"), "got:\n{ir}");
    }

    #[test]
    fn an_annotation_settles_a_constructor_too() {
        let ir = emit(&format!(
            "{OPT} implement main0() = let val x: opt(int) = None() in println!(1) end"
        ))
        .expect("emit");
        assert!(ir.contains("store i64 0, ptr"), "the tag must be stored:\n{ir}");
    }

    #[test]
    fn a_constructor_argument_is_checked_against_the_instance() {
        let err = emit_err(&format!("{OPT} fun f(): opt(int) = Some(\"wrong\")"));
        assert!(err.message().contains("Some"), "{err}");
    }

    #[test]
    fn an_unresolvable_constructor_says_so() {
        // Two instances exist and nothing says which is meant.
        let err = emit_err(&format!(
            "{OPT} fun i(): opt(int) = None() fun s(): opt(string) = None() \
             implement main0() = let val x = None() in println!(1) end"
        ));
        assert!(err.message().contains("None"), "{err}");
    }

    #[test]
    fn a_case_over_an_instance_binds_the_element_type() {
        let ir = emit(&format!(
            "{OPT} fun unwrap(o: opt(int)): int = case o of | Some(v) => v | None() => 0 \
             implement main0() = println!(unwrap(Some(7)))"
        ))
        .expect("emit");
        assert!(ir.contains("define i64 @unwrap(ptr %o)"), "got:\n{ir}");
        assert!(ir.contains("load i64, ptr"), "the field must load as an int:\n{ir}");
    }

    #[test]
    fn a_recursive_parameterized_datatype_instantiates_once() {
        let ir = emit(
            "datatype lst(a) = Nil of () | Cons of (a, lst(a)) \
             fun total(xs: lst(int)): int = case xs of | Nil() => 0 | Cons(x, r) => x + total(r) \
             implement main0() = println!(total(Cons(1, Cons(2, Nil()))))",
        )
        .expect("emit");
        assert_eq!(ir.matches("; datatype lst$int").count(), 1, "got:\n{ir}");
    }

    #[test]
    fn an_unused_parameterized_datatype_is_not_instantiated() {
        let ir = emit(&format!("{OPT} implement main0() = println!(1)")).expect("emit");
        assert!(!ir.contains("datatype opt$"), "got:\n{ir}");
    }

    // --- templates ---------------------------------------------------

    const IDENT: &str = "extern fun{a:t@ype} ident (x: a): a implement{a} ident (x) = x ";

    #[test]
    fn a_template_is_emitted_once_per_instantiation() {
        let ir = emit(&format!(
            "{IDENT} implement main0() = println!(ident<int>(1), ident<string>(\"s\"))"
        ))
        .expect("emit");
        assert!(ir.contains("define i64 @ident$int(i64 %x)"), "no int instance in:\n{ir}");
        assert!(ir.contains("define ptr @ident$string(ptr %x)"), "no string instance in:\n{ir}");
    }

    #[test]
    fn a_call_names_the_instance_it_wants() {
        let ir = emit(&format!("{IDENT} implement main0() = println!(ident<int>(1))")).expect("emit");
        assert!(ir.contains("call i64 @ident$int(i64 1)"), "got:\n{ir}");
    }

    #[test]
    fn an_unused_template_is_not_emitted_at_all() {
        // A template is a *recipe*.  With no instantiation there is no
        // function, which is also why its body is never type-checked.
        let ir = emit(&format!("{IDENT} implement main0() = println!(1)")).expect("emit");
        assert!(!ir.contains("@ident"), "got:\n{ir}");
    }

    #[test]
    fn the_same_instantiation_twice_emits_one_function() {
        let ir = emit(&format!(
            "{IDENT} implement main0() = println!(ident<int>(1), ident<int>(2))"
        ))
        .expect("emit");
        assert_eq!(ir.matches("define i64 @ident$int").count(), 1, "got:\n{ir}");
    }

    #[test]
    fn a_template_may_call_another_at_the_same_instantiation() {
        let ir = emit(
            "extern fun{a:t@ype} twice (x: a): a \
             extern fun{a:t@ype} once (x: a): a \
             implement{a} once (x) = x \
             implement{a} twice (x) = once<a>(once<a>(x)) \
             implement main0() = println!(twice<int>(3))",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @twice$int"), "got:\n{ir}");
        assert!(ir.contains("define i64 @once$int"), "got:\n{ir}");
        assert!(ir.contains("call i64 @once$int"), "got:\n{ir}");
    }

    #[test]
    fn a_recursive_template_instantiates_once() {
        let ir = emit(
            "extern fun{a:t@ype} count (n: int, x: a): int \
             implement{a} count (n, x) = if n <= 0 then 0 else 1 + count<a>(n - 1, x) \
             implement main0() = println!(count<int>(3, 0))",
        )
        .expect("emit");
        assert_eq!(ir.matches("define i64 @count$int").count(), 1, "got:\n{ir}");
    }

    #[test]
    fn instantiating_an_undeclared_template_is_an_error() {
        let err = emit_err("implement main0() = println!(nosuch<int>(1))");
        assert!(err.message().contains("nosuch"), "{err}");
    }

    #[test]
    fn a_template_with_no_implementation_is_an_error() {
        let err = emit_err("extern fun{a:t@ype} f (x: a): a implement main0() = println!(f<int>(1))");
        assert!(err.message().contains("f"), "{err}");
    }

    #[test]
    fn calling_a_template_without_saying_which_instance_now_infers_it() {
        // The instantiation used to have to be written out.  Inference
        // reads it off the argument instead.
        let ir = emit(&format!("{IDENT} implement main0() = println!(ident(1))")).expect("emit");
        assert!(ir.contains("call i64 @ident$int(i64 1)"), "got:\n{ir}");
    }

    // --- declarations and their definitions -------------------------

    #[test]
    fn an_implement_takes_its_types_from_the_declaration() {
        let ir = emit("extern fun twice (x: int): int implement twice (x) = x + x").expect("emit");
        assert!(ir.contains("define i64 @twice(i64 %x)"), "got:\n{ir}");
    }

    #[test]
    fn a_declared_function_can_be_called_before_it_is_defined() {
        let ir = emit(
            "extern fun twice (x: int): int implement main0() = println!(twice(21)) implement twice (x) = x + x",
        )
        .expect("emit");
        assert!(ir.contains("call i64 @twice(i64 21)"), "got:\n{ir}");
    }

    #[test]
    fn an_implement_may_still_annotate_its_parameters() {
        let ir = emit("extern fun twice (x: int): int implement twice (x: int): int = x + x").expect("emit");
        assert!(ir.contains("define i64 @twice(i64 %x)"), "got:\n{ir}");
    }

    #[test]
    fn implementing_something_never_declared_is_an_error() {
        let err = emit_err("implement nowhere (x) = x");
        assert!(err.message().contains("nowhere"), "{err}");
    }

    #[test]
    fn an_implement_must_agree_with_its_declaration_on_arity() {
        let err = emit_err("extern fun twice (x: int): int implement twice (x, y) = x");
        assert!(err.message().contains("twice"), "{err}");
    }

    #[test]
    fn a_declaration_with_no_definition_emits_nothing() {
        let ir = emit("extern fun twice (x: int): int").expect("emit");
        assert!(!ir.contains("define"), "got:\n{ir}");
    }

    // --- files ------------------------------------------------------

    #[test]
    fn the_standard_streams_are_loaded_from_libc_globals() {
        // `stdin`/`stdout`/`stderr` are C *variables* holding streams, so
        // reaching one costs a load.
        let ir = emit("implement main0() = let val f = stdin_ref in fileref_close(f) end").expect("emit");
        assert!(ir.contains("@stdin = external global ptr"), "got:\n{ir}");
        assert!(ir.contains("load ptr, ptr @stdin"), "got:\n{ir}");
    }

    #[test]
    fn a_fileref_parameter_is_a_pointer() {
        let ir = emit("fun f(inp: FILEref): void = fileref_close(inp)").expect("emit");
        assert!(ir.contains("define void @f(ptr %inp)"), "got:\n{ir}");
    }

    #[test]
    fn getc_and_putc_become_fgetc_and_fputc() {
        let ir = emit(
            "fun copy(i: FILEref, o: FILEref): void = let val c = fileref_getc(i) in fileref_putc(o, c) end",
        )
        .expect("emit");
        assert!(ir.contains("call i32 @fgetc(ptr"), "got:\n{ir}");
        assert!(ir.contains("call i32 @fputc(i32"), "got:\n{ir}");
    }

    #[test]
    fn getc_widens_its_result_to_the_subsets_int() {
        // `fgetc` yields a C `int`; every `int` here is an `i64`, and the
        // widening must be *signed* so EOF stays -1.
        let ir = emit("fun f(i: FILEref): int = fileref_getc(i)").expect("emit");
        assert!(ir.contains("sext i32"), "EOF must stay negative:\n{ir}");
    }

    #[test]
    fn opening_a_file_checks_the_result() {
        let ir = emit(
            "implement main0(argc, argv) = let val f = fileref_open_exn(argv[1], file_mode_r) in fileref_close(f) end",
        )
        .expect("emit");
        assert!(ir.contains("call ptr @fopen(ptr"), "got:\n{ir}");
        assert!(ir.contains("icmp eq ptr"), "a failed open must be detected:\n{ir}");
    }

    #[test]
    fn the_file_modes_are_the_c_strings() {
        let ir = emit(
            "implement main0(argc, argv) = let val f = fileref_open_exn(argv[1], file_mode_w) in fileref_close(f) end",
        )
        .expect("emit");
        assert!(ir.contains(r#"c"w\00""#), "got:\n{ir}");
    }

    #[test]
    fn fprint_writes_to_the_stream_it_is_given() {
        let ir = emit("fun f(out: FILEref): void = fprintln!(out, \"x = \", 1)").expect("emit");
        assert!(ir.contains("call i32 (ptr, ptr, ...) @fprintf(ptr %out"), "got:\n{ir}");
    }

    #[test]
    fn printing_a_fileref_is_an_error() {
        let err = emit_err("fun f(out: FILEref): void = println!(out)");
        assert!(err.message().contains("FILEref") || err.message().contains("file"), "{err}");
    }

    #[test]
    fn fileref_load_scans_into_the_cell_it_is_given() {
        // `fileref_load<int>(f, N)` reads a value *into* `N`, so it needs
        // the cell's address rather than the value inside it.
        let ir = emit(
            "implement main0() = let var n: int val ok = fileref_load<int>(stdin_ref, n) in println!(n) end",
        )
        .expect("emit");
        assert!(ir.contains("call i32 (ptr, ptr, ...) @fscanf(ptr"), "got:\n{ir}");
        assert!(ir.contains("ptr %n.cell"), "the cell's address must be passed:\n{ir}");
    }

    #[test]
    fn fileref_load_reports_whether_it_succeeded() {
        // It yields a bool: `fscanf` returns how many items it converted.
        let ir = emit(
            "implement main0() = let var n: int val ok = fileref_load<int>(stdin_ref, n) in println!(ok) end",
        )
        .expect("emit");
        assert!(ir.contains("icmp eq i32"), "the count must be compared:\n{ir}");
    }

    #[test]
    fn fileref_load_needs_a_var_not_a_val() {
        let err = emit_err(
            "implement main0() = let val n: int = 0 val ok = fileref_load<int>(stdin_ref, n) in println!(n) end",
        );
        assert!(err.message().contains("var"), "{err}");
    }

    // --- datatypes and pattern matching -----------------------------

    const COLOR: &str = "datatype color = Red | Green | Blue ";
    const LIST: &str = "datatype intlist = Nil | Cons(int, intlist) ";

    #[test]
    fn a_nullary_constructor_is_a_tagged_allocation() {
        let ir = emit(&format!("{COLOR} implement main0() = let val c = Red() in println!(1) end")).expect("emit");
        // Each constructor of a datatype gets a distinct tag, stored in
        // the first word of the value.
        assert!(ir.contains("store i64 0, ptr"), "no tag stored in:\n{ir}");
    }

    #[test]
    fn constructors_are_numbered_in_declaration_order() {
        let ir = emit(&format!("{COLOR} implement main0() = let val c = Blue() in println!(1) end")).expect("emit");
        assert!(ir.contains("store i64 2, ptr"), "Blue should carry tag 2:\n{ir}");
    }

    #[test]
    fn a_constructor_with_fields_stores_them_after_the_tag() {
        let ir = emit(&format!("{LIST} implement main0() = let val xs = Cons(7, Nil()) in println!(1) end")).expect("emit");
        assert!(ir.contains("store i64 7, ptr"), "the field must be stored:\n{ir}");
    }

    #[test]
    fn a_case_switches_on_the_tag() {
        let ir = emit(&format!(
            "{COLOR} fun name(c: color): int = case c of | Red() => 0 | Green() => 1 | Blue() => 2 \
             implement main0() = println!(name(Green()))"
        ))
        .expect("emit");
        assert!(ir.contains("load i64, ptr"), "the tag must be read:\n{ir}");
        assert!(ir.contains("icmp eq i64"), "the tag must be tested:\n{ir}");
    }

    #[test]
    fn a_pattern_binds_the_fields_it_names() {
        let ir = emit(&format!(
            "{LIST} fun head(xs: intlist): int = case xs of | Cons(x, r) => x | Nil() => 0 \
             implement main0() = println!(head(Cons(9, Nil())))"
        ))
        .expect("emit");
        assert!(ir.contains("getelementptr"), "fields are reached by address:\n{ir}");
    }

    #[test]
    fn a_variable_pattern_matches_anything() {
        let ir = emit(&format!(
            "{COLOR} fun f(c: color): int = case c of | Red() => 0 | other => 1 \
             implement main0() = println!(f(Blue()))"
        ))
        .expect("emit");
        assert!(ir.contains("define i64 @f(ptr %c)"), "got:\n{ir}");
    }

    #[test]
    fn an_unknown_constructor_is_an_error() {
        let err = emit_err(&format!("{COLOR} fun f(c: color): int = case c of | Purple() => 0"));
        assert!(err.message().contains("Purple"), "{err}");
    }

    #[test]
    fn a_constructor_from_another_datatype_is_an_error() {
        let err = emit_err(&format!(
            "{COLOR} {LIST} fun f(c: color): int = case c of | Nil() => 0 | _ => 1"
        ));
        assert!(err.message().contains("intlist") || err.message().contains("color"), "{err}");
    }

    #[test]
    fn a_constructor_checks_its_argument_count() {
        let err = emit_err(&format!("{LIST} implement main0() = let val xs = Cons(1) in println!(1) end"));
        assert!(err.message().contains("Cons"), "{err}");
    }

    #[test]
    fn case_arms_must_agree_on_a_type() {
        let err = emit_err(&format!(
            "{COLOR} fun f(c: color): int = case c of | Red() => 0 | _ => true"
        ));
        assert!(err.message().contains("type"), "{err}");
    }

    #[test]
    fn allocation_starts_in_a_static_arena() {
        // The common case allocates a few hundred bytes and should not
        // touch the allocator at all: a bump pointer into a static
        // buffer is both faster and impossible to leak.
        let ir = emit(&format!("{COLOR} implement main0() = let val c = Red() in println!(1) end")).expect("emit");
        assert!(ir.contains("@.heap = internal global"), "expected a static arena:\n{ir}");
    }

    #[test]
    fn an_exhausted_arena_grows_and_gives_the_growth_back() {
        // No fixed size is the right one for every program: a lazy
        // stream allocates for as long as it is walked, and the sieve
        // walks a long way.  So the arena grows rather than giving up —
        // and hands every chunk back before `main` returns, which is
        // what keeps "nothing leaks" true rather than merely intended.
        let ir = emit(&format!("{COLOR} implement main0() = let val c = Red() in println!(1) end")).expect("emit");
        assert!(ir.contains("call ptr @malloc"), "the arena cannot grow:\n{ir}");
        assert!(ir.contains("call void @free"), "the growth is never returned:\n{ir}");
    }

    // --- `exit`, and the type of an expression that never returns ---

    #[test]
    fn exit_terminates_the_block() {
        let ir = emit("implement main0() = exit(1)").expect("emit");
        // The status narrows from the subset's i64 to the i32 C wants.
        assert!(ir.contains("trunc i64 1 to i32"), "got:\n{ir}");
        assert!(ir.contains("call void @exit(i32 %"), "got:\n{ir}");
        assert!(ir.contains("unreachable"), "control must not fall through:\n{ir}");
    }

    #[test]
    fn a_branch_that_exits_takes_the_type_of_the_other_one() {
        // `exit` never returns, so it is compatible with any branch it
        // shares an `if` with — the classic bottom type.
        let ir = emit("fun f(n: int): int = if n > 0 then n else exit(1)").expect("emit");
        assert!(ir.contains("define i64 @f(i64 %n)"), "got:\n{ir}");
    }

    #[test]
    fn the_phi_skips_a_branch_that_never_arrives() {
        // A branch ending in `unreachable` is not a predecessor of the
        // merge block, so naming it in the phi would be invalid IR.
        let ir = emit("fun f(n: int): int = if n > 0 then n else exit(1)").expect("emit");
        let phi = ir.lines().find(|l| l.contains("phi")).unwrap_or("");
        assert_eq!(phi.matches('[').count(), 1, "expected one incoming edge, got: {phi}");
    }

    #[test]
    fn a_function_may_end_in_exit_whatever_it_returns() {
        let ir = emit("fun f(): string = exit(2)").expect("emit");
        assert!(ir.contains("define ptr @f()"), "got:\n{ir}");
    }

    #[test]
    fn exit_wants_an_int() {
        let err = emit_err("implement main0() = exit(\"nope\")");
        assert!(err.message().contains("int"), "{err}");
    }

    // --- the two entry points ---------------------------------------

    #[test]
    fn main0_ignores_its_body_and_exits_zero() {
        // `main0` is the "no exit code" entry: whatever it evaluates to
        // is discarded and the process reports success.
        let ir = emit("implement main0() = println!(1)").expect("emit");
        assert!(ir.contains("ret i32 0"), "got:\n{ir}");
    }

    #[test]
    fn main_returns_its_value_as_the_exit_code() {
        // `main` is the "with exit code" entry: its `int` result is the
        // status the process exits with, narrowed to C's `int`.
        let ir = emit("implement main(argc, argv): int = 0").expect("emit");
        assert!(ir.contains("define i32 @main(i32 %argc.raw, ptr %argv)"), "got:\n{ir}");
        assert!(ir.contains("trunc i64 0 to i32"), "the code must narrow to C's int:\n{ir}");
        assert!(!ir.contains("ret i32 0\n}"), "the exit code must not be hardcoded:\n{ir}");
    }

    #[test]
    fn main_must_produce_an_int() {
        let err = emit_err("implement main(argc, argv): int = println!(1)");
        assert!(err.message().contains("exit code"), "{err}");
    }

    #[test]
    fn implementing_without_a_declaration_says_what_is_missing() {
        let err = emit_err("implement something_else() = 1");
        assert!(err.message().contains("extern fun"), "{err}");
    }

    // --- indexed types erase to the type underneath -----------------

    #[test]
    fn an_indexed_int_is_an_int() {
        // `int(n)` is "the int whose value is n".  The index is a fact for
        // the type checker; at runtime it is an ordinary machine integer,
        // so the type erases to its base.
        let ir = emit("fun f(n: int(n)): int(n) = n").expect("emit");
        assert!(ir.contains("define i64 @f(i64 %n)"), "got:\n{ir}");
    }

    #[test]
    fn a_bounded_int_is_an_int() {
        let ir = emit("fun f(n: intGte(0)): intGte(0) = n").expect("emit");
        assert!(ir.contains("define i64 @f(i64 %n)"), "got:\n{ir}");
    }

    #[test]
    fn an_indexed_string_is_a_string() {
        let ir = emit("fun f(s: string(n)): string(n) = s").expect("emit");
        assert!(ir.contains("define ptr @f(ptr %s)"), "got:\n{ir}");
    }

    #[test]
    fn an_application_of_an_unknown_head_is_still_unsupported() {
        // A datatype nobody declared is not an erasable index.
        let err = emit_err("fun f(xs: bag(int, n)): int = 0");
        assert!(err.message().contains("bag"), "{err}");
    }

    // --- the prelude shims -----------------------------------------

    #[test]
    fn g0string2int_becomes_a_call_to_atoi() {
        let ir = emit("implement main0(argc, argv) = println!(g0string2int(argv[1]))").expect("emit");
        assert!(ir.contains("call i64 @atoi(ptr"), "got:\n{ir}");
        assert!(ir.contains("declare i64 @atoi(ptr)"), "atoi must be declared:\n{ir}");
    }

    #[test]
    fn the_int_suffixed_spelling_is_the_same_shim() {
        let ir = emit("implement main0(argc, argv) = println!(g0string2int_int(argv[1]))").expect("emit");
        assert!(ir.contains("call i64 @atoi(ptr"), "got:\n{ir}");
    }

    #[test]
    fn string_length_becomes_a_call_to_strlen() {
        let ir = emit("implement main0() = println!(string_length(\"abc\"))").expect("emit");
        assert!(ir.contains("call i64 @strlen(ptr"), "got:\n{ir}");
    }

    #[test]
    fn the_representation_changing_shims_are_the_identity() {
        // `g1ofg0` moves a value between ATS's two integer *sorts*.  The
        // sorts differ only in what the type checker knows about them, so
        // at the level of machine values the conversion is a no-op.
        let ir = emit("implement main0() = let val n = g1ofg0(41) in println!(n + 1) end").expect("emit");
        assert!(!ir.contains("call i64 @g1ofg0"), "the shim must vanish, not be called:\n{ir}");
        assert!(ir.contains("add i64 41, 1"), "got:\n{ir}");
    }

    #[test]
    fn a_shim_checks_the_type_of_its_argument() {
        let err = emit_err("implement main0() = println!(g0string2int(1))");
        // Not merely "unknown function": the shim exists and refuses the
        // argument it was handed.
        assert!(err.message().contains("expects a ptr argument"), "{err}");
    }

    // --- the command line ------------------------------------------

    #[test]
    fn main_with_arguments_takes_the_c_entry_signature() {
        let ir = emit("implement main0(argc, argv) = println!(argc)").expect("emit");
        assert!(ir.contains("define i32 @main(i32 %argc.raw, ptr %argv)"), "got:\n{ir}");
    }

    #[test]
    fn argc_widens_to_the_subsets_integer_width() {
        // C hands over an `i32`; every `int` here is an `i64`.
        let ir = emit("implement main0(argc, argv) = println!(argc)").expect("emit");
        assert!(ir.contains("%argc = sext i32 %argc.raw to i64"), "got:\n{ir}");
    }

    #[test]
    fn main_without_arguments_still_takes_none() {
        let ir = emit("implement main0() = println!(1)").expect("emit");
        assert!(ir.contains("define i32 @main()"), "got:\n{ir}");
    }

    #[test]
    fn indexing_argv_loads_a_string() {
        let ir = emit("implement main0(argc, argv) = println!(argv[1])").expect("emit");
        assert!(ir.contains("getelementptr ptr, ptr %argv"), "no address computation in:\n{ir}");
        assert!(ir.contains("load ptr, ptr"), "no load in:\n{ir}");
    }

    #[test]
    fn indexing_something_that_is_not_indexable_is_an_error() {
        let err = emit_err("implement main0() = let val x: int = 1 in println!(x[0]) end");
        assert!(err.message().contains("index"), "{err}");
    }

    // --- mutable state: cells, assignment, and the loop forms ------

    #[test]
    fn a_var_binding_allocates_a_cell_and_stores_into_it() {
        // A `val` is an SSA value and needs no storage; a `var` is a cell,
        // so it costs exactly one alloca and one store.
        let ir = emit("implement main0() = let var x: int = 7 in println!(x) end").expect("emit");
        assert!(ir.contains("= alloca i64"), "no alloca in:\n{ir}");
        assert!(ir.contains("store i64 7, ptr %x.cell"), "no initializing store in:\n{ir}");
    }

    #[test]
    fn reading_a_var_is_a_load() {
        let ir = emit("implement main0() = let var x: int = 7 in println!(x) end").expect("emit");
        assert!(ir.contains("load i64, ptr %x.cell"), "no load in:\n{ir}");
    }

    #[test]
    fn a_val_binding_still_allocates_nothing() {
        let ir = emit("implement main0() = let val x: int = 7 in println!(x) end").expect("emit");
        assert!(!ir.contains("alloca"), "a `val` must not allocate:\n{ir}");
    }

    #[test]
    fn an_implement_with_template_parameters_is_a_template_even_undeclared() {
        // No `extern fun{x}` declares it, so nothing but the `{x}` says
        // this is a template — and that has to be enough, or `x` reaches
        // the emitter as if it were a real type.
        let ir = emit(
            "implement{x}\nmyforeach (xs: list0(x)): int = 0\nimplement main0() = println!(1)",
        )
        .expect("emit");
        assert!(!ir.contains("@myforeach"), "an uninstantiated template was emitted:\n{ir}");
    }

    #[test]
    fn raising_names_the_exception_and_leaves() {
        // There is no handler to reach, so the honest lowering of a
        // raise is to say what happened and stop.
        let ir = emit("implement main0() = $raise StreamSubscriptExn").expect("emit");
        assert!(ir.contains("StreamSubscriptExn"), "the name is lost:\n{ir}");
        assert!(ir.contains("call void @exit"), "the program carries on:\n{ir}");
    }

    #[test]
    fn a_raise_can_stand_where_a_value_is_wanted() {
        // A branch that never returns agrees with any type the other
        // branch has, which is what lets a lookup say "or fail".
        let ir = emit(
            "fun get (n: int): int = if n = 0 then 1 else $raise SubscriptExn\n\
             implement main0() = println!(get(0))",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @get(i64 %n)"), "got:\n{ir}");
    }

    #[test]
    fn an_unannotated_lambda_parameter_takes_its_type_from_the_context() {
        // `lam x => x > 0` says nothing about `x`.  The parameter it is
        // being passed as does, and that is the only thing that can.
        let ir = emit(
            "extern fun apply (f: (int) -<cloref1> bool): bool\n\
             implement apply (f) = f(1)\n\
             implement main0() = println!(apply(lam x => x > 0))",
        )
        .expect("emit");
        assert!(ir.contains("i64 %x"), "the parameter is not an int:\n{ir}");
    }

    #[test]
    fn a_tilde_on_a_linear_value_frees_it_rather_than_negating_it() {
        // ATS spells "negate" and "consume this linear value" with the
        // same character, and only the operand's type tells them apart.
        // With an arena there is nothing to free, so the consuming one
        // is a statement that does nothing.
        let ir = emit(
            "implement main0() = let val xs: list0(int) = list0_cons(1, list0_nil()) in (~xs; ()) end",
        )
        .expect("emit");
        assert!(!ir.contains("sub i64 0, "), "a list was negated:\n{ir}");
    }

    #[test]
    fn implementing_a_prelude_template_does_not_hide_its_declaration() {
        // The prelude fills gaps and never shadows — but an `implement`
        // is not a declaration, it is a *body* for one.  Counting it as
        // a declaration took the prelude's away and left the body with
        // nothing to be the body of.
        let ir = emit(
            "implement fprint_val<int> (out, x) = fprint!(out, x)\n\
             implement main0() = fprint_val<int> (stdout_ref, 1)",
        )
        .expect("emit");
        assert!(ir.contains("%ld"), "the instance never printed:\n{ir}");
    }

    #[test]
    fn an_implement_may_supply_one_instance_of_a_template() {
        // `implement show<int> (x) = ...` fills in *that* instance and
        // says nothing about the others.  It is how ATS's printing
        // protocol works: a program supplies `fprint_val` for its own
        // types and the compiler keeps the ones it already knows.
        let ir = emit(
            "extern fun{a:t@ype} show (x: a): void\n\
             implement show<int> (x) = println!(x)\n\
             implement main0() = show<int> (1)",
        )
        .expect("emit");
        assert!(ir.contains("define void @show"), "the instance was not built:\n{ir}");
    }

    #[test]
    fn an_instance_implement_does_not_answer_for_other_instances() {
        let err = emit_err(
            "extern fun{a:t@ype} show (x: a): void\n\
             implement show<int> (x) = println!(x)\n\
             implement main0() = show<bool> (true)",
        );
        assert!(err.message().contains("show"), "{err}");
    }

    #[test]
    fn a_declared_function_with_no_definition_falls_to_the_shim() {
        // `extern fun srand48_with_time (): void = \"ext#\"` says the
        // definition lives outside ATS — in the `%{ ... %}` block this
        // compiler skips, because it emits LLVM IR and never runs a C
        // compiler.  Declaring it must therefore not stop the compiler
        // answering it, or the program links against a symbol nobody
        // ever defined.
        let ir = emit(
            "extern fun srand48_with_time (): void\nimplement main0() = srand48_with_time()",
        )
        .expect("emit");
        assert!(ir.contains("@srand48("), "the shim did not answer:\n{ir}");
        assert!(!ir.contains("call void @srand48_with_time"), "called a symbol nobody defines:\n{ir}");
    }

    #[test]
    fn a_declared_function_with_no_definition_or_shim_is_declared_to_c() {
        // Nothing here knows `my_c_helper`, and `ext#` says it is C's.
        // Emitting a declaration for it is what makes an ATS program
        // able to call out at all.
        let ir = emit(
            "extern fun my_c_helper (x: int): int\nimplement main0() = println!(my_c_helper(1))",
        )
        .expect("emit");
        assert!(ir.contains("declare i64 @my_c_helper(i64)"), "no C declaration:\n{ir}");
    }

    #[test]
    fn a_byte_buffer_is_a_pointer_and_dereferencing_it_changes_nothing() {
        // `b0ytes(n)` is `n` uninitialized bytes, and a pointer to them
        // is all there is at run time.  `!p` *views* those bytes as the
        // buffer rather than loading anything — there is no element type
        // to load.
        let ir = emit(
            "fun take (buf: &b0ytes(8), n: int): int = n\n\
             implement main0() = let val p = malloc_gc(8) in println!(take(!p, 8)) end",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @take(ptr %buf, i64 %n)"), "got:\n{ir}");
    }

    #[test]
    fn a_pointer_compared_against_zero_is_a_null_test() {
        // ATS writes `p > 0` for "the call gave me something".  A
        // pointer is not a number, so the comparison is the null test it
        // means rather than an ordering.
        let ir = emit(
            "implement main0() = let val p = malloc_gc(8) in if p > 0 then println!(1) else println!(0) end",
        )
        .expect("emit");
        assert!(ir.contains("icmp ne ptr"), "not a null test:\n{ir}");
    }

    #[test]
    fn matching_a_value_held_by_reference_names_its_cells() {
        // Taking apart a value you hold *by reference* gives references
        // to its parts: that is what lets the recursion in `intrange`
        // fill in the tail of the cons it just built.  No `@` is written
        // — in ATS the linearity of the value is what says so, and here
        // it is that the scrutinee is a cell.
        let ir = emit(
            "datatype box = Box of (int, box)\n\
             fun fill (b: &box): void = let\n\
               val () = b := Box (1, _)\n\
               val Box (_, rest) = b\n\
             in rest := b end\n\
             implement main0() = let var b: box = Box(1, _) val () = fill(b) in println!(1) end",
        )
        .expect("emit");
        assert!(ir.contains("define void @fill(ptr %b)"), "not by reference:\n{ir}");
    }

    #[test]
    fn a_constructor_field_may_be_left_to_be_filled_in() {
        // `list_vt_cons(m, _)` builds a cons whose tail is not known
        // yet: the recursion writes it through the cell the match hands
        // back.  ATS's linear types are what promise nothing reads the
        // hole first, so the only job here is to leave it well-defined.
        let ir = emit(
            "datatype box = Box of (int, box)\n\
             implement main0() = let val b: box = Box(1, _) in println!(1) end",
        )
        .expect("emit");
        assert!(ir.contains("store ptr null, ptr %t."), "the hole is not defined:\n{ir}");
    }

    #[test]
    fn a_parameter_the_body_assigns_to_is_passed_by_reference() {
        // `r: &int` where the body writes `r := 7` is an *out*
        // parameter: the write has to land in the caller's cell, so the
        // parameter is the address of that cell rather than a copy of
        // what it held.
        let ir = emit(
            "fun setit (r: &int): void = r := 7\n\
             implement main0() = let var x: int = 0 val () = setit(x) in println!(x) end",
        )
        .expect("emit");
        assert!(ir.contains("define void @setit(ptr %r)"), "not by reference:\n{ir}");
        assert!(ir.contains("call void @setit(ptr %x.cell)"), "the cell was not passed:\n{ir}");
    }

    #[test]
    fn a_parameter_only_read_is_still_passed_by_value() {
        // `&` on an aggregate says "the caller's array, not a copy", and
        // an array already *is* its storage.  Nothing is gained by
        // adding a level of indirection, so nothing is added.
        let ir = emit("fun peek (r: &int): int = r + 1\nimplement main0() = println!(peek(1))")
            .expect("emit");
        assert!(ir.contains("define i64 @peek(i64 %r)"), "needless indirection:\n{ir}");
    }

    #[test]
    fn a_by_reference_argument_must_be_something_with_an_address() {
        let err = emit_err(
            "fun setit (r: &int): void = r := 7\nimplement main0() = setit(1)",
        );
        assert!(err.message().contains("var"), "{err}");
    }

    #[test]
    fn an_at_pattern_names_the_cells_of_a_value_not_copies_of_them() {
        // `val-@Box(n) = b` takes `b` apart *in place*: `n` names the
        // field itself, so assigning to it writes into `b`.  That is
        // what lets ATS build a list by filling in its own tail, and it
        // is the whole difference from an ordinary pattern.
        let ir = emit(
            "datatype box = Box of (int)\n\
             implement main0() = let val b = Box(1) val-@Box(n) = b in (n := 2; println!(n)) end",
        )
        .expect("emit");
        assert!(!ir.contains("%n.cell = alloca"), "the field was copied:\n{ir}");
        assert!(ir.contains("store i64 2, ptr %t."), "no write into the value:\n{ir}");
    }

    // --- records --------------------------------------------------

    #[test]
    fn printing_a_list_walks_it_and_separates_with_commas() {
        // ATS prints a list as its elements, comma-separated.  No format
        // string can say that — the length is not known until the list
        // is walked — so the print becomes a loop.
        let ir = emit(
            "implement main0() = let val xs: list0(int) = list0_cons(0, list0_nil()) in println!(\"xs = \", xs) end",
        )
        .expect("emit");
        assert!(ir.contains("print.list"), "no walk over the list:\n{ir}");
        assert!(ir.contains("c\", \\00\""), "no separator:\n{ir}");
    }

    #[test]
    fn a_top_level_val_with_no_name_still_runs() {
        // `val () = println! (...)` is how ATS writes a statement at the
        // top level.  It binds nothing, but it is the whole point of the
        // line, and dropping it loses the program's output.
        let ir = emit("implement main0() = ()\nval () = println!(\"hi\")").expect("emit");
        assert!(ir.contains("@.fmt"), "the statement was dropped:\n{ir}");
    }

    #[test]
    fn compare_yields_the_sign_of_the_difference() {
        // Not `x - y`: that overflows, and ATS promises the *sign*, not
        // the difference.
        let ir = emit("implement main0() = println!(compare(1, 2))").expect("emit");
        assert!(ir.contains("icmp sgt i64"), "no greater-than test:\n{ir}");
        assert!(ir.contains("icmp slt i64"), "no less-than test:\n{ir}");
    }

    #[test]
    fn a_record_allocates_one_slot_per_field() {
        let ir = emit(
            "implement main0() = let val p: '{ x= int, y= int } = '{ x= 1, y= 2 } in println!(1) end",
        )
        .expect("emit");
        assert!(ir.contains("call ptr @.ats_alloc(i64 16)"), "wrong width:\n{ir}");
    }

    #[test]
    fn a_field_is_reached_by_the_slot_its_name_holds() {
        // `.y` is the second field, so it is one slot in — and which
        // slot a name means comes from the record's type, which is the
        // whole difference between a record and a tuple.
        let ir = emit(
            "implement main0() = let val p: '{ x= int, y= int } = '{ x= 1, y= 2 } in println!(p.y) end",
        )
        .expect("emit");
        // Two geps at offset 8 off the record: one to store `y`, one to
        // read it back.
        assert_eq!(
            ir.matches("getelementptr i8, ptr %t.0, i64 8").count(),
            2,
            "wrong slot:\n{ir}"
        );
    }

    #[test]
    fn a_field_a_record_does_not_have_is_an_error() {
        let err = emit_err(
            "implement main0() = let val p: '{ x= int } = '{ x= 1 } in println!(p.z) end",
        );
        assert!(err.message().contains("z"), "{err}");
    }

    #[test]
    fn a_record_field_may_hold_a_function() {
        // The point of a record in ATS is usually a *module*: a bundle of
        // functions passed around as one value.
        let ir = emit(
            "implement main0() = let\n\
               val m: '{ add= (int, int) -> int } = '{ add= lam (x: int, y: int): int => x + y }\n\
             in println!(m.add(1, 2)) end",
        )
        .expect("emit");
        assert!(ir.contains("define i64 @lam.0"), "no lambda:\n{ir}");
    }

    // --- lazy streams ---------------------------------------------

    const ONES: &str = "fun ones(): stream(int) = $delay(stream_cons(1, ones()))\n";

    #[test]
    fn a_global_stream_starts_from_a_null_pointer() {
        // A global's declared initializer is a placeholder — `main`
        // overwrites it before anything runs — but it still has to be a
        // constant of the right type, and a stream is a pointer.
        let ir = emit(&format!(
            "{ONES}val first: stream(int) = ones()\nimplement main0() = ()"
        ))
        .expect("emit");
        assert!(ir.contains("@first = internal global ptr null"), "got:\n{ir}");
    }

    #[test]
    fn a_delayed_stream_is_a_two_word_memo_cell() {
        // One word for the thunk, one for the answer it will produce.
        // The answer slot starts null, which is also what says the
        // stream has not been forced.
        let ir = emit(&format!("{ONES}implement main0() = ()")).expect("emit");
        assert!(ir.contains("store ptr null, ptr"), "no empty answer slot in:\n{ir}");
    }

    #[test]
    fn forcing_a_stream_tests_whether_it_was_forced_before() {
        let ir = emit(&format!(
            "{ONES}implement main0() = let val s = ones() in case+ !s of | stream_cons(x, _) => println!(x) | stream_nil() => () end"
        ))
        .expect("emit");
        assert!(ir.contains("icmp eq ptr"), "no forced-yet test in:\n{ir}");
        assert!(ir.contains("stream.forced"), "no forced path in:\n{ir}");
    }

    #[test]
    fn a_linear_stream_has_the_same_representation_as_a_lazy_one() {
        // `stream_vt` is linear and `stream` is not, which is a
        // difference the type checker cares about and the machine does
        // not: both are a thunk and the answer it caches.
        let plain = emit(&format!("{ONES}implement main0() = ()")).expect("emit");
        let linear = emit(
            "fun ones(): stream_vt(int) = $ldelay(stream_vt_cons(1, ones()))\nimplement main0() = ()",
        )
        .expect("emit");
        assert_eq!(
            plain.matches("store ptr null, ptr").count(),
            linear.matches("store ptr null, ptr").count(),
            "different shapes:\n{plain}\n---\n{linear}"
        );
    }

    #[test]
    fn fprint_tupval_prints_a_tuple_in_ats_notation() {
        let ir = emit(
            "implement main0() = fprint_tupval2<int,char> (stdout_ref, @(0, 'a'))",
        )
        .expect("emit");
        assert!(ir.contains("(%ld, %c)"), "wrong format in:\n{ir}");
    }

    #[test]
    fn fprint_tupval_recurses_into_a_nested_tuple() {
        let ir = emit(
            "implement main0() = fprint_tupval2<int,tup(bool,char)> (stdout_ref, @(0, (true, 'a')))",
        )
        .expect("emit");
        assert!(ir.contains("(%ld, (%s, %c))"), "wrong format in:\n{ir}");
    }

    #[test]
    fn a_template_hole_stays_a_definition_even_with_template_parameters() {
        // `implement{env} f$hole (...)` is filled in by whoever
        // instantiates `f`, so it must not be mistaken for a template
        // waiting to be instantiated on its own.
        let ir = emit(
            "extern fun{a:t@ype} each (n: int): void\n\
             extern fun{a:t@ype} each$work (i: int): void\n\
             implement{a} each (n) = each$work<a> (n)\n\
             implement{a} each$work (i) = println!(i)\n\
             implement main0() = each<int> (3)",
        )
        .expect("emit");
        assert!(ir.contains("define void @each"), "the instance is missing:\n{ir}");
    }

    #[test]
    fn an_uninitialized_var_of_a_datatype_starts_from_null() {
        let ir = emit(
            "implement main0() = let var xs: list0(int) in xs := list0_nil() end",
        )
        .expect("emit");
        assert!(ir.contains("store ptr null, ptr %xs.cell"), "got:\n{ir}");
    }

    #[test]
    fn assignment_stores_into_the_cell() {
        let ir = emit("implement main0() = let var x: int = 1 in x := 9 end").expect("emit");
        assert!(ir.contains("store i64 9, ptr %x.cell"), "no store in:\n{ir}");
    }

    #[test]
    fn assigning_to_an_immutable_binding_is_an_error() {
        let err = emit_err("implement main0() = let val x: int = 1 in x := 9 end");
        assert!(err.message().contains("val"), "{err}");
    }

    #[test]
    fn assigning_an_unknown_name_is_an_error() {
        let err = emit_err("implement main0() = nosuch := 1");
        assert!(err.message().contains("nosuch"), "{err}");
    }

    #[test]
    fn assigning_the_wrong_type_is_an_error() {
        let err = emit_err("implement main0() = let var x: int = 1 in x := true end");
        assert!(err.message().contains("type"), "{err}");
    }

    #[test]
    fn a_while_loop_emits_a_header_body_and_exit() {
        let ir = emit(
            "implement main0() = let var i: int = 0 in while (i < 3) i :=+ 1 end",
        )
        .expect("emit");
        // The condition must live in its own block so it is re-evaluated
        // on every turn — a loop whose test sits in the entry block runs
        // at most once.
        assert!(ir.contains("while.cond."), "no condition block in:\n{ir}");
        assert!(ir.contains("while.body."), "no body block in:\n{ir}");
        assert!(ir.contains("while.end."), "no exit block in:\n{ir}");
        assert!(ir.contains("br label %while.cond."), "the body must jump back:\n{ir}");
    }

    #[test]
    fn a_while_loop_has_type_void() {
        // A loop runs for its effects; it produces nothing.
        let err = emit_err("fun f(): int = let var i: int = 0 in while (i < 3) i :=+ 1 end");
        assert!(err.message().contains("void"), "{err}");
    }

    #[test]
    fn a_for_loop_puts_its_step_in_its_own_block() {
        let ir = emit(
            "implement main0() = let var i: int = 0 in for (i := 0; i < 3; i :=+ 1) println!(i) end",
        )
        .expect("emit");
        assert!(ir.contains("for.cond."), "no condition block in:\n{ir}");
        assert!(ir.contains("for.body."), "no body block in:\n{ir}");
        assert!(ir.contains("for.step."), "no step block in:\n{ir}");
        assert!(ir.contains("for.end."), "no exit block in:\n{ir}");
    }

    #[test]
    fn a_loop_condition_must_be_a_bool() {
        let err = emit_err("implement main0() = let var i: int = 0 in while (i) i :=+ 1 end");
        assert!(err.message().contains("bool"), "{err}");
    }

    // --- unsupported constructs -----------------------------------

    #[test]
    fn unsupported_types_are_errors() {
        let err = emit_err("fun len(xs: list(a)): int = 0");
        assert!(err.message().contains("type"), "{}", err);
    }

    #[test]
    fn a_function_may_be_taken_as_an_argument() {
        // A function type is a closure type, so a parameter may hold one
        // and be applied like any other function.
        let ir = emit("fun apply(f: (int, int) -> int, x: int): int = f(x, x)").expect("emit");
        assert!(ir.contains("define i64 @apply(ptr %f, i64 %x)"), "got:\n{ir}");
        assert!(ir.contains("call i64 %"), "the call must be indirect:\n{ir}");
    }

    #[test]
    fn a_lambda_is_not_an_int() {
        // Lambdas work now, but one is still a closure and not a number.
        let err = emit_err("fun f(): int = lam (x: int) => x");
        assert!(err.message().contains("body has type"), "{}", err);
    }

    #[test]
    fn undefined_variables_are_errors() {
        let err = emit_err("fun f(x: int): int = y");
        assert!(err.message().contains("undefined variable"), "{}", err);
    }

    #[test]
    fn arithmetic_on_bools_is_an_error() {
        let err = emit_err("fun f(a: bool): int = a + 1");
        assert!(err.message().contains("arithmetic"), "{}", err);
    }

    // --- datatypes ------------------------------------------------

    #[test]
    fn a_datatype_declaration_emits_no_code_of_its_own() {
        // A datatype describes a *shape*.  Nothing is emitted for the
        // declaration itself: the code lives in the constructors that
        // build values and the `case`s that take them apart.
        let ir = emit("datatype intlist = Nil | Cons(int, intlist)").expect("emit");
        assert!(ir.contains("; datatype intlist"), "got:\n{ir}");
        assert!(!ir.contains("define"), "got:\n{ir}");
        // With nothing allocating, the arena is not emitted either.
        assert!(!ir.contains("@.heap"), "an unused arena should not appear:\n{ir}");
    }

    // --- end-to-end demo program ----------------------------------

    #[test]
    fn compiles_the_factorial_demo_end_to_end() {
        let src = "\n(* factorial, in the ATS spirit *)\nfun fact(n: int): int = if n = 0 then 1 else n * fact(n - 1)\n\nimplement main0() = println!(\"fact(5) = \", fact(5))\n";
        let ir = emit(src).expect("emit");
        assert!(ir.contains("define i64 @fact(i64 %n)"), "got:\n{ir}");
        assert!(ir.contains("define i32 @main()"), "got:\n{ir}");
        assert!(ir.contains("call i64 @fact(i64 5)"), "got:\n{ir}");
        assert!(ir.contains("call i32 (ptr, ...) @printf"), "got:\n{ir}");
        assert!(ir.contains("fact(5) = %ld"), "got:\n{ir}");
    }
}
