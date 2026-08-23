use super::emitter::global_type_of;
use ats2_domain::ast::*;
use ats2_domain::errors::CompileError;
use ats2_domain::tokens::*;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LlvmType {
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
pub(crate) struct FnSig {
    pub(crate) params: Vec<LlvmType>,
    pub(crate) ret: LlvmType,
}

impl Registry {
    /// The index of a tuple shape, adding it if it is new.
    ///
    /// Shapes are interned so that two tuples with the same components
    /// share a type — `(int, int)` written twice is one type, and code
    /// that returns one can be passed to code that takes the other.
    pub(crate) fn intern_tuple(&self, parts: Vec<LlvmType>) -> usize {
        let mut tuples = self.tuples.borrow_mut();
        if let Some(i) = tuples.iter().position(|t| *t == parts) {
            return i;
        }
        tuples.push(parts);
        tuples.len() - 1
    }

    /// The components of a tuple shape.
    pub(crate) fn tuple_parts(&self, index: usize) -> Vec<LlvmType> {
        self.tuples.borrow()[index].clone()
    }

    /// The index of an array element type, adding it if it is new.
    pub(crate) fn intern_array(&self, elem: LlvmType) -> usize {
        let mut arrays = self.arrays.borrow_mut();
        if let Some(i) = arrays.iter().position(|t| *t == elem) {
            return i;
        }
        arrays.push(elem);
        arrays.len() - 1
    }

    /// What one cell of an array holds.
    pub(crate) fn array_elem(&self, index: usize) -> LlvmType {
        self.arrays.borrow()[index]
    }

    /// The index of a record shape, adding it if it is new.
    pub(crate) fn intern_record(&self, fields: Vec<(String, LlvmType)>) -> usize {
        let mut records = self.records.borrow_mut();
        if let Some(i) = records.iter().position(|r| *r == fields) {
            return i;
        }
        records.push(fields);
        records.len() - 1
    }

    /// A record's fields, in slot order.
    pub(crate) fn record_fields(&self, index: usize) -> Vec<(String, LlvmType)> {
        self.records.borrow()[index].clone()
    }

    /// The index of a forced type, adding it if it is new.
    pub(crate) fn intern_lazy(&self, forced: LlvmType) -> usize {
        let mut lazies = self.lazies.borrow_mut();
        if let Some(i) = lazies.iter().position(|t| *t == forced) {
            return i;
        }
        lazies.push(forced);
        lazies.len() - 1
    }

    /// What forcing a suspended value yields.
    pub(crate) fn lazy_forced(&self, index: usize) -> LlvmType {
        self.lazies.borrow()[index]
    }

    /// The index of a closure signature, adding it if it is new.
    pub(crate) fn intern_closure(&self, sig: FnSig) -> usize {
        let mut closures = self.closures.borrow_mut();
        if let Some(i) = closures
            .iter()
            .position(|c| c.params == sig.params && c.ret == sig.ret)
        {
            return i;
        }
        closures.push(sig);
        closures.len() - 1
    }

    /// The signature behind a closure type.
    pub(crate) fn closure_sig(&self, index: usize) -> FnSig {
        self.closures.borrow()[index].clone()
    }
}

/// Everything an expression needs to know about the rest of the program:
/// the signature of every function (so recursion and mutual recursion
/// resolve regardless of order), and the value of every `#define`
/// constant (which is substituted, not stored).
#[derive(Debug, Default)]
pub(crate) struct Registry {
    pub(crate) fns: HashMap<String, FnSig>,
    pub(crate) consts: HashMap<String, Expr>,
    /// Declared datatypes, in declaration order; `LlvmType::Data` indexes
    /// into this.
    pub(crate) datatypes: Vec<String>,
    /// Top-level `val`s: name → the type of the global holding it.
    ///
    /// Their *values* are not known here — a global's initializer may be
    /// any expression — so each is a piece of storage written once, before
    /// `main` runs.
    pub(crate) globals: HashMap<String, LlvmType>,
    /// Operators the program has given a function to fall back on.
    pub(crate) overloads: HashMap<String, String>,
    /// The distinct closure signatures the program uses.
    pub(crate) closures: std::cell::RefCell<Vec<FnSig>>,
    /// The distinct tuple shapes the program uses.
    pub(crate) tuples: std::cell::RefCell<Vec<Vec<LlvmType>>>,
    /// The distinct array element types the program uses.
    pub(crate) arrays: std::cell::RefCell<Vec<LlvmType>>,
    /// The distinct types a suspended value can produce once forced.
    pub(crate) lazies: std::cell::RefCell<Vec<LlvmType>>,
    /// The distinct record shapes the program uses: for each, the fields
    /// in slot order.
    pub(crate) records: std::cell::RefCell<Vec<Vec<(String, LlvmType)>>>,
    /// Every constructor of every datatype, by name.
    ///
    /// A name may belong to several: two instances of one parameterized
    /// datatype declare the same constructors, so `None` can build an
    /// `opt$int` or an `opt$string`.  Which one is meant depends on the
    /// types around it, so all the candidates are kept and the choice is
    /// made at the use site.
    pub(crate) ctors: HashMap<String, Vec<CtorInfo>>,
    /// The functions this program actually defines, as opposed to merely
    /// declaring.
    ///
    /// An `extern fun ... = "ext#"` says the definition lives outside
    /// ATS — often in the `%{ ... %}` block of C this compiler skips.
    /// Declaring it must not stop the compiler answering it with a shim,
    /// and when nothing answers it, a C declaration is what lets the
    /// program call out at all.  Either way, a declaration alone is not
    /// a definition to call.
    pub(crate) defined: std::collections::HashSet<String>,
    /// Which of a function's parameters it writes back through.
    ///
    /// `r: &int` where the body says `r := 7` is an *out* parameter: the
    /// write must land in the caller's cell, so the parameter is that
    /// cell's address.  A `&` the body only reads needs no indirection —
    /// and an aggregate is its own storage, so writes *into* one land
    /// without any of this.  Assignment to the parameter is therefore
    /// the thing that decides, and it is decided from the body rather
    /// than from the annotation, which cannot be trusted to be there.
    pub(crate) by_ref: HashMap<String, Vec<bool>>,
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
    pub(crate) holes: HashMap<String, ats2_domain::ast::ImplementDef>,
}

/// What the emitter needs to know about one constructor.
#[derive(Debug, Clone)]
pub(crate) struct CtorInfo {
    /// Which datatype it builds (an index into `Registry::datatypes`).
    pub(crate) datatype: usize,
    /// Its tag: the position it was declared in.
    pub(crate) tag: i64,
    /// The types of its fields, in order.
    pub(crate) fields: Vec<LlvmType>,
    /// The widest constructor of the same datatype.
    ///
    /// Every value reserves that much, so reading field `i` of *any*
    /// constructor lands inside the value.  That is what makes a nested
    /// pattern safe to lay out as a sequence of loads and tests: the load
    /// happens before the tag is known to match, and it must not run off
    /// the end of a narrower record.
    pub(crate) width: usize,
}

/// Where a print macro sends its bytes.
///
/// The two standard destinations are named rather than computed, because
/// `printf` needs no stream operand at all and that is the common case.
/// `Ref` covers a stream the program worked out for itself — the `out` a
/// function was handed, a file it opened.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Stream {
    Stdout,
    Stderr,
    Ref(String),
}

/// An SSA value produced by an expression: its register text and its type.
#[derive(Debug, Clone)]
pub(crate) struct FnValue {
    pub(crate) reg: String,
    pub(crate) ty: LlvmType,
}

/// Collects every function's signature up front, so recursive and
/// mutually-recursive calls resolve regardless of definition order.
pub(crate) fn registry_of(program: &Program) -> Result<Registry, CompileError> {
    let mut registry = Registry::default();
    // Datatypes come first: a function's signature may mention one, and a
    // datatype may mention itself (a list holds a list), so every name
    // must be known before any field type is resolved.
    for def in &program.defs {
        if let Def::Datatype(d) = def {
            if registry.datatypes.contains(&d.name) {
                return Err(CompileError::emit(format!(
                    "datatype `{}` is declared twice",
                    d.name
                )));
            }
            registry.datatypes.push(d.name.clone());
        }
    }
    for def in &program.defs {
        if let Def::Datatype(d) = def {
            let index = registry
                .datatypes
                .iter()
                .position(|n| n == &d.name)
                .expect("just added");
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
                candidates.push(CtorInfo {
                    datatype: index,
                    tag: tag as i64,
                    fields,
                    width: 0,
                });
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

    // Exceptions: each `exception X of (t1, t2)` is a constructor of a
    // shared `exn` datatype.  Collecting them here gives every raise a
    // box to build and every `try` a tag to dispatch on.
    let exn_ctor: Vec<(String, Vec<LlvmType>)> = program
        .defs
        .iter()
        .filter_map(|d| match d {
            Def::Exception(name, payload) => payload
                .iter()
                .map(|t| llvm_type_in(t, &registry))
                .collect::<Result<Vec<_>, _>>()
                .ok()
                .map(|fields| (name.clone(), fields)),
            _ => None,
        })
        .collect();
    if !exn_ctor.is_empty() {
        let exn_index = registry.datatypes.len();
        registry.datatypes.push("exn".to_string());
        let width = exn_ctor.iter().map(|(_, f)| f.len()).max().unwrap_or(0);
        for (tag, (name, fields)) in exn_ctor.into_iter().enumerate() {
            registry
                .ctors
                .entry(name.clone())
                .or_default()
                .push(CtorInfo {
                    datatype: exn_index,
                    tag: tag as i64,
                    fields,
                    width,
                });
        }
    }
    for def in &program.defs {
        match def {
            // Not this compiler's language; the toolchain reads it.
            Def::InlineC(_) => {}
            Def::Exception(_, payload) => {
                for t in payload {
                    llvm_type_in(t, &registry)?;
                }
            }
            Def::Fun(f) => {
                let params = f
                    .params
                    .iter()
                    .map(|p| llvm_type_in(&p.ty, &registry))
                    .collect::<Result<Vec<_>, _>>()?;
                // `fun f (m: int) = lam (n: int): int => ...` writes no
                // return type.  The lambda's own annotations give it, and
                // they must be read *before* the body is emitted, because
                // the body may call `f` again.
                let declared = match (&f.ret, &f.body) {
                    (Ty::Name(n), Expr::Lam(ps, Some(r), _)) if n == "_" => Ty::Fun(
                        ps.iter().map(|p| p.ty.clone()).collect(),
                        Box::new(r.clone()),
                    ),
                    (other, _) => other.clone(),
                };
                let ret = llvm_type_in(&declared, &registry)?;
                registry
                    .by_ref
                    .insert(f.name.clone(), assigned_parameters(&f.params, &f.body));
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
                let sig = match registry.fns.get(&im.name).cloned() {
                    Some(sig) => {
                        if sig.params.len() != im.params.len() {
                            return Err(CompileError::emit(format!(
                                "`{}` is declared with {} parameter(s) but implemented with {}",
                                im.name,
                                sig.params.len(),
                                im.params.len()
                            )));
                        }
                        sig
                    }
                    None => {
                        let is_ambient = im.name.starts_with("atsruntime_")
                            || im.name.starts_with("patsolve_")
                            || im.name.starts_with("myhashtbl_")
                            || im.name.starts_with("node_")
                            || im.name.starts_with("the_")
                            || im.name.starts_with("EStream_")
                            || im.name.starts_with("int_")
                            || im.name.starts_with("draw_")
                            || im.name.starts_with("fprint_")
                            || im.name.starts_with("gcompare_")
                            || im.name.starts_with("emit_")
                            || im.name.starts_with("prerr_")
                            || im.ret.is_some()
                            || im.params.iter().any(|p| !matches!(&p.ty, Ty::Name(n) if n == "_" || n.is_empty()));
                        if is_ambient {
                            let mut params = Vec::with_capacity(im.params.len());
                            for p in &im.params {
                                params.push(llvm_type_in(&p.ty, &registry)?);
                            }
                            let ret = match &im.ret {
                                Some(t) => llvm_type_in(t, &registry)?,
                                None => LlvmType::Void,
                            };
                            let sig = FnSig { params, ret };
                            registry.fns.insert(im.name.clone(), sig.clone());
                            sig
                        } else {
                            return Err(CompileError::emit(format!(
                                "`{}` is implemented but never declared; add an `extern fun` for it",
                                im.name
                            )));
                        }
                    }
                };
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
                    _ => {
                        return Err(CompileError::emit(
                            "main0 takes either no parameters or `(argc, argv)`",
                        ));
                    }
                };
                registry.fns.insert(
                    im.name.clone(),
                    FnSig {
                        params,
                        ret: LlvmType::I32,
                    },
                );
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
                let params = d
                    .params
                    .iter()
                    .map(|p| llvm_type_in(&p.ty, &registry))
                    .collect::<Result<Vec<_>, _>>()?;
                let ret = llvm_type_in(&d.ret, &registry)?;
                registry.fns.insert(d.name.clone(), FnSig { params, ret });
            }
            Def::Datatype(_) => {}
        }
    }
    Ok(registry)
}

/// As `llvm_type_of`, but also resolving the datatypes declared here.
/// The primitive an ATS refinement family refines.
///
/// `intGte(0)` is an `int` that is known to be at least nought; the
/// knowledge is the checker's business and the machine word is the
/// emitter's.  This is where the knowledge is dropped.
pub(crate) fn refined_primitive(name: &str) -> Option<&'static str> {
    if let Some(base) = crate::prelude::canonical_scalar_type(name) {
        // Canonicalization is idempotent: only an alias needs another
        // lowering pass. Re-entering for `double -> double` never terminates.
        return (base != name).then_some(base);
    }
    Some(match name {
        "intGt" | "intGte" | "intLt" | "intLte" | "intBtw" | "intBtwe" | "nat" | "natLt"
        | "natLte" | "natGt" | "natGte" | "uintGt" | "uintGte" | "uintLt" | "uintLte"
        | "sizeGt" | "sizeGte" | "sizeLt" | "sizeLte" | "sizeBtw" | "sizeBtwe" | "size_t"
        | "ssize_t" | "uint" | "pos" | "Nat" | "Pos" => "int",
        _ => return None,
    })
}

pub(crate) fn llvm_type_in(ty: &Ty, registry: &Registry) -> Result<LlvmType, CompileError> {
    if let Ty::Name(n) = ty {
        if let Some(primitive) = refined_primitive(n) {
            return llvm_type_in(&Ty::Name(primitive.into()), registry);
        }
        // `a`, `b`, ... — an *unconstrained type parameter*, which ATS
        // boxes: its value is whatever the caller substituted, reached
        // through a pointer.  `_` — a type the source declined to name.
        // Both are a pointer, and letting one reach the "only int, bool,
        // string" wall would stop a program whose data is merely generic.
        if is_type_variable(n) || n == "_" {
            return Ok(LlvmType::I8Ptr);
        }
    }
    // `(int) -> int` is a function *value*, which in this subset means a
    // closure: nothing else can produce one.
    if let Ty::Fun(params, ret) = ty {
        let params = params
            .iter()
            .map(|p| llvm_type_in(p, registry))
            .collect::<Result<Vec<_>, _>>()?;
        let ret = llvm_type_in(ret, registry)?;
        return Ok(LlvmType::Closure(
            registry.intern_closure(FnSig { params, ret }),
        ));
    }
    if let Ty::Record(fields) = ty {
        let parts = fields
            .iter()
            .map(|(n, t)| Ok((n.clone(), llvm_type_in(t, registry)?)))
            .collect::<Result<Vec<_>, CompileError>>()?;
        return Ok(LlvmType::Record(registry.intern_record(parts)));
    }
    if let Ty::Tuple(items) = ty {
        let parts = items
            .iter()
            .map(|i| llvm_type_in(i, registry))
            .collect::<Result<Vec<_>, _>>()?;
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
pub(crate) fn llvm_type_of(ty: &Ty) -> Result<LlvmType, CompileError> {
    match ty {
        // `(pf | v)` occupies exactly what `v` occupies: a proof is not
        // a value and has no representation to ask about.
        Ty::Proof(_, value) => llvm_type_of(value),
        // An index is a fact *about* a value, never a part of one, so
        // emission looks straight through it.  This is what ATS itself
        // does: the static language is gone before any code is emitted.
        Ty::Index(base, _) => llvm_type_of(base),
        // `int(n)`, `intGte(0)`, `string(n)` — an *indexed* type.  The
        // index is a static fact (this int equals n, that one is at least
        // zero); it describes no part of the machine value, so the type
        // erases to the base it decorates.  This is what ATS itself does:
        // the static language is gone by the time code is emitted.
        Ty::App(head, _) => Ok(base_type_named(head).unwrap_or(LlvmType::I8Ptr)),
        // `argv` is C's `char **`.  Under opaque pointers every pointer is
        // spelled `ptr`, so it shares a representation with `string` and
        // is told apart only by how it may be used.
        //
        // An unknown name is an *opaque* type: a record from a signature
        // file this compilation did not load, an abstraction whose body
        // no one may see, a `$rec` the source only ever passes around.
        // Whatever its shape, nothing here may take it apart, so a
        // pointer is what it is — the same box the established rule
        // gives a type variable or an unnamed type.
        Ty::Name(n) => Ok(base_type_named(n).unwrap_or(LlvmType::I8Ptr)),
        Ty::Fun(_, _) => Err(CompileError::emit(
            "higher-order function types are not supported yet",
        )),
        Ty::Tuple(_) => Err(CompileError::emit("tuple types are not supported yet")),
        Ty::Record(_) => Err(CompileError::emit(
            "internal: a record type reached the fallback mapper",
        )),
    }
}

/// How an operator is written, for looking it up among the overloads.
pub(crate) fn operator_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "mod",
        BinOp::Eq => "=",
        BinOp::Ne => "<>",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::Andalso => "andalso",
        BinOp::Orelse => "orelse",
    }
}

/// Whether a pattern always matches, so that no later arm can be reached.
pub(crate) fn is_irrefutable(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Wildcard | Pattern::Var(_) => true,
        Pattern::Tuple(items) => items.iter().all(is_irrefutable),
        _ => false,
    }
}

/// Which of these parameters the body assigns to.
pub(crate) fn assigned_parameters(params: &[Param], body: &Expr) -> Vec<bool> {
    let mut written = std::collections::HashSet::new();
    collect_assigned(body, &mut written);
    params.iter().map(|p| written.contains(&p.name)).collect()
}

/// Every name assigned to anywhere in an expression.
pub(crate) fn collect_assigned(expr: &Expr, out: &mut std::collections::HashSet<String>) {
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
pub(crate) fn resolve_ctor(
    name: &str,
    ty_args: &[Ty],
    expected: Option<LlvmType>,
    registry: &Registry,
) -> Result<CtorInfo, CompileError> {
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
            candidates
                .iter()
                .find(|c| registry.datatypes[c.datatype] == w)
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
    let names: Vec<&str> = candidates
        .iter()
        .map(|c| registry.datatypes[c.datatype].as_str())
        .collect();
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
pub(crate) fn instance_name(candidates: &[CtorInfo], ty_args: &[Ty], registry: &Registry) -> Option<String> {
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
pub(crate) fn ty_for(t: LlvmType) -> Ty {
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
            LlvmType::Data(_)
            | LlvmType::Tuple(_)
            | LlvmType::Array(_)
            | LlvmType::Closure(_)
            | LlvmType::Lazy(_)
            | LlvmType::Record(_) => "void",
        }
        .into(),
    )
}

/// The libc global behind an ATS standard-stream name.
pub(crate) fn standard_stream(name: &str) -> Option<&'static str> {
    match name {
        "stdin_ref" => Some("stdin"),
        "stdout_ref" => Some("stdout"),
        "stderr_ref" => Some("stderr"),
        _ => None,
    }
}

/// The C mode string an ATS file-mode name stands for.
pub(crate) fn file_mode(name: &str) -> Option<&'static str> {
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
/// Whether `name` is a bare type variable — the single lowercase letter
/// ATS conventionally uses for an unconstrained type parameter.  Such a
/// value is boxed, so it lowers to a pointer.
pub(crate) fn is_type_variable(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(
        (chars.next(), chars.next()),
        (Some(c), None) if c.is_ascii_lowercase()
    )
}

pub(crate) fn base_type_named(name: &str) -> Option<LlvmType> {
    match name {
        // Every integer ATS distinguishes — by width, by signedness, by
        // which static sort tracks it — is one machine word here.  The
        // distinctions are real to its type checker and invisible to a
        // 64-bit target.
        "int" | "intGt" | "intGte" | "intLt" | "intLte" | "nat" | "pos" | "size_t" | "sizeGt"
        | "sizeGte" | "sizeLt" | "sizeLte" | "ssize_t" | "uint" | "lint" | "ulint" | "llint"
        | "ullint" | "sint" | "usint" | "Int" | "Nat" | "Uint" | "intmax" | "uintmax" => {
            Some(LlvmType::I64)
        }
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

/// The program with its proof declarations removed.
///
/// Everything the static language declares is invisible from here on: it
/// has already been read by the checker, which is the only stage that
/// could do anything with it.
pub(crate) fn without_proofs(program: &Program) -> Program {
    Program::new(
        program
            .defs()
            .iter()
            // A `praxi` is a declaration; a `prfun` is a definition with
            // a derivation for a body.  Both are proofs, and neither is
            // code — dropping only the declaration left the derivation
            // to be emitted as a function whose body builds a value of a
            // type no machine has.
            .filter(|d| !matches!(d, Def::Extern(decl) if decl.proof))
            .filter(|d| !matches!(d, Def::Fun(f) if f.proof))
            .cloned()
            .collect(),
    )
}

/// An expression with any static instantiation stripped away.
///
/// `ax{n}(...)` names which claim was made, and by emission time no
/// claim is being made any more.  Every place that asks "what is being
/// called here" wants the answer underneath.
pub(crate) fn peel_static(e: &Expr) -> &Expr {
    match e {
        Expr::StaticInst(inner, _) => peel_static(inner),
        _ => e,
    }
}

pub(crate) fn llvm_ty_str(t: LlvmType) -> &'static str {
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
pub(crate) fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' || c == '$' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

/// Escape a decoded string for an LLVM `c"..."` constant body: printable
/// ASCII passes through, everything else becomes `\HH` hex escapes.
pub(crate) fn llvm_escape(s: &str) -> String {
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
pub(crate) const HEAP_BYTES: usize = 1 << 20;

/// How much a chunk holds once the static arena is full, in bytes.
///
/// Large enough that a program walking a long stream asks the allocator
/// for memory a few dozen times rather than a few million.
pub(crate) const HEAP_CHUNK_BYTES: usize = 1 << 23;

/// The bytes at the head of a malloc'd chunk, reserved for the link that
/// threads it onto the list of chunks to free.  A whole slot rather than
/// a word, so the data after it stays slot-aligned.
pub(crate) const HEAP_CHUNK_HEADER: usize = WORD * 2;

/// The two runtime routines the arena needs, as LLVM IR.
///
/// They are functions rather than inline code because allocation happens
/// at every constructor, and a dozen instructions repeated at each of
/// them would swamp the IR that says what the program actually does.
pub(crate) fn heap_runtime() -> String {
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

/// The exception runtime: a stack of setjmp frames and a cell where a
/// raised value waits to be caught.  A raise longjmps to the nearest
/// enclosing `try`; a `try` began by saving its frame.  Because the
/// program never returns from a raise, the frames are a linked list
/// threaded through the arena rather than freed — the same bargain the
/// heap runtime makes.

/// The width of one slot in a datatype value.  Every field occupies one,
/// whatever its type, so field `i` sits at the same offset regardless of
/// which constructor built the value.
pub(crate) const WORD: usize = 8;
