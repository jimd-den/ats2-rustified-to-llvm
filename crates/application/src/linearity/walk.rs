//! # Where a resource changes hands
//!
//! *Literate note.*  [`super::resources`] keeps the ledger; this module
//! decides what goes in it.  The whole question is: at which points in a
//! program does a linear value stop being one body's and start being
//! another's?  There turn out to be few of them, and they are all
//! *positions* rather than expressions — an argument in a non-borrowed
//! parameter, a value a `let` moves to a new name, the thing a body ends
//! with.
//!
//! Two decisions keep it honest.
//!
//! **Only a declaration makes a value linear.**  Nothing about the bits
//! says which kind a value is, and guessing from a name — everything
//! ending in `_vt`, say — would police values the program never said
//! were resources.
//!
//! **A callee nobody declared may have taken it.**  When the walk meets a
//! call it cannot look up, it stops claiming to know what a body still
//! holds, and reports no leaks for that body.  Use-after-handover
//! survives, because that one is about what *did* happen rather than
//! what did not.  A checker that reported leaks it could not have known
//! about would be reporting its own ignorance.

use std::collections::HashSet;

use ats2_domain::ast::{Def, Expr, FunDef, LetBind, Param, Pattern, Program, Ty};

use crate::checking::signatures::{strip_index, SigTable};

use super::resources::{Resources, Use};

/// A resource discipline the program did not keep.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fault {
    /// Reached for after it had been handed over.
    UsedAgain { function: String, name: String },
    /// Still held when the body ended.
    Leaked { function: String, name: String },
    /// One branch gave it away and another did not.
    BranchesDisagree { function: String, name: String },
}

impl Fault {
    /// The sentence a diagnostic prints.
    pub fn describe(&self) -> String {
        match self {
            Fault::UsedAgain { function, name } => format!(
                "in `{function}`, `{name}` is used after it has already been given away"
            ),
            Fault::Leaked { function, name } => {
                format!("in `{function}`, `{name}` is never given away")
            }
            Fault::BranchesDisagree { function, name } => format!(
                "in `{function}`, one branch gives `{name}` away and another keeps it, \
                 so what is held afterwards depends on which way it went"
            ),
        }
    }
}

/// Every resource fault a program contains.
pub fn faults(program: &Program, ambient: &Program) -> Vec<Fault> {
    let mut sigs = SigTable::of(ambient);
    sigs.extend(SigTable::of(program));
    let linear = linear_types(ambient, program);
    let ctors = linear_ctors(ambient, program);
    let mut walk =
        Walk { sigs: &sigs, linear: &linear, ctors: &ctors, out: Vec::new(), function: String::new(), certain: true };
    for def in program.defs() {
        match def {
            Def::Fun(f) => walk.function_def(f),
            Def::Implement(im) => {
                walk.body(&im.name, &im.params, &im.body);
            }
            _ => {}
        }
    }
    walk.out
}

/// The type names whose values are resources.
///
/// Only a declaration says so.  A `datavtype` declares them directly; a
/// `dataview`'s constructors declare that what they build is one.
fn linear_types(ambient: &Program, program: &Program) -> HashSet<String> {
    let mut out = HashSet::new();
    for def in ambient.defs().iter().chain(program.defs()) {
        match def {
            Def::Datatype(d) if d.linear => {
                out.insert(d.name.clone());
            }
            Def::Extern(d) if d.linear => {
                if let Some(name) = type_name(&d.ret) {
                    out.insert(name);
                }
            }
            _ => {}
        }
    }
    out
}

/// The constructors that *build* a resource.
///
/// A function that returns one says so in a signature, and the walk can
/// look that up.  A constructor has no signature to look up — the
/// `datavtype` declaration is the only place that says `mk_vt` hands
/// back something owed, so that is where the walk has to read it.
fn linear_ctors(ambient: &Program, program: &Program) -> HashSet<String> {
    let mut out = HashSet::new();
    for def in ambient.defs().iter().chain(program.defs()) {
        if let Def::Datatype(d) = def {
            if d.linear {
                out.extend(d.ctors.iter().map(|c| c.name.clone()));
            }
        }
    }
    out
}

/// The name at the head of a type, past anything that only decorates it.
fn type_name(ty: &Ty) -> Option<String> {
    match strip_index(ty) {
        Ty::Name(n) => Some(n.clone()),
        Ty::App(n, _) => Some(n.clone()),
        Ty::Proof(_, value) => type_name(value),
        _ => None,
    }
}

struct Walk<'a> {
    sigs: &'a SigTable,
    linear: &'a HashSet<String>,
    /// The constructors of those types, which have no signature to consult.
    ctors: &'a HashSet<String>,
    out: Vec<Fault>,
    function: String,
    /// Whether the walk still knows what this body holds.
    ///
    /// A call it could not look up may have taken anything handed to it,
    /// so past one of those a leak report would be reporting the walk's
    /// own ignorance rather than the program's mistake.
    certain: bool,
}

impl<'a> Walk<'a> {
    fn is_linear(&self, ty: &Ty) -> bool {
        type_name(ty).is_some_and(|n| self.linear.contains(&n))
    }

    fn function_def(&mut self, f: &FunDef) {
        self.body(&f.name, &f.params, &f.body);
    }

    /// One body, from the resources it is handed to the ones it owes.
    fn body(&mut self, name: &str, params: &[Param], body: &Expr) {
        let outer = std::mem::replace(&mut self.function, name.to_string());
        let was_certain = std::mem::replace(&mut self.certain, true);
        let mut held = Resources::default();
        for p in params {
            // A borrowed parameter is lent: the caller keeps it, and the
            // body must neither free it nor answer for it at the end.
            if self.is_linear(&p.ty) && !p.borrowed {
                held.acquire(&p.name);
            }
        }
        self.expr(body, &mut held);
        // What the body ends with, it hands back to its caller.
        self.consume_result(body, &mut held);
        if self.certain {
            for leaked in held.leaked() {
                self.out.push(Fault::Leaked {
                    function: self.function.clone(),
                    name: leaked,
                });
            }
        }
        self.function = outer;
        self.certain = was_certain;
    }

    /// The value a body ends with is given to whoever called it.
    fn consume_result(&mut self, body: &Expr, held: &mut Resources) {
        match body {
            Expr::Var(name) => {
                self.record(held.consume(name), name);
            }
            Expr::Let(_, rest) | Expr::LetFun(_, rest) => self.consume_result(rest, held),
            Expr::Ascribe(inner, _) | Expr::ProofPair(_, inner) => {
                self.consume_result(inner, held)
            }
            _ => {}
        }
    }

    fn record(&mut self, outcome: Use, name: &str) {
        if outcome == Use::Again {
            self.out.push(Fault::UsedAgain {
                function: self.function.clone(),
                name: name.to_string(),
            });
        }
    }

    fn expr(&mut self, e: &Expr, held: &mut Resources) {
        match e {
            Expr::Call(callee, args) => self.call(callee, args, held),
            Expr::IfThenElse(cond, t, f) => {
                self.expr(cond, held);
                let mut taken = held.clone();
                let mut untaken = held.clone();
                self.expr(t, &mut taken);
                self.consume_result(t, &mut taken);
                self.expr(f, &mut untaken);
                self.consume_result(f, &mut untaken);
                self.join(&taken, &untaken, held);
            }
            Expr::Case(scrutinee, arms) => {
                self.expr(scrutinee, held);
                let mut settled: Option<Resources> = None;
                for (pattern, arm) in arms {
                    let mut path = held.clone();
                    self.take_apart(pattern, scrutinee, &mut path);
                    self.expr(arm, &mut path);
                    self.consume_result(arm, &mut path);
                    settled = Some(match settled {
                        None => path,
                        Some(first) => {
                            self.join(&first, &path, held);
                            first
                        }
                    });
                }
                if let Some(path) = settled {
                    *held = path;
                }
            }
            Expr::Let(binds, rest) => {
                for b in binds {
                    self.let_bind(b, held);
                }
                self.expr(rest, held);
            }
            Expr::LetFun(funs, rest) => {
                // A nested function answers for its own resources.
                for f in funs {
                    self.function_def(f);
                }
                self.expr(rest, held);
            }
            other => other.each_subexpr(&mut |sub| self.expr(sub, held)),
        }
    }

    /// Two paths, reconciled — or reported as irreconcilable.
    fn join(&mut self, taken: &Resources, untaken: &Resources, held: &mut Resources) {
        match taken.disagreement(untaken) {
            Some(name) => {
                self.out.push(Fault::BranchesDisagree {
                    function: self.function.clone(),
                    name,
                });
                // What is held past here really does depend on which way
                // it went, so the walk stops claiming to know.  One
                // mistake earns one complaint: reporting the leak that
                // follows from it would be describing the same fault
                // twice, and sending the reader after a second one that
                // is not there.
                self.certain = false;
            }
            None => *held = taken.clone(),
        }
    }

    /// `case xs of ~cons (x, rest)` — taking a resource apart consumes
    /// it, and hands back whatever its fields were.
    fn take_apart(&mut self, pattern: &Pattern, scrutinee: &Expr, held: &mut Resources) {
        if !matches!(pattern, Pattern::Ctor(_, _) | Pattern::InPlace(_)) {
            return;
        }
        if let Expr::Var(name) = scrutinee {
            if held.is_held(name) {
                self.record(held.consume(name), name);
            }
        }
    }

    fn let_bind(&mut self, b: &LetBind, held: &mut Resources) {
        // What the right-hand side does, it does first.
        self.expr(&b.value, held);
        let Some(name) = &b.name else {
            // A discard binding still has to answer for its value.
            self.consume_result(&b.value, held);
            return;
        };
        match &b.value {
            // `val ys = xs` — the resource moves to the new name, and
            // the old one is not the body's any more.
            Expr::Var(from) if held.is_held(from) => {
                self.record(held.consume(from), from);
                held.acquire(name);
            }
            // A call that returns a resource hands one over.
            value => {
                if self.returns_a_resource(value) {
                    held.acquire(name);
                } else {
                    self.consume_result(value, held);
                }
            }
        }
    }

    /// Whether an expression produces a resource of its own.
    fn returns_a_resource(&self, e: &Expr) -> bool {
        let named = match e {
            Expr::Call(callee, _) => callee_name(callee),
            // A constructor that takes no fields is not written as a
            // call, and builds a resource all the same.
            Expr::Var(_) | Expr::Inst(_, _) => callee_name(e),
            _ => return false,
        };
        let Some(name) = named else { return false };
        if self.ctors.contains(&name) {
            return true;
        }
        matches!(e, Expr::Call(_, _))
            && self.sigs.get(&name).is_some_and(|sig| self.is_linear(&sig.ret))
    }

    /// A call: each argument changes hands, or does not, by what the
    /// callee said it wanted.
    fn call(&mut self, callee: &Expr, args: &[Expr], held: &mut Resources) {
        for arg in args {
            self.expr(arg, held);
        }
        let named = callee_name(callee);
        if let Some(name) = &named {
            // A constructor has no signature, but it is not unknown: it
            // takes its fields, and whatever resource goes into one is
            // the structure's from here on.
            if self.ctors.contains(name) && self.sigs.get(name).is_none() {
                for arg in args {
                    if let Expr::Var(n) = arg {
                        if held.is_held(n) {
                            self.record(held.consume(n), n);
                        }
                    }
                }
                return;
            }
        }
        let declared = named.and_then(|n| self.sigs.get(&n));
        let Some(sig) = declared else {
            // Nobody declared it, so nobody knows what it took.  Every
            // argument is left alone and this body stops claiming to
            // know what it still holds.
            if args.iter().any(|a| matches!(a, Expr::Var(n) if held.is_held(n))) {
                self.certain = false;
            }
            return;
        };
        let wants = sig.borrowed.clone();
        for (i, arg) in args.iter().enumerate() {
            let Expr::Var(name) = arg else { continue };
            let outcome = match wants.get(i) {
                // `!xs` — lent, so it stays where it was.
                Some(true) => held.borrow(name),
                _ => held.consume(name),
            };
            self.record(outcome, name);
        }
    }
}

/// The name a call is calling, past the decorations that do not change it.
fn callee_name(callee: &Expr) -> Option<String> {
    match callee {
        Expr::Var(name) => Some(name.clone()),
        Expr::Inst(name, _) => Some(name.clone()),
        Expr::StaticInst(inner, _) => callee_name(inner),
        _ => None,
    }
}
