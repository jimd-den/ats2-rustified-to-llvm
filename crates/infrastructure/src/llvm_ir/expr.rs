use super::emitter::zero_literal;
use super::builder::*;
use super::emitter::LlvmIrEmitter;
use super::types::*;
use ats2_domain::ast::*;
use ats2_domain::errors::CompileError;
use ats2_domain::tokens::*;
use std::collections::{HashMap, HashSet};

impl LlvmIrEmitter {
    /// Lower one expression, appending its instructions to `fb`.
    pub(crate) fn emit_expr(
        &self,
        expr: &Expr,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
    pub(crate) fn emit_expr_expecting(
        &self,
        expr: &Expr,
        expected: Option<LlvmType>,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
        match expr {
            Expr::Unit => Ok(FnValue {
                reg: String::new(),
                ty: LlvmType::Void,
            }),
            // `fact_ind{n}()` — a static instantiation.  It picks which
            // *claim* is being made and no bits at all, so emission
            // looks straight through it.  This is where the static
            // language stops: everything past here runs.
            // `e : t` — an ascription.  It says what `e` should be,
            // which the checker has already read; nothing about the
            // value changes, so emission looks through it.
            Expr::Ascribe(inner, _) => {
                self.emit_expr_expecting(inner, expected, fb, registry, module)
            }
            // `$extval`/`$extfcall` — a reach into C.  The type argument is
            // what ATS sees; the string is what C is called.  The arguments
            // are emitted as ordinary expressions, their types fix the C
            // signature, and the function is *declared* here — which is
            // what lets the host toolchain find it at link time.  (`$extfcall`
            // goes through a function pointer in C; both spellings name a
            // function symbol here, so both declare one and call it.)
            Expr::ExtVal { ty, name, args, .. } => {
                if args.is_empty() {
                    // `$extval(T, "CONST")` names a C constant — a macro
                    // or enum, most often, which has no symbol of its own,
                    // or a global.  A getter is generated beside the
                    // program's own C — `T ats_extval_CONST(void) { return
                    // (T)(CONST); }` — where the defining `#include` lives,
                    // and this is the call into it.  A getter, not a
                    // global, because a file-scope initializer cannot read
                    // a global, and the point of the name is that it may
                    // be either.
                    let ty = llvm_type_in(ty, registry)?;
                    let c_name = format!("ats_extval_{}", sanitize(name));
                    module.externs.insert(Box::leak(
                        format!("declare {} @{}()", llvm_ty_str(ty), c_name)
                            .into_boxed_str(),
                    ));
                    let reg = fb.fresh_temp();
                    fb.line(format!("{reg} = call {} @{}()", llvm_ty_str(ty), c_name));
                    return Ok(FnValue { reg, ty });
                }
                let ret = llvm_type_in(ty, registry)?;
                let mut arg_tys: Vec<LlvmType> = Vec::new();
                let mut operands: Vec<String> = Vec::new();
                for arg in args {
                    let v = self.emit_expr(arg, fb, registry, module)?;
                    arg_tys.push(v.ty);
                    operands.push(format!("{} {}", llvm_ty_str(v.ty), v.reg));
                }
                let params = arg_tys
                    .iter()
                    .map(|t| llvm_ty_str(*t))
                    .collect::<Vec<_>>()
                    .join(", ");
                module.externs.insert(Box::leak(
                    format!(
                        "declare {} @{}({})",
                        llvm_ty_str(ret),
                        sanitize(name),
                        params
                    )
                    .into_boxed_str(),
                ));
                if ret == LlvmType::Void {
                    fb.line(format!(
                        "call void @{}({})",
                        sanitize(name),
                        operands.join(", ")
                    ));
                    return Ok(FnValue {
                        reg: String::new(),
                        ty: LlvmType::Void,
                    });
                }
                let reg = fb.fresh_temp();
                fb.line(format!(
                    "{reg} = call {} @{}({})",
                    llvm_ty_str(ret),
                    sanitize(name),
                    operands.join(", ")
                ));
                Ok(FnValue { reg, ty: ret })
            }
            // `(pf | v)` — a value with a proof about it.  The proof is
            // erased; what runs is `v`.
            Expr::ProofPair(_, value) => {
                self.emit_expr_expecting(value, expected, fb, registry, module)
            }
            Expr::StaticInst(inner, _) => {
                self.emit_expr_expecting(inner, expected, fb, registry, module)
            }
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
                Ok(FnValue {
                    reg: ptr,
                    ty: LlvmType::Record(registry.intern_record(shape)),
                })
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
                    return Err(CompileError::emit(format!(
                        "this record has no field `{name}`"
                    )));
                };
                let addr = self.emit_slot_address(&v.reg, slot, fb);
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = load {}, ptr {addr}", llvm_ty_str(ty)));
                Ok(FnValue { reg, ty })
            }
            Expr::TupleLit(items) => {
                let want: Vec<Option<LlvmType>> = match expected {
                    Some(LlvmType::Tuple(i)) => {
                        registry.tuple_parts(i).into_iter().map(Some).collect()
                    }
                    _ => vec![None; items.len()],
                };
                let mut values = Vec::new();
                for (item, w) in items
                    .iter()
                    .zip(want.into_iter().chain(std::iter::repeat(None)))
                {
                    values.push(self.emit_expr_expecting(item, w, fb, registry, module)?);
                }
                let parts: Vec<LlvmType> = values.iter().map(|v| v.ty).collect();
                let ptr = self.emit_alloc(WORD * values.len(), fb, module);
                for (i, v) in values.iter().enumerate() {
                    let addr = self.emit_slot_address(&ptr, i, fb);
                    fb.line(format!("store {} {}, ptr {addr}", llvm_ty_str(v.ty), v.reg));
                }
                Ok(FnValue {
                    reg: ptr,
                    ty: LlvmType::Tuple(registry.intern_tuple(parts)),
                })
            }
            Expr::Wildcard => Err(CompileError::emit(
                "`_` stands for a value the compiler must infer, which this one cannot",
            )),
            // An uninitialized `var`.  The annotation is the only thing
            // that says what the cell holds, so without one there is
            // nothing to start it from.
            Expr::Uninit => match expected {
                Some(ty) => Ok(FnValue {
                    reg: zero_literal(ty).to_string(),
                    ty,
                }),
                None => Err(CompileError::emit(
                    "an uninitialized `var` needs a type annotation to say what its cell holds",
                )),
            },
            Expr::Inst(name, _) => Err(CompileError::emit(format!(
                "internal: the template `{name}` was not expanded"
            ))),
            Expr::IntLit(n) => Ok(FnValue {
                reg: n.to_string(),
                ty: LlvmType::I64,
            }),
            Expr::CharLit(b) => Ok(FnValue {
                reg: b.to_string(),
                ty: LlvmType::I8,
            }),
            // LLVM wants a float constant to look like one, so a whole
            // number still carries its point: `1` would be an integer.
            Expr::FloatLit(v) => {
                let x = v.value();
                let text = if x == x.trunc() && x.is_finite() {
                    format!("{x:.1}")
                } else {
                    format!("{x}")
                };
                Ok(FnValue {
                    reg: text,
                    ty: LlvmType::F64,
                })
            }
            Expr::BoolLit(b) => Ok(FnValue {
                reg: if *b { "true".into() } else { "false".into() },
                ty: LlvmType::I1,
            }),
            Expr::StrLit(s) => {
                // With opaque pointers, a constant's address is the global
                // itself: `ptr @.str.k`.  No GEP is needed for whole
                // constants (modern LLVM style).
                let reg = module.add_string(s);
                Ok(FnValue {
                    reg,
                    ty: LlvmType::I8Ptr,
                })
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
                Ok(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Never,
                })
            }
            Expr::Var(name) if fb.cells.contains_key(name) => {
                let cell = fb.cells[name].clone();
                let reg = fb.fresh_temp();
                fb.line(format!(
                    "{reg} = load {}, ptr {}",
                    llvm_ty_str(cell.ty),
                    cell.ptr
                ));
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
                fb.line(format!(
                    "{reg} = load {}, ptr @{}",
                    llvm_ty_str(ty),
                    sanitize(name)
                ));
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
                Ok(FnValue {
                    reg,
                    ty: LlvmType::FileRef,
                })
            }
            // `file_mode_r` / `file_mode_w` are the C mode strings.
            Expr::Var(name) if !fb.env.contains_key(name) && file_mode(name).is_some() => {
                let reg = module.add_string(file_mode(name).expect("just checked"));
                Ok(FnValue {
                    reg,
                    ty: LlvmType::I8Ptr,
                })
            }
            // `Nil` without parentheses still builds the value.
            Expr::Var(name)
                if !fb.env.contains_key(name)
                    && registry
                        .ctors
                        .get(name)
                        .is_some_and(|c| c.iter().all(|i| i.fields.is_empty())) =>
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
                None if registry.fns.contains_key(name) => Err(CompileError::emit(format!(
                    "function `{name}` used as a value; higher-order functions are not supported yet"
                ))),
                None => Err(CompileError::emit(format!("undefined variable `{name}`"))),
            },
            Expr::UnaryNeg(e) => {
                let v = self.emit_expr(e, fb, registry, module)?;
                match v.ty {
                    LlvmType::I64 => {
                        let reg = fb.fresh_temp();
                        fb.line(format!("{reg} = sub i64 0, {}", v.reg));
                        Ok(FnValue {
                            reg,
                            ty: LlvmType::I64,
                        })
                    }
                    LlvmType::F64 => {
                        let reg = fb.fresh_temp();
                        fb.line(format!("{reg} = fneg double {}", v.reg));
                        Ok(FnValue {
                            reg,
                            ty: LlvmType::F64,
                        })
                    }
                    // `~xs` on anything else *consumes* it: ATS spells
                    // "negate" and "free this linear value" with the same
                    // character, and only the operand's type tells them
                    // apart.  The operand is still evaluated — it may be
                    // a call that does the real work — and then there is
                    // nothing to free, because the arena frees
                    // everything at once.
                    _ => Ok(FnValue {
                        reg: String::new(),
                        ty: LlvmType::Void,
                    }),
                }
            }
            Expr::BinOp(op, l, r) => self.emit_binop(*op, l, r, fb, registry, module),
            Expr::Call(callee, args) => {
                self.emit_call(callee, args, expected, fb, registry, module)
            }
            Expr::Index(base, index) => self.emit_index(base, index, fb, registry, module),
            Expr::Proj(base, slot) => self.emit_proj(base, *slot, fb, registry, module),
            Expr::Deref(inner) => self.emit_deref(inner, fb, registry, module),
            Expr::Store(place, value) => self.emit_store(place, value, fb, registry, module),
            Expr::IfThenElse(c, t, e) => self.emit_if(c, t, e, expected, fb, registry, module),
            Expr::Let(binds, body) => {
                for bind in binds {
                    // A proof binding names a proof: no storage, no
                    // code, and the axiom on its right-hand side has no
                    // body anywhere.  Emission is where the static
                    // language stops, and this is the line where it
                    // stops.
                    if bind.proof {
                        continue;
                    }
                    let annotated = bind
                        .ty
                        .as_ref()
                        .map(|t| llvm_type_in(t, registry))
                        .transpose()?;
                    let v =
                        self.emit_expr_expecting(&bind.value, annotated, fb, registry, module)?;
                    if let Some(ann) = &bind.ty {
                        let expected = llvm_type_in(ann, registry)?;
                        if v.ty != expected {
                            return Err(CompileError::emit(format!(
                                "binding `{}` has type {}, annotation says {}",
                                bind.name.as_deref().unwrap_or("()"),
                                llvm_ty_str(v.ty),
                                llvm_ty_str(expected)
                            )));
                        }
                    }
                    if let Some(name) = &bind.name {
                        if bind.mutable {
                            let ptr = fb.alloca(name, v.ty);
                            fb.line(format!(
                                "store {} {}, ptr {}",
                                llvm_ty_str(v.ty),
                                v.reg,
                                ptr
                            ));
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
            Expr::Lam(params, ret, body) => {
                self.emit_lambda(params, ret.as_ref(), body, expected, fb, registry, module)
            }
            Expr::LetFun(_, _) => Err(CompileError::emit(
                "internal: a nested function survived lambda lifting",
            )),
            Expr::Assign(name, value) => self.emit_assign(name, value, fb, registry, module),
            Expr::While(c, b) => self.emit_while(c, b, fb, registry, module),
            Expr::For(i, c, st, b) => self.emit_for(i, c, st, b, fb, registry, module),
            Expr::Case(scrutinee, arms) => {
                self.emit_case(scrutinee, arms, expected, fb, registry, module)
            }
            Expr::MacroCall(name, args) => self.emit_macro(name, args, fb, registry, module),
            Expr::Try(body, handlers) => self.emit_try(body, handlers, expected, fb, registry, module),
            Expr::Raise(value) => self.emit_raise(value, fb, registry, module),
        }
    }

    pub(crate) fn emit_binop(
        &self,
        op: BinOp,
        l: &Expr,
        r: &Expr,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
        let (lv, rv) = (
            self.emit_expr(l, fb, registry, module)?,
            self.emit_expr(r, fb, registry, module)?,
        );
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
    pub(crate) fn emit_binop_values(
        &self,
        op: BinOp,
        lv: FnValue,
        rv: FnValue,
        fb: &mut FnBuilder,
    ) -> Result<FnValue, CompileError> {
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                if lv.ty == LlvmType::F64 && rv.ty == LlvmType::F64 {
                    let instr = match op {
                        BinOp::Add => "fadd",
                        BinOp::Sub => "fsub",
                        BinOp::Mul => "fmul",
                        BinOp::Div => "fdiv",
                        _ => "frem",
                    };
                    let reg = fb.fresh_temp();
                    fb.line(format!("{reg} = {instr} double {}, {}", lv.reg, rv.reg));
                    return Ok(FnValue {
                        reg,
                        ty: LlvmType::F64,
                    });
                }
                let instr = match op {
                    BinOp::Add => "add",
                    BinOp::Sub => "sub",
                    BinOp::Mul => "mul",
                    BinOp::Div => "sdiv",
                    _ => "srem",
                };
                self.emit_arithmetic(instr, lv, rv, fb)
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                self.emit_comparison(op, lv, rv, fb)
            }
            BinOp::Andalso | BinOp::Orelse => Err(CompileError::emit(
                "andalso/orelse are not value operations",
            )),
        }
    }

    /// Apply the function an `overload` named for this operator.
    ///
    /// Only the generic numeric shims are reachable this way so far, which
    /// is what the samples declare; a user function of the right shape
    /// would need its arguments passed rather than its meaning inlined.
    pub(crate) fn emit_overload(
        &self,
        func: &str,
        op: BinOp,
        lv: FnValue,
        rv: FnValue,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
        if func.starts_with('g') && (func.contains("_int_val") || func.contains("_val_int")) {
            return self.emit_promoted(op, lv, rv, fb);
        }
        let sig = registry.fns.get(func).ok_or_else(|| {
            CompileError::emit(format!(
                "`{func}` is named by an `overload` but is not defined"
            ))
        })?;
        if sig.params.len() != 2 {
            return Err(CompileError::emit(format!(
                "`{func}` is an overload, so it must take two arguments"
            )));
        }
        let _ = module;
        let operands = [
            format!("{} {}", llvm_ty_str(lv.ty), lv.reg),
            format!("{} {}", llvm_ty_str(rv.ty), rv.reg),
        ];
        let reg = fb.fresh_temp();
        fb.line(format!(
            "{reg} = call {} @{}({})",
            llvm_ty_str(sig.ret),
            sanitize(func),
            operands.join(", ")
        ));
        Ok(FnValue { reg, ty: sig.ret })
    }

    /// `+ - * / mod` on ints.
    pub(crate) fn emit_arithmetic(
        &self,
        instr: &str,
        lv: FnValue,
        rv: FnValue,
        fb: &mut FnBuilder,
    ) -> Result<FnValue, CompileError> {
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
            return Ok(FnValue {
                reg,
                ty: LlvmType::F64,
            });
        }
        if lv.ty != LlvmType::I64 || rv.ty != LlvmType::I64 {
            return Err(CompileError::emit("arithmetic requires int operands"));
        }
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = {instr} i64 {}, {}", lv.reg, rv.reg));
        Ok(FnValue {
            reg,
            ty: LlvmType::I64,
        })
    }

    /// Comparisons, lowered to `icmp` with the code dictated by the
    /// operand type (`slt` for ints; `eq`/`ne` for bools; ordering a bool
    /// is an error).
    pub(crate) fn emit_comparison(
        &self,
        op: BinOp,
        lv: FnValue,
        rv: FnValue,
        fb: &mut FnBuilder,
    ) -> Result<FnValue, CompileError> {
        // `p > 0`, `p = 0` — ATS's way of asking whether a call handed
        // back anything.  A pointer is not a number, so the only reading
        // that means something is the null test, and that is what is
        // emitted rather than an ordering on addresses.
        if let Some(v) = self.emit_null_test(op, &lv, &rv, fb) {
            return Ok(v);
        }
        if lv.ty != rv.ty {
            return Err(CompileError::emit(
                "cannot compare values of different types",
            ));
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
                BinOp::Eq => "oeq",
                BinOp::Ne => "one",
                BinOp::Lt => "olt",
                BinOp::Le => "ole",
                BinOp::Gt => "ogt",
                _ => "oge",
            };
            let reg = fb.fresh_temp();
            fb.line(format!(
                "{reg} = fcmp {fcode} double {}, {}",
                lv.reg, rv.reg
            ));
            return Ok(FnValue {
                reg,
                ty: LlvmType::I1,
            });
        }
        let reg = fb.fresh_temp();
        fb.line(format!(
            "{reg} = icmp {code} {} {}, {}",
            llvm_ty_str(lv.ty),
            lv.reg,
            rv.reg
        ));
        Ok(FnValue {
            reg,
            ty: LlvmType::I1,
        })
    }

    /// A comparison of a pointer against the literal zero, as the null
    /// test it means.  `None` when this is not that comparison.
    pub(crate) fn emit_null_test(
        &self,
        op: BinOp,
        lv: &FnValue,
        rv: &FnValue,
        fb: &mut FnBuilder,
    ) -> Option<FnValue> {
        let pointerish = |t: LlvmType| {
            matches!(
                t,
                LlvmType::I8Ptr
                    | LlvmType::Data(_)
                    | LlvmType::Tuple(_)
                    | LlvmType::Array(_)
                    | LlvmType::Closure(_)
                    | LlvmType::Lazy(_)
                    | LlvmType::Record(_)
                    | LlvmType::FileRef
            )
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
        Some(FnValue {
            reg,
            ty: LlvmType::I1,
        })
    }

    /// `a andalso b` / `a orelse b` with ATS short-circuit semantics:
    /// evaluate `b` only when the first operand decides the outcome.
    pub(crate) fn emit_short_circuit(
        &self,
        op: BinOp,
        cond: String,
        r: &Expr,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
            FnValue {
                reg: "true".into(),
                ty: LlvmType::I1,
            }
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
            FnValue {
                reg: "false".into(),
                ty: LlvmType::I1,
            }
        };
        let epred = fb.cur_block.clone();
        for v in [&then_done, &else_done] {
            if v.ty != LlvmType::I1 {
                return Err(CompileError::emit("andalso/orelse require bool operands"));
            }
        }
        fb.label(&m);
        let reg = fb.fresh_temp();
        fb.line(format!(
            "{reg} = phi i1 [ {}, %{tpred} ], [ {}, %{epred} ]",
            then_done.reg, else_done.reg
        ));
        Ok(FnValue {
            reg,
            ty: LlvmType::I1,
        })
    }

    pub(crate) fn emit_call(
        &self,
        callee: &Expr,
        args: &[Expr],
        expected: Option<LlvmType>,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
            let head = match peel_static(inner) {
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
            return self.emit_call(
                &Expr::Var(field.clone()),
                &all,
                expected,
                fb,
                registry,
                module,
            );
        }

        // `f<t>(x)` reaches here when `f` is a shim rather than a
        // template: the type arguments choose which shim is meant.
        // Static instantiation — `ax{n}(...)` — chose a *claim*, which
        // stopped mattering one stage ago, so it is looked through.
        let callee = peel_static(callee);
        let (name, ty_args) = match callee {
            Expr::Var(n) => (n, Vec::new()),
            Expr::Inst(n, tys) => (n, tys.clone()),
            _ => {
                return Err(CompileError::emit(
                    "only named functions can be called (no higher-order calls)",
                ));
            }
        };
        if name == "main0" || name == "main" {
            return Err(CompileError::emit(format!(
                "`{name}` is the program entry and cannot be called"
            )));
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
        let sig = registry
            .fns
            .get(name)
            .ok_or_else(|| CompileError::emit(format!("unknown function `{name}`")))?;
        // Declared here, defined nowhere and answered by no shim: it is
        // C's, and a declaration is what lets the call reach it.
        if !registry.defined.contains(name) {
            let ps: Vec<&str> = sig.params.iter().map(|p| llvm_ty_str(*p)).collect();
            module.externs.insert(Box::leak(
                format!(
                    "declare {} @{}({})",
                    llvm_ty_str(sig.ret),
                    sanitize(name),
                    ps.join(", ")
                )
                .into_boxed_str(),
            ));
        }
        if args.len() != sig.params.len() {
            return Err(CompileError::emit(format!(
                "function `{name}` expects {} argument(s), got {}",
                sig.params.len(),
                args.len()
            )));
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
                return Err(CompileError::emit(format!(
                    "argument to `{name}` has type {}, expected {}",
                    llvm_ty_str(v.ty),
                    llvm_ty_str(*want)
                )));
            }
            operands.push(format!("{} {}", llvm_ty_str(v.ty), v.reg));
        }
        // A void call names no result: `%t = call void @f()` is invalid IR.
        if sig.ret == LlvmType::Void {
            fb.line(format!(
                "call void @{}({})",
                sanitize(name),
                operands.join(", ")
            ));
            return Ok(FnValue {
                reg: String::new(),
                ty: LlvmType::Void,
            });
        }
        let reg = fb.fresh_temp();
        fb.line(format!(
            "{reg} = call {} @{}({})",
            llvm_ty_str(sig.ret),
            sanitize(name),
            operands.join(", ")
        ));
        Ok(FnValue { reg, ty: sig.ret })
    }

    pub(crate) fn emit_if(
        &self,
        c: &Expr,
        t: &Expr,
        e: &Expr,
        expected: Option<LlvmType>,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
            return Ok(FnValue {
                reg: String::new(),
                ty: LlvmType::Never,
            });
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
            return Ok(FnValue {
                reg: String::new(),
                ty: LlvmType::Void,
            });
        }
        let incoming: Vec<String> = arms
            .iter()
            .map(|(v, p)| format!("[ {}, %{p} ]", v.reg))
            .collect();
        let reg = fb.fresh_temp();
        fb.line(format!(
            "{reg} = phi {} {}",
            llvm_ty_str(ty),
            incoming.join(", ")
        ));
        Ok(FnValue { reg, ty })
    }

    /// The `print` family.  ATS spells the destination and the trailing
    /// newline into the macro's *name*: `print!`/`println!` go to stdout,
    /// `prerr!`/`prerrln!` to stderr, and the `f`-prefixed forms take the
    /// stream as their first argument.  All of them collapse to a single
    /// `printf`/`fprintf` call with one synthesized format string, which
    /// is both the simplest lowering and the fastest one.

    /// `$raise e` — store the raised value and longjmp to the nearest
    /// enclosing `try`.  `setjmp`/`longjmp` are libc, and LLVM requires a
    /// `setjmp` to be called *directly* in the frame that reads its
    /// return (a helper would silently never unwind), so the raise emits
    /// the `longjmp` inline against a frame the try set up the same way.
    /// The raised value and the current frame live in two globals the
    /// `try` and `raise` share.
    pub(crate) fn emit_raise(
        &self,
        value: &Expr,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
        module.needs_exn = true;
        module.externs.insert("declare i32 @setjmp(ptr)");
        module
            .externs
            .insert("declare void @longjmp(ptr, i32) noreturn");
        let name = match value {
            Expr::Var(n) => n.clone(),
            Expr::Call(head, _) => match head.as_ref() {
                Expr::Var(n) => n.clone(),
                _ => "exception".to_string(),
            },
            _ => "exception".to_string(),
        };
        // Build the exception box (a declared exception) or, failing
        // that, evaluate the value in case it constructs one.
        let box_reg = if registry.ctors.contains_key(name.as_str()) {
            let info = resolve_ctor(&name, &[], None, registry)?;
            let ptr = self.emit_alloc(WORD * (1 + info.width), fb, module);
            fb.line(format!("store i64 {}, ptr {ptr}", info.tag));
            // `$raise Found(x)` — the payload rides in the slots after
            // the tag, each argument stored where its handler reads it.
            if let Expr::Call(_, args) = value {
                for (i, arg) in args.iter().enumerate() {
                    let v = self.emit_expr(arg, fb, registry, module)?;
                    let addr = self.emit_slot_address(&ptr, i + 1, fb);
                    fb.line(format!("store {} {}, ptr {addr}", llvm_ty_str(v.ty), v.reg));
                }
            }
            ptr
        } else {
            // Either a constructed exception (build it) or a genuinely
            // unknown name: fall back to naming the uncaught raise.
            match value {
                Expr::Call(..) => self.emit_expr(value, fb, registry, module)?.reg,
                Expr::Var(_) => {
                    let msg = format!("exit(ATS): uncaught {name}\n");
                    self.emit_printf(Stream::Stderr, &msg, &[], fb, module);
                    fb.line("call void @exit(i32 1)");
                    fb.line("unreachable");
                    return Ok(FnValue {
                        reg: String::new(),
                        ty: LlvmType::Never,
                    });
                }
                _ => "null".to_string(),
            }
        };
        // Store the raised value, load the current frame, longjmp.
        fb.line(format!("store ptr {box_reg}, ptr @ats2_exval"));
        let cur = fb.fresh_temp();
        fb.line(format!("{cur} = load ptr, ptr @ats2_cur"));
        // No frame at all: what raised here has nothing to unwind to, so
        // the honest end is the one the raise always had before a `try`
        // could catch — name the exception and stop.
        let id = fb.fresh_block_id();
        let ok = format!("raise.throw.{id}");
        let none = format!("raise.none.{id}");
        let has = fb.fresh_temp();
        fb.line(format!("{has} = icmp ne ptr {cur}, null"));
        fb.line(format!("br i1 {has}, label %{ok}, label %{none}"));
        fb.label(&none);
        let msg = format!("exit(ATS): uncaught {name}\n");
        self.emit_printf(Stream::Stderr, &msg, &[], fb, module);
        fb.line("call void @exit(i32 1)");
        fb.line("unreachable");
        fb.label(&ok);
        let jb = fb.fresh_temp();
        fb.line(format!("{jb} = getelementptr i8, ptr {cur}, i64 8"));
        fb.line(format!("call void @longjmp(ptr {jb}, i32 1)"));
        fb.line("unreachable");
        Ok(FnValue {
            reg: String::new(),
            ty: LlvmType::Never,
        })
    }

    /// `try e with | ~X(p) => h | ... ` — run `e` under a handler.  The
    /// `setjmp` is emitted *directly* here (LLVM needs it in the frame
    /// that checks its return), the body runs, and a raise longjmps back
    /// so this returns nonzero and the handlers dispatch on the tag.
    pub(crate) fn emit_try(
        &self,
        body: &Expr,
        handlers: &[(Pattern, Expr)],
        expected: Option<LlvmType>,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
        if handlers.is_empty() {
            return Err(CompileError::emit("a `try` needs at least one handler"));
        }
        module.needs_exn = true;
        module.externs.insert("declare i32 @setjmp(ptr)");
        module
            .externs
            .insert("declare void @longjmp(ptr, i32) noreturn");

        let id = fb.fresh_block_id();
        let merge = format!("try.done.{id}");
        let body_label = format!("try.body.{id}");
        let nolabel = format!("try.ralabel.{id}");

        // Frame: { parent*, jmp_buf }.  Set the chain and save jmp_buf.
        let frame = self.emit_alloc(512, fb, module);
        let old = fb.fresh_temp();
        fb.line(format!("{old} = load ptr, ptr @ats2_cur"));
        fb.line(format!("store ptr {old}, ptr {frame}"));
        fb.line(format!("store ptr {frame}, ptr @ats2_cur"));
        let jb = fb.fresh_temp();
        fb.line(format!("{jb} = getelementptr i8, ptr {frame}, i64 8"));
        let r = fb.fresh_temp();
        fb.line(format!("{r} = call i32 @setjmp(ptr {jb})"));
        let z = fb.fresh_temp();
        fb.line(format!("{z} = icmp eq i32 {r}, 0"));
        let caught_l = format!("try.dsp.{id}.0");
        fb.line(format!("br i1 {z}, label %{body_label}, label %{caught_l}"));

        // Body: run it; on normal completion restore the frame chain.
        fb.label(&body_label);
        let saved_env = fb.env.clone();
        let saved_cells = fb.cells.clone();
        let mut results: Vec<(FnValue, String)> = Vec::new();
        let b = self.emit_expr_expecting(body, expected, fb, registry, module)?;
        if b.ty != LlvmType::Never {
            let body_pred = fb.cur_block.clone();
            // restore: @ats2_cur = old
            fb.line(format!("store ptr {old}, ptr @ats2_cur"));
            fb.line(format!("br label %{merge}"));
            results.push((b, body_pred));
        }
        fb.env = saved_env;
        fb.cells = saved_cells;

        // Caught: read the raised value and its tag, then dispatch.
        // The frame chain is restored *first*, so a handler that raises
        // throws into the frame this try was itself under, not back into
        // this one — a raise must not be caught by the try that is
        // already handling it.
        fb.label(&caught_l);
        fb.line(format!("store ptr {old}, ptr @ats2_cur"));
        let exn = fb.fresh_temp();
        fb.line(format!("{exn} = load ptr, ptr @ats2_exval"));
        let tag = fb.fresh_temp();
        fb.line(format!("{tag} = load i64, ptr {exn}"));
        let mut catchall_hit = false;

        for (i, (pat, handler)) in handlers.iter().enumerate() {
            // Each handler's dispatch block (beyond the first, which is
            // the caught block) is where the previous handler's mismatch
            // branches to.
            if i > 0 {
                let d = format!("try.dsp.{id}.{i}");
                fb.label(&d);
            }
            let arm = format!("try.arm.{id}.{i}");
            let is_last = i + 1 == handlers.len();
            let next_i: Option<String> = if is_last {
                None
            } else {
                Some(format!("try.dsp.{id}.{}", i + 1))
            };
            match pat {
                Pattern::Ctor(xname, fieldpats) => {
                    let Some(info) = registry.ctors.get(xname.as_str()).and_then(|c| c.get(0))
                    else {
                        continue;
                    };
                    let clash = fb.fresh_temp();
                    fb.line(format!("{clash} = icmp eq i64 {tag}, {}", info.tag));
                    let miss = next_i.as_deref().unwrap_or(&nolabel);
                    let arm_l = arm.clone();
                    fb.line(format!("br i1 {clash}, label %{arm_l}, label %{miss}"));
                    fb.label(&arm);
                    let saved = fb.env.clone();
                    for (fi, fpat) in fieldpats.iter().enumerate() {
                        if let Pattern::Var(vname) = fpat {
                            let ty = info.fields.get(fi).copied().unwrap_or(LlvmType::I64);
                            let addr = self.emit_slot_address(&exn, fi + 1, fb);
                            let reg = fb.fresh_temp();
                            fb.line(format!("{reg} = load {}, ptr {addr}", llvm_ty_str(ty)));
                            fb.env.insert(vname.clone(), FnValue { reg, ty });
                        }
                    }
                    let hv = self.emit_expr_expecting(handler, expected, fb, registry, module)?;
                    if hv.ty != LlvmType::Never {
                        let pred = fb.cur_block.clone();
                        fb.line(format!("store ptr {old}, ptr @ats2_cur"));
                        fb.line(format!("br label %{merge}"));
                        results.push((hv, pred));
                    }
                    fb.env = saved;
                }
                Pattern::Var(vname) => {
                    catchall_hit = true;
                    let saved = fb.env.clone();
                    let reg = fb.fresh_temp();
                    fb.line(format!("{reg} = load i64, ptr {exn}"));
                    fb.env.insert(
                        vname.clone(),
                        FnValue {
                            reg,
                            ty: LlvmType::I64,
                        },
                    );
                    let hv = self.emit_expr_expecting(handler, expected, fb, registry, module)?;
                    if hv.ty != LlvmType::Never {
                        let pred = fb.cur_block.clone();
                        fb.line(format!("store ptr {old}, ptr @ats2_cur"));
                        fb.line(format!("br label %{merge}"));
                        results.push((hv, pred));
                    }
                    fb.env = saved;
                    break;
                }
                Pattern::Wildcard => {
                    catchall_hit = true;
                    let hn = self.emit_expr_expecting(handler, expected, fb, registry, module)?;
                    if hn.ty != LlvmType::Never {
                        let pred = fb.cur_block.clone();
                        fb.line(format!("store ptr {old}, ptr @ats2_cur"));
                        fb.line(format!("br label %{merge}"));
                        results.push((hn, pred));
                    }
                    break;
                }
                _ => continue,
            }
        }

        // Re-raise whatever no handler covered (restoring the chain first).
        if !catchall_hit {
            fb.label(&nolabel);
            fb.line(format!("store ptr {old}, ptr @ats2_cur"));
            let cur2 = fb.fresh_temp();
            fb.line(format!("{cur2} = load ptr, ptr @ats2_cur"));
            let jb2 = fb.fresh_temp();
            fb.line(format!("{jb2} = getelementptr i8, ptr {cur2}, i64 8"));
            fb.line(format!("call void @longjmp(ptr {jb2}, i32 1)"));
            fb.line("unreachable");
        }
        // A raise that longjmps past this try has already restored the
        // frame chain via the re-raise above.

        // Merge the arms that produced values.
        fb.label(&merge);
        let Some(((first, _), rest)) = results.split_first() else {
            fb.line("unreachable");
            return Ok(FnValue {
                reg: String::new(),
                ty: LlvmType::Never,
            });
        };
        for (other, _) in rest {
            if other.ty != first.ty {
                return Err(CompileError::emit(format!(
                    "try arms have different types ({} vs {})",
                    llvm_ty_str(first.ty),
                    llvm_ty_str(other.ty)
                )));
            }
        }
        let ty = first.ty;
        if ty == LlvmType::Void {
            return Ok(FnValue {
                reg: String::new(),
                ty,
            });
        }
        let incoming: Vec<String> = results
            .iter()
            .map(|(v, p)| format!("[ {}, %{p} ]", v.reg))
            .collect();
        let reg = fb.fresh_temp();
        fb.line(format!(
            "{reg} = phi {} {}",
            llvm_ty_str(ty),
            incoming.join(", ")
        ));
        Ok(FnValue { reg, ty })
    }

    pub(crate) fn emit_macro(
        &self,
        name: &str,
        args: &[Expr],
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
        let (stream, newline, takes_stream) = match name {
            "print!" => (Stream::Stdout, false, false),
            "println!" => (Stream::Stdout, true, false),
            "prerr!" => (Stream::Stderr, false, false),
            "prerrln!" => (Stream::Stderr, true, false),
            "fprint!" => (Stream::Stdout, false, true),
            "fprintln!" => (Stream::Stdout, true, true),
            _ => {
                return Err(CompileError::emit(format!(
                    "unsupported macro `{name}` (the print family and `assertloc` are what exist)"
                )));
            }
        };
        // `fprint!(out, ...)`: the stream argument is read from the first
        // position.  It may be any expression of type `FILEref`; the two
        // standard streams are recognised by name only because writing to
        // them needs no stream operand.
        let (stream, args) = if takes_stream {
            let Some((first, rest)) = args.split_first() else {
                return Err(CompileError::emit(format!(
                    "`{name}` needs a stream as its first argument"
                )));
            };
            (
                self.emit_stream_argument(name, first, fb, registry, module)?,
                rest,
            )
        } else {
            (stream, args)
        };
        self.emit_format(&stream, args, newline, fb, registry, module)?;
        Ok(FnValue {
            reg: String::new(),
            ty: LlvmType::Void,
        })
    }

    /// The destination named by a print form's first argument.
    ///
    /// It may be any expression of type `FILEref`; the two standard
    /// streams are recognised by name as well, because writing to those
    /// needs no stream operand at all.
    pub(crate) fn emit_stream_argument(
        &self,
        name: &str,
        first: &Expr,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<Stream, CompileError> {
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
    pub(crate) fn emit_format(
        &self,
        stream: &Stream,
        args: &[Expr],
        newline: bool,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<(), CompileError> {
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
    pub(crate) fn format_one(
        &self,
        stream: &Stream,
        v: FnValue,
        fmt: &mut String,
        operands: &mut Vec<String>,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<(), CompileError> {
        {
            {
                {
                    match v.ty {
                        // ATS writes a tuple as `(a, b)`, and a nested one
                        // the same way — which is why this is the case
                        // that recurses.
                        LlvmType::Tuple(index) => {
                            fmt.push('(');
                            for (slot, part) in registry.tuple_parts(index).into_iter().enumerate()
                            {
                                if slot > 0 {
                                    fmt.push_str(", ");
                                }
                                let addr = self.emit_slot_address(&v.reg, slot, fb);
                                let reg = fb.fresh_temp();
                                fb.line(format!("{reg} = load {}, ptr {addr}", llvm_ty_str(part)));
                                self.format_one(
                                    stream,
                                    FnValue { reg, ty: part },
                                    fmt,
                                    operands,
                                    fb,
                                    registry,
                                    module,
                                )?;
                            }
                            fmt.push(')');
                        }
                        LlvmType::I64 => {
                            fmt.push_str("%ld");
                            operands.push(format!("i64 {}", v.reg));
                        }
                        LlvmType::I8Ptr => {
                            fmt.push_str("%s");
                            operands.push(format!("ptr {}", v.reg));
                        }
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
                        LlvmType::I32 => {
                            fmt.push_str("%d");
                            operands.push(format!("i32 {}", v.reg));
                        }
                        // varargs promote a byte to an int, so the
                        // operand must be widened to match.
                        LlvmType::F64 => {
                            fmt.push_str("%f");
                            operands.push(format!("double {}", v.reg));
                        }
                        LlvmType::I8 => {
                            let reg = fb.fresh_temp();
                            fb.line(format!("{reg} = sext i8 {} to i32", v.reg));
                            fmt.push_str("%c");
                            operands.push(format!("i32 {reg}"));
                        }
                        LlvmType::Argv => {
                            return Err(CompileError::emit(
                                "cannot print `argv` itself; index it first",
                            ));
                        }
                        LlvmType::Never => {
                            return Err(CompileError::emit(
                                "cannot print the result of an expression that never returns",
                            ));
                        }
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
                        LlvmType::Data(_) => {
                            return Err(CompileError::emit(
                                "cannot print a datatype value; match on it first",
                            ));
                        }

                        LlvmType::Array(_) => {
                            return Err(CompileError::emit(
                                "cannot print an array; index it first",
                            ));
                        }
                        LlvmType::Closure(_) => {
                            return Err(CompileError::emit("cannot print a function"));
                        }
                        LlvmType::Lazy(_) => {
                            return Err(CompileError::emit(
                                "cannot print a stream; force it with `!` first",
                            ));
                        }
                        LlvmType::Record(_) => {
                            return Err(CompileError::emit(
                                "cannot print a record; name a field of it",
                            ));
                        }
                        LlvmType::FileRef => {
                            return Err(CompileError::emit(
                                "cannot print a FILEref; it names a stream, it is not data",
                            ));
                        }
                        LlvmType::Void => {
                            return Err(CompileError::emit("cannot print a void value"));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Emit the call itself.  Writing to stderr costs one extra load,
    /// because `stderr` is a libc *variable* holding the stream.
    pub(crate) fn emit_printf(
        &self,
        stream: Stream,
        fmt: &str,
        operands: &[String],
        fb: &mut FnBuilder,
        module: &mut ModuleBuilder,
    ) {
        let fmt_reg = module.add_format(fmt);
        let mut tail = String::new();
        if !operands.is_empty() {
            tail.push_str(", ");
            tail.push_str(&operands.join(", "));
        }
        let reg = fb.fresh_temp();
        match stream {
            Stream::Stdout => {
                fb.line(format!(
                    "{reg} = call i32 (ptr, ...) @printf(ptr {fmt_reg}{tail})"
                ));
            }
            Stream::Stderr => {
                let s = fb.fresh_temp();
                fb.line(format!("{s} = load ptr, ptr @stderr"));
                fb.line(format!(
                    "{reg} = call i32 (ptr, ptr, ...) @fprintf(ptr {s}, ptr {fmt_reg}{tail})"
                ));
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
    pub(crate) fn emit_shim(
        &self,
        name: &str,
        ty_args: &[Ty],
        args: &[Expr],
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<Option<FnValue>, CompileError> {
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
                self.require(
                    n.ty,
                    LlvmType::I64,
                    "the length given to an array constructor",
                )?;
                let ptr = self.emit_alloc_dynamic(&n.reg, fb, module);
                // `array_ptr_alloc` leaves the cells uninitialised; the
                // others fill them.  Uninitialised here still means
                // zeroed, because the arena is.
                if let Some(init) = args.get(1) {
                    let v = self.emit_expr_expecting(init, Some(elem), fb, registry, module)?;
                    self.emit_fill(&ptr, &n.reg, &v, fb);
                }
                Ok(Some(FnValue {
                    reg: ptr,
                    ty: LlvmType::Array(registry.intern_array(elem)),
                }))
            }
            // `arrayptr_foreach_env<a><env>(A, n, env)` — run the hole
            // `list_tabulate<a> (n)` — the list [f 0, ..., f (n-1)],
            // where `f` is the `$fopr` the caller filled in.
            //
            // A shim rather than ATS, because a hole is *inlined* into
            // the caller's scope rather than called: `list_tabulate$fopr`
            // in `listpermute` reads two of the enclosing function's own
            // bindings, and an ATS-level `list_tabulate` would have had
            // to call it and lose them.
            //
            // Counting down rather than up: consing builds a list back
            // to front, so starting at the last index puts the elements
            // in order in one pass instead of two.
            "list_tabulate" | "list_vt_tabulate" | "list_tabulate_vt" => {
                let [count] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes a length")));
                };
                let n = self.emit_expr(count, fb, registry, module)?;
                self.require(n.ty, LlvmType::I64, "a list length")?;
                let elem = match ty_args.first() {
                    Some(t) => llvm_type_in(t, registry)?,
                    None => {
                        return Err(CompileError::emit(format!(
                            "`{name}` must say what it builds a list of, as in `{name}<int>(n)`"
                        )));
                    }
                };
                let (nil, cons) = self.list_constructors(elem, registry).ok_or_else(|| {
                    CompileError::emit(format!(
                        "`{name}` builds a list of {}, and nothing in this program uses one",
                        llvm_ty_str(elem)
                    ))
                })?;
                let hole = self.require_hole("list_tabulate$fopr", registry)?;

                let list_ty = LlvmType::Data(nil.datatype);
                let acc = fb.alloca(&format!("tabulate.acc.{}", fb.block_ids), list_ty);
                let empty = self.emit_ctor_from_values(&nil, &[], fb, module);
                fb.line(format!("store ptr {}, ptr {acc}", empty.reg));

                let id = fb.fresh_block_id();
                let (head, body, done) = (
                    format!("tabulate.head.{id}"),
                    format!("tabulate.body.{id}"),
                    format!("tabulate.done.{id}"),
                );
                let index = fb.alloca(&format!("tabulate.i.{id}"), LlvmType::I64);
                let last = fb.fresh_temp();
                fb.line(format!("{last} = sub i64 {}, 1", n.reg));
                fb.line(format!("store i64 {last}, ptr {index}"));
                fb.line(format!("br label %{head}"));

                fb.label(&head);
                let i = fb.fresh_temp();
                let more = fb.fresh_temp();
                fb.line(format!("{i} = load i64, ptr {index}"));
                fb.line(format!("{more} = icmp sge i64 {i}, 0"));
                fb.line(format!("br i1 {more}, label %{body}, label %{done}"));

                fb.label(&body);
                let x = self.inline_hole(
                    &hole,
                    &[FnValue {
                        reg: i.clone(),
                        ty: LlvmType::I64,
                    }],
                    None,
                    fb,
                    registry,
                    module,
                )?;
                let tail = fb.fresh_temp();
                fb.line(format!("{tail} = load ptr, ptr {acc}"));
                let cell = self.emit_ctor_from_values(
                    &cons,
                    &[
                        x,
                        FnValue {
                            reg: tail,
                            ty: list_ty,
                        },
                    ],
                    fb,
                    module,
                );
                fb.line(format!("store ptr {}, ptr {acc}", cell.reg));
                let prev = fb.fresh_temp();
                let now = fb.fresh_temp();
                fb.line(format!("{prev} = load i64, ptr {index}"));
                fb.line(format!("{now} = sub i64 {prev}, 1"));
                fb.line(format!("store i64 {now}, ptr {index}"));
                fb.line(format!("br label %{head}"));

                fb.label(&done);
                let out = fb.fresh_temp();
                fb.line(format!("{out} = load ptr, ptr {acc}"));
                Ok(Some(FnValue {
                    reg: out,
                    ty: list_ty,
                }))
            }
            // `array_foreach$fwork` over every cell.
            "arrayptr_foreach_env"
            | "array_foreach_env"
            | "arrayref_foreach_env"
            | "arrayptr_foreach"
            | "array_foreach"
            | "arrayref_foreach" => {
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
                fb.line(format!(
                    "{addr} = getelementptr i8, ptr {}, i64 {off}",
                    a.reg
                ));
                let x = fb.fresh_temp();
                fb.line(format!("{x} = load {}, ptr {addr}", llvm_ty_str(elem_ty)));
                let bound = FnValue {
                    reg: x,
                    ty: elem_ty,
                };
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
                Ok(Some(FnValue {
                    reg: processed,
                    ty: LlvmType::I64,
                }))
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
                let bound = FnValue {
                    reg: i.clone(),
                    ty: LlvmType::I64,
                };
                self.inline_hole(&hole, &[bound], args.get(2), fb, registry, module)?;
                let next = fb.fresh_temp();
                fb.line(format!("{next} = add i64 {i}, 1"));
                fb.line(format!("store i64 {next}, ptr {cell}"));
                fb.line(format!("br label %{head}"));
                fb.label(&done);
                let processed = fb.fresh_temp();
                fb.line(format!("{processed} = sub i64 {}, {}", hi.reg, lo.reg));
                Ok(Some(FnValue {
                    reg: processed,
                    ty: LlvmType::I64,
                }))
            }
            // `string_foreach_env<env>(s, env)` — the same over a
            // string's characters, with an optional `$cont` hole deciding
            // whether to keep going.
            "string_foreach_env" | "string_foreach" => {
                let s = self.emit_expr(&args[0], fb, registry, module)?;
                self.require(
                    s.ty,
                    LlvmType::I8Ptr,
                    "the string given to `string_foreach`",
                )?;
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
                        let bound = FnValue {
                            reg: c.clone(),
                            ty: LlvmType::I8,
                        };
                        let v = self.inline_hole(k, &[bound], args.get(1), fb, registry, module)?;
                        self.require(v.ty, LlvmType::I1, "`string_foreach$cont`")?;
                        v.reg
                    }
                };
                fb.line(format!("br i1 {more}, label %{body}, label %{done}"));
                fb.label(&body);
                let bound = FnValue {
                    reg: c,
                    ty: LlvmType::I8,
                };
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
                Ok(Some(FnValue {
                    reg: processed,
                    ty: LlvmType::I64,
                }))
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
                    return Err(CompileError::emit(format!(
                        "`{name}` takes a string and an index"
                    )));
                };
                let sv = self.emit_expr(s, fb, registry, module)?;
                self.require(sv.ty, LlvmType::I8Ptr, name)?;
                let iv = self.emit_expr(i, fb, registry, module)?;
                let iv = self.emit_numeric_cast(iv, LlvmType::I64, fb)?;
                let addr = fb.fresh_temp();
                fb.line(format!(
                    "{addr} = getelementptr i8, ptr {}, i64 {}",
                    sv.reg, iv.reg
                ));
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = load i8, ptr {addr}"));
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I8,
                }))
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
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I8Ptr,
                }))
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
                    None => {
                        if name.ends_with("pred") {
                            "-1".into()
                        } else {
                            "1".into()
                        }
                    }
                };
                let off = fb.fresh_temp();
                fb.line(format!("{off} = mul i64 {step}, {width}"));
                let reg = fb.fresh_temp();
                fb.line(format!(
                    "{reg} = getelementptr i8, ptr {}, i64 {off}",
                    pv.reg
                ));
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
                fb.line(format!(
                    "{reg} = load {}, ptr {}",
                    llvm_ty_str(elem),
                    pv.reg
                ));
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
                // A target type that cannot be named here is still a
                // cast that moves no bits.  This happens inside a
                // template *hole*, whose body is inlined rather than
                // monomorphised and so may still mention the enclosing
                // template's type variables; the value's own type is
                // then the honest answer, and it is the right one,
                // because the cast never changed it.
                match ty_args.first().and_then(|t| llvm_type_in(t, registry).ok()) {
                    Some(want) if want != v.ty => {
                        let reinterpreted = FnValue {
                            reg: v.reg.clone(),
                            ty: want,
                        };
                        // A numeric conversion is a real instruction; a
                        // cast between two pointer-shaped types is not.
                        Ok(Some(
                            self.emit_numeric_cast(v, want, fb).unwrap_or(reinterpreted),
                        ))
                    }
                    _ => Ok(Some(v)),
                }
            }
            // `double(n)`, `int2double(n)` — a number as a float, and
            // back.
            "double"
            | "int2double"
            | "g0int2float"
            | "g1int2float"
            | "double_of_int"
            | "g0int2float_int_double"
            | "g1int2float_int_double"
            | "g0i2f"
            | "g1i2f" => {
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
                    return Ok(Some(FnValue {
                        reg,
                        ty: LlvmType::I64,
                    }));
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
                Ok(Some(FnValue {
                    reg: ptr,
                    ty: LlvmType::Tuple(registry.intern_tuple(vec![v.ty])),
                }))
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
            "g0int_add" | "g1int_add" | "g0int_sub" | "g1int_sub" | "g0int_mul" | "g1int_mul"
            | "g0int_div" | "g1int_div" | "g0int_mod" | "g1int_mod" | "g0int_nmod"
            | "g1int_nmod" | "g0int_ndiv" | "g1int_ndiv" => {
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
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I1,
                }))
            }
            // `fprint_val (out, x)` — the default of ATS's printing
            // protocol, for the types the compiler already knows how to
            // write.  A program supplies its own instances, and one of
            // those wins over this: monomorphisation only leaves the
            // call here when nothing was supplied.
            "fprint_val" | "print_val" | "prerr_val" => {
                let (stream, value) = match (name, args) {
                    ("fprint_val", [out, x]) => (
                        self.emit_stream_argument(name, out, fb, registry, module)?,
                        x,
                    ),
                    ("print_val", [x]) => (Stream::Stdout, x),
                    ("prerr_val", [x]) => (Stream::Stderr, x),
                    _ => {
                        return Err(CompileError::emit(format!(
                            "`{name}` takes a value to print"
                        )));
                    }
                };
                self.emit_format(
                    &stream,
                    std::slice::from_ref(value),
                    false,
                    fb,
                    registry,
                    module,
                )?;
                Ok(Some(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Void,
                }))
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
                Ok(Some(FnValue {
                    reg: ptr,
                    ty: LlvmType::I8Ptr,
                }))
            }
            // Lemmas are proofs.  They say something the type checker
            // needed to hear and nothing the machine does.
            "lemma_list_param"
            | "lemma_list_vt_param"
            | "lemma_array_param"
            | "lemma_g1uint_param"
            | "lemma_g1int_param" => Ok(Some(FnValue {
                reg: String::new(),
                ty: LlvmType::Void,
            })),
            "mfree_gc" | "free_gc" | "mfree" => {
                for a in args {
                    self.emit_expr(a, fb, registry, module)?;
                }
                Ok(Some(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Void,
                }))
            }
            // `fgets (buf, n, filr)` — a line into the caller's buffer,
            // or null at end of input.
            "fgets" => {
                let [buf, n, filr] = args else {
                    return Err(CompileError::emit(
                        "`fgets` takes a buffer, a size and a stream",
                    ));
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
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I8Ptr,
                }))
            }
            "fputs" | "fputs_exn" => {
                let [s, filr] = args else {
                    return Err(CompileError::emit(format!(
                        "`{name}` takes a string and a stream"
                    )));
                };
                let sv = self.emit_expr(s, fb, registry, module)?;
                self.require(sv.ty, LlvmType::I8Ptr, name)?;
                let stream = self.emit_stream_argument(name, filr, fb, registry, module)?;
                self.emit_printf(stream, "%s", &[format!("ptr {}", sv.reg)], fb, module);
                Ok(Some(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Void,
                }))
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
                        Ok(Some(FnValue {
                            reg,
                            ty: LlvmType::F64,
                        }))
                    }
                    "rand" | "random" => {
                        module.externs.insert("declare i32 @rand()");
                        let raw = fb.fresh_temp();
                        let reg = fb.fresh_temp();
                        fb.line(format!("{raw} = call i32 @rand()"));
                        fb.line(format!("{reg} = sext i32 {raw} to i64"));
                        Ok(Some(FnValue {
                            reg,
                            ty: LlvmType::I64,
                        }))
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
                        Ok(Some(FnValue {
                            reg: String::new(),
                            ty: LlvmType::Void,
                        }))
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
                    return Err(CompileError::emit(format!(
                        "`{name}` compares two values of one type"
                    )));
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
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I64,
                }))
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
                fb.line(format!(
                    "{reg} = select i1 {c}, i64 {}, i64 {}",
                    av.reg, bv.reg
                ));
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I64,
                }))
            }
            // `succ`/`pred` — one more, one less.  ATS uses them
            // wherever a *static* index must move by exactly one, so
            // they appear far more often than `+ 1` does.
            "succ" | "pred" | "isucc" | "ipred" | "succ1" | "pred1" | "g1int_succ"
            | "g1int_pred" => {
                let [x] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one number")));
                };
                let v = self.emit_expr(x, fb, registry, module)?;
                self.require(v.ty, LlvmType::I64, name)?;
                let op = if name.contains("succ") { "add" } else { "sub" };
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = {op} i64 {}, 1", v.reg));
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I64,
                }))
            }
            // The character classifications.  Emitted as comparisons
            // rather than calls to libc's: `isdigit` and friends are
            // locale-dependent there, and ATS's are not.
            "isdigit" | "isalpha" | "isalnum" | "isspace" | "isupper" | "islower" | "ispunct"
            | "isxdigit" | "char_isdigit" | "char_isalpha" | "char_isspace" => {
                let [c] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one character")));
                };
                let v = self.emit_expr(c, fb, registry, module)?;
                let c = self.emit_numeric_cast(v, LlvmType::I64, fb)?;
                let reg = self.emit_char_class(name.trim_start_matches("char_"), &c.reg, fb);
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I1,
                }))
            }
            "toupper" | "tolower" | "char_toupper" | "char_tolower" => {
                let [c] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one character")));
                };
                let v = self.emit_expr(c, fb, registry, module)?;
                let (lo, hi, delta) = if name.ends_with("upper") {
                    ('a', 'z', -32)
                } else {
                    ('A', 'Z', 32)
                };
                let ge = fb.fresh_temp();
                fb.line(format!("{ge} = icmp sge i8 {}, {}", v.reg, lo as u8));
                let le = fb.fresh_temp();
                fb.line(format!("{le} = icmp sle i8 {}, {}", v.reg, hi as u8));
                let both = fb.fresh_temp();
                fb.line(format!("{both} = and i1 {ge}, {le}"));
                let shifted = fb.fresh_temp();
                fb.line(format!("{shifted} = add i8 {}, {delta}", v.reg));
                let reg = fb.fresh_temp();
                fb.line(format!(
                    "{reg} = select i1 {both}, i8 {shifted}, i8 {}",
                    v.reg
                ));
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I8,
                }))
            }
            // `arrayptr_make_intrange(lo, hi)` — the cells `lo..hi-1`.
            "arrayptr_make_intrange" | "arrayref_make_intrange" => {
                let lo = self.emit_expr(&args[0], fb, registry, module)?;
                let hi = self.emit_expr(&args[1], fb, registry, module)?;
                let n = fb.fresh_temp();
                fb.line(format!("{n} = sub i64 {}, {}", hi.reg, lo.reg));
                let ptr = self.emit_alloc_dynamic(&n, fb, module);
                self.emit_fill_intrange(&ptr, &lo.reg, &n, fb);
                Ok(Some(FnValue {
                    reg: ptr,
                    ty: LlvmType::Array(registry.intern_array(LlvmType::I64)),
                }))
            }
            // The arena owns every cell and outlives every program, so
            // freeing is a promise already kept.
            "arrayptr_free" | "array_ptr_free" | "arrayptr_addback" | "arrayref_free" => {
                for a in args {
                    self.emit_expr(a, fb, registry, module)?;
                }
                Ok(Some(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Void,
                }))
            }
            // `fprint_tupval2<a,b>(out, @(x, y))` — print a tuple.  The
            // arity is in the name because ATS has no variadic template,
            // but the *shape* is in the value, so one arm serves them
            // all: the format is read off the tuple's own components.
            name if name.starts_with("fprint_tupval") => {
                let Some((first, rest)) = args.split_first() else {
                    return Err(CompileError::emit(format!(
                        "`{name}` takes a stream and a tuple"
                    )));
                };
                let [tuple] = rest else {
                    return Err(CompileError::emit(format!(
                        "`{name}` takes a stream and a tuple"
                    )));
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
                Ok(Some(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Void,
                }))
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
                self.emit_printf(
                    Stream::Stderr,
                    &format!("exit(ATS): uncaught {name}\n"),
                    &[],
                    fb,
                    module,
                );
                fb.line("call void @exit(i32 1)");
                // `unreachable` terminates the block, exactly as `exit`
                // does.  No label follows: a raise is the end of its
                // block, and an empty block after it would have no
                // terminator of its own.
                fb.line("unreachable");
                Ok(Some(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Never,
                }))
            }
            // `$delay(e)` — suspend `e`.  The parser has already wrapped
            // the body in a nullary lambda, because suspending is what a
            // lambda does; what is built here is the one thing a lambda
            // cannot express, the cell that remembers the answer.
            "$delay" => {
                let [thunk] = args else {
                    return Err(CompileError::emit(
                        "`$delay` suspends exactly one expression",
                    ));
                };
                let f = self.emit_expr(thunk, fb, registry, module)?;
                let LlvmType::Closure(index) = f.ty else {
                    return Err(CompileError::emit(
                        "internal: `$delay` was not given a thunk",
                    ));
                };
                let sig = registry.closure_sig(index);
                if !sig.params.is_empty() {
                    return Err(CompileError::emit(
                        "internal: a delayed thunk takes no arguments",
                    ));
                }
                let cell = self.emit_alloc(WORD * 2, fb, module);
                fb.line(format!("store ptr {}, ptr {cell}", f.reg));
                let answer = self.emit_slot_address(&cell, 1, fb);
                fb.line(format!("store ptr null, ptr {answer}"));
                Ok(Some(FnValue {
                    reg: cell,
                    ty: LlvmType::Lazy(registry.intern_lazy(sig.ret)),
                }))
            }
            // Handing out the pointer inside an `arrayptr`, and taking it
            // back, are proof steps: the value does not move.
            "arrayptr_takeout_viewptr"
            | "arrayptr_takeout"
            | "arrayptr2ptr"
            | "arrayptr_refize"
            | "ptr2arrayptr"
            | "ptrcast"
            | "arrayptr_addback"
            | "list_vt2t"
            | "list_t2vt"
            | "unsafe_cast"
            | "ignoret"
            | "g0ofg1_list"
            | "list2list_vt"
            | "list_vt2list" => {
                let v = self.emit_expr(&args[0], fb, registry, module)?;
                Ok(Some(v))
            }
            // The integer conversions ATS uses to move between its signed
            // and unsigned *static* sorts.  One machine word throughout.
            "g1i2u" | "g0i2u" | "g1int2uint" | "g0int2uint" | "g1u2i" | "g0u2i" | "g1uint2int"
            | "g0uint2int" | "i2sz" | "sz2i" | "g1i2sz" | "g0i2sz" | "sz2u" | "u2sz" | "g1sz2i"
            | "g0sz2i" => {
                let v = self.emit_expr(&args[0], fb, registry, module)?;
                Ok(Some(v))
            }
            // `gnumber_int<t>(n)` — the number `n` as a `t`.  ATS uses it
            // to write a literal in code that is generic over the numeric
            // type, which is exactly what a template body cannot do.
            "gnumber_int" | "gnumber_int_int" => {
                let [n] = args else {
                    return Err(CompileError::emit("`gnumber_int` takes one int"));
                };
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
            "gmul_int_val" | "gadd_int_val" | "gsub_int_val" | "gdiv_int_val" | "gmul_val_int"
            | "gadd_val_int" | "gsub_val_int" | "gdiv_val_int" => {
                let [l, r] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes two arguments")));
                };
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
            "ggt_val_int" | "glt_val_int" | "gge_val_int" | "gle_val_int" | "geq_val_int"
            | "gneq_val_int" => {
                let [l, r] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes two arguments")));
                };
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
            "g1ofg0" | "g0ofg1" | "g1int2int" | "g0int2int" | "int2int" | "g1ofg0_int"
            | "g0ofg1_int" => {
                let [arg] = args else {
                    return Err(CompileError::emit(format!(
                        "`{name}` takes exactly one argument"
                    )));
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
                Ok(Some(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Never,
                }))
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
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I64,
                }))
            }
            "fileref_putc" | "fileref_put_char" => {
                let [f, c] = args else {
                    return Err(CompileError::emit(
                        "`fileref_putc` takes a stream and a character",
                    ));
                };
                let fv = self.emit_expr(f, fb, registry, module)?;
                self.require(fv.ty, LlvmType::FileRef, "`fileref_putc`")?;
                let cv = self.emit_expr(c, fb, registry, module)?;
                self.require(cv.ty, LlvmType::I64, "`fileref_putc`")?;
                module.externs.insert("declare i32 @fputc(i32, ptr)");
                let narrowed = fb.fresh_temp();
                fb.line(format!("{narrowed} = trunc i64 {} to i32", cv.reg));
                let reg = fb.fresh_temp();
                fb.line(format!(
                    "{reg} = call i32 @fputc(i32 {narrowed}, ptr {})",
                    fv.reg
                ));
                Ok(Some(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Void,
                }))
            }
            "fileref_open_exn" | "fileref_open" => {
                let [path, mode] = args else {
                    return Err(CompileError::emit(
                        "`fileref_open_exn` takes a path and a mode",
                    ));
                };
                let pv = self.emit_expr(path, fb, registry, module)?;
                self.require(
                    pv.ty,
                    LlvmType::I8Ptr,
                    "the path given to `fileref_open_exn`",
                )?;
                let mv = self.emit_expr(mode, fb, registry, module)?;
                self.require(
                    mv.ty,
                    LlvmType::I8Ptr,
                    "the mode given to `fileref_open_exn`",
                )?;
                module.externs.insert("declare ptr @fopen(ptr, ptr)");
                let reg = fb.fresh_temp();
                fb.line(format!(
                    "{reg} = call ptr @fopen(ptr {}, ptr {})",
                    pv.reg, mv.reg
                ));
                // The `_exn` spelling promises to raise rather than return
                // a null stream, so the check belongs here.
                let id = fb.fresh_block_id();
                let (bad, ok) = (format!("open.fail.{id}"), format!("open.ok.{id}"));
                let failed = fb.fresh_temp();
                fb.line(format!("{failed} = icmp eq ptr {reg}, null"));
                fb.line(format!("br i1 {failed}, label %{bad}, label %{ok}"));
                fb.label(&bad);
                self.emit_printf(
                    Stream::Stderr,
                    "exit(ATS): cannot open the file\n",
                    &[],
                    fb,
                    module,
                );
                fb.line("call void @exit(i32 1)");
                fb.line("unreachable");
                fb.label(&ok);
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::FileRef,
                }))
            }
            // `fileref_load<t>(f, x)` reads one value *into* `x`, so `x`
            // must be a `var` — a cell with an address — rather than a
            // `val`, which is a value with none.
            "fileref_load" | "fileref_load_int" => {
                let [f, target] = args else {
                    return Err(CompileError::emit(
                        "`fileref_load` takes a stream and a destination",
                    ));
                };
                let fv = self.emit_expr(f, fb, registry, module)?;
                self.require(fv.ty, LlvmType::FileRef, "`fileref_load`")?;
                let Expr::Var(name) = target else {
                    return Err(CompileError::emit(
                        "`fileref_load` must be given a `var` to read into",
                    ));
                };
                let Some(cell) = fb.cells.get(name).cloned() else {
                    return Err(CompileError::emit(format!(
                        "`fileref_load` reads into `{name}`, so it must be declared with `var`, not `val`"
                    )));
                };
                if cell.ty != LlvmType::I64 {
                    return Err(CompileError::emit(
                        "`fileref_load` can only read an int so far",
                    ));
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
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I1,
                }))
            }
            "string_is_null" => {
                let [x] = args else {
                    return Err(CompileError::emit("`string_is_null` takes one string"));
                };
                let v = self.emit_expr(x, fb, registry, module)?;
                self.require(v.ty, LlvmType::I8Ptr, "`string_is_null`")?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = icmp eq ptr {}, null", v.reg));
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I1,
                }))
            }
            // Read one line into the arena, without its newline.  A null
            // result means the stream had nothing left.
            //
            // It is built a character at a time rather than with
            // `getline`, which would allocate with `malloc` and leave the
            // caller holding memory nothing in the subset can free.  The
            // arena has no such problem.
            "fileref_get_line_string" | "fileref_get_line" => {
                let [f] = args else {
                    return Err(CompileError::emit(
                        "`fileref_get_line_string` takes one stream",
                    ));
                };
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
                fb.line(format!(
                    "{off} = phi i64 [ {start}, %{entry} ], [ {next_off}, %{store} ]",
                    next_off = format!("%t.next.{id}")
                ));
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
                fb.line(format!(
                    "{ended} = phi i64 [ {off}, %{body} ], [ {off}, %{done} ], [ {off}, %{empty} ]"
                ));
                let was_empty = fb.fresh_temp();
                fb.line(format!("{was_empty} = phi i1 [ false, %{body} ], [ false, %{done} ], [ true, %{empty} ]"));
                // Terminate the string and hand the arena back its space.
                let term = fb.fresh_temp();
                fb.line(format!(
                    "{term} = getelementptr i8, ptr @.heap, i64 {ended}"
                ));
                fb.line(format!("store i8 0, ptr {term}"));
                let after = fb.fresh_temp();
                fb.line(format!("{after} = add i64 {ended}, 1"));
                fb.line(format!("store i64 {after}, ptr @.heap.off"));
                let text = fb.fresh_temp();
                fb.line(format!(
                    "{text} = getelementptr i8, ptr @.heap, i64 {start}"
                ));
                let reg = fb.fresh_temp();
                fb.line(format!(
                    "{reg} = select i1 {was_empty}, ptr null, ptr {text}"
                ));
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I8Ptr,
                }))
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
                Ok(Some(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Void,
                }))
            }
            // --- the print shims, and characters ----------------------
            "print_char" | "prerr_char" => {
                let [c] = args else {
                    return Err(CompileError::emit("`print_char` takes one character"));
                };
                let v = self.emit_expr(c, fb, registry, module)?;
                self.require(v.ty, LlvmType::I8, "`print_char`")?;
                let stream = if name.starts_with("prerr") {
                    Stream::Stderr
                } else {
                    Stream::Stdout
                };
                let widened = fb.fresh_temp();
                fb.line(format!("{widened} = sext i8 {} to i32", v.reg));
                self.emit_printf(stream, "%c", &[format!("i32 {widened}")], fb, module);
                Ok(Some(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Void,
                }))
            }
            "print_int" | "print_string" | "print_bool" | "prerr_int" | "prerr_string" => {
                let [x] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one argument")));
                };
                let stream = if name.starts_with("prerr") {
                    Stream::Stderr
                } else {
                    Stream::Stdout
                };
                self.emit_format(
                    &stream,
                    std::slice::from_ref(x),
                    false,
                    fb,
                    registry,
                    module,
                )?;
                Ok(Some(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Void,
                }))
            }
            "print_newline" | "prerr_newline" => {
                let stream = if name.starts_with("prerr") {
                    Stream::Stderr
                } else {
                    Stream::Stdout
                };
                self.emit_printf(stream, "\n", &[], fb, module);
                Ok(Some(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Void,
                }))
            }
            // The same, to a stream the caller names.
            "fprint_newline" => {
                let [out] = args else {
                    return Err(CompileError::emit("`fprint_newline` takes one stream"));
                };
                let stream = self.emit_stream_argument(name, out, fb, registry, module)?;
                self.emit_printf(stream, "\n", &[], fb, module);
                Ok(Some(FnValue {
                    reg: String::new(),
                    ty: LlvmType::Void,
                }))
            }
            "g0int2float_double" | "int2float" | "i2d" => {
                let [n] = args else {
                    return Err(CompileError::emit("`int2double` takes one int"));
                };
                let v = self.emit_expr(n, fb, registry, module)?;
                self.require(v.ty, LlvmType::I64, "`int2double`")?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = sitofp i64 {} to double", v.reg));
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::F64,
                }))
            }
            "d2i" => {
                let [x] = args else {
                    return Err(CompileError::emit("`double2int` takes one double"));
                };
                let v = self.emit_expr(x, fb, registry, module)?;
                self.require(v.ty, LlvmType::F64, "`double2int`")?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = fptosi double {} to i64", v.reg));
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I64,
                }))
            }
            "char2int" | "char2int0" | "c2i" => {
                let [c] = args else {
                    return Err(CompileError::emit("`char2int` takes one character"));
                };
                let v = self.emit_expr(c, fb, registry, module)?;
                self.require(v.ty, LlvmType::I8, "`char2int`")?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = sext i8 {} to i64", v.reg));
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I64,
                }))
            }
            "int2char" | "int2char0" | "i2c" => {
                let [n] = args else {
                    return Err(CompileError::emit("`int2char` takes one int"));
                };
                let v = self.emit_expr(n, fb, registry, module)?;
                self.require(v.ty, LlvmType::I64, "`int2char`")?;
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = trunc i64 {} to i8", v.reg));
                Ok(Some(FnValue {
                    reg,
                    ty: LlvmType::I8,
                }))
            }
            "g0string2int" | "g0string2int_int" | "g1string2int" | "string2int" | "atoi" => {
                Ok(Some(self.emit_libc_shim(
                    name,
                    "atoi",
                    "declare i64 @atoi(ptr)",
                    LlvmType::I8Ptr,
                    LlvmType::I64,
                    args,
                    fb,
                    registry,
                    module,
                )?))
            }
            "string_length" | "string0_length" | "string1_length" | "strlen" => {
                Ok(Some(self.emit_libc_shim(
                    name,
                    "strlen",
                    "declare i64 @strlen(ptr)",
                    LlvmType::I8Ptr,
                    LlvmType::I64,
                    args,
                    fb,
                    registry,
                    module,
                )?))
            }
            // `string_append (s, t)` — a *third* string.  ATS strings are
            // NUL-terminated bytes somebody else owns, so joining two
            // means asking the arena for room and copying both in: there
            // is nowhere else for the result to live, and writing into
            // either argument would be writing into a constant.
            "string_append" | "string_append1" | "string0_append" | "strcat" => {
                let [first, second] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes two strings")));
                };
                let a = self.emit_string_arg(first, name, fb, registry, module)?;
                let b = self.emit_string_arg(second, name, fb, registry, module)?;
                let na = self.emit_strlen(&a, fb, module);
                let nb = self.emit_strlen(&b, fb, module);
                let total = fb.fresh_temp();
                fb.line(format!("{total} = add i64 {na}, {nb}"));
                let room = fb.fresh_temp();
                fb.line(format!("{room} = add i64 {total}, 1"));
                let out = self.emit_alloc_bytes(&room, fb, module);
                self.emit_memcpy(&out, &a, &na, fb, module);
                let tail = fb.fresh_temp();
                fb.line(format!("{tail} = getelementptr i8, ptr {out}, i64 {na}"));
                // One more byte than `b` is long: that is its terminator,
                // and it becomes the result's.
                let with_nul = fb.fresh_temp();
                fb.line(format!("{with_nul} = add i64 {nb}, 1"));
                self.emit_memcpy(&tail, &b, &with_nul, fb, module);
                Ok(Some(FnValue {
                    reg: out,
                    ty: LlvmType::I8Ptr,
                }))
            }
            // `string_make_substring (s, start, len)` — `len` bytes from
            // `start`.  The copy is terminated here rather than carried
            // over: a substring ends where it is told to, not where the
            // string it came from did.
            "string_make_substring" | "substring" | "string_substring" => {
                let [subject, start, len] = args else {
                    return Err(CompileError::emit(format!(
                        "`{name}` takes a string, a start and a length"
                    )));
                };
                let s = self.emit_string_arg(subject, name, fb, registry, module)?;
                let from = self.emit_expr(start, fb, registry, module)?;
                let from = self.emit_numeric_cast(from, LlvmType::I64, fb)?;
                let count = self.emit_expr(len, fb, registry, module)?;
                let count = self.emit_numeric_cast(count, LlvmType::I64, fb)?;
                let room = fb.fresh_temp();
                fb.line(format!("{room} = add i64 {}, 1", count.reg));
                let out = self.emit_alloc_bytes(&room, fb, module);
                let src = fb.fresh_temp();
                fb.line(format!(
                    "{src} = getelementptr i8, ptr {s}, i64 {}",
                    from.reg
                ));
                self.emit_memcpy(&out, &src, &count.reg, fb, module);
                let end = fb.fresh_temp();
                fb.line(format!(
                    "{end} = getelementptr i8, ptr {out}, i64 {}",
                    count.reg
                ));
                fb.line(format!("store i8 0, ptr {end}"));
                Ok(Some(FnValue {
                    reg: out,
                    ty: LlvmType::I8Ptr,
                }))
            }
            _ => Ok(None),
        }
    }

    /// Widen a number to the numeric type asked for.
    pub(crate) fn emit_numeric_cast(
        &self,
        v: FnValue,
        want: LlvmType,
        fb: &mut FnBuilder,
    ) -> Result<FnValue, CompileError> {
        if v.ty == want {
            return Ok(v);
        }
        match (v.ty, want) {
            (LlvmType::I64, LlvmType::F64) => {
                // A literal converts at compile time: `gnumber_int<double>(1)`
                // should read as the constant it is, not as a conversion
                // the reader has to perform in their head.
                if let Ok(n) = v.reg.parse::<i64>() {
                    return Ok(FnValue {
                        reg: format!("{:.1}", n as f64),
                        ty: LlvmType::F64,
                    });
                }
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = sitofp i64 {} to double", v.reg));
                Ok(FnValue {
                    reg,
                    ty: LlvmType::F64,
                })
            }
            // A character *is* a small integer in ATS: `c - '0'` is
            // arithmetic, not a conversion the programmer writes.
            (LlvmType::I8, LlvmType::I64) => {
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = sext i8 {} to i64", v.reg));
                Ok(FnValue {
                    reg,
                    ty: LlvmType::I64,
                })
            }
            (LlvmType::I64, LlvmType::I8) => {
                let reg = fb.fresh_temp();
                fb.line(format!("{reg} = trunc i64 {} to i8", v.reg));
                Ok(FnValue {
                    reg,
                    ty: LlvmType::I8,
                })
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
    pub(crate) fn emit_promoted(
        &self,
        op: BinOp,
        lv: FnValue,
        rv: FnValue,
        fb: &mut FnBuilder,
    ) -> Result<FnValue, CompileError> {
        let want = if lv.ty == LlvmType::F64 || rv.ty == LlvmType::F64 {
            LlvmType::F64
        } else {
            LlvmType::I64
        };
        let lv = self.emit_numeric_cast(lv, want, fb)?;
        let rv = self.emit_numeric_cast(rv, want, fb)?;
        self.emit_binop_values(op, lv, rv, fb)
    }

    /// One-argument shims that are a call to a libc function.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn emit_libc_shim(
        &self,
        ats_name: &str,
        c_name: &str,
        decl: &'static str,
        want: LlvmType,
        ret: LlvmType,
        args: &[Expr],
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
        let [arg] = args else {
            return Err(CompileError::emit(format!(
                "`{ats_name}` takes exactly one argument"
            )));
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
        fb.line(format!(
            "{reg} = call {} @{c_name}({} {})",
            llvm_ty_str(ret),
            llvm_ty_str(want),
            v.reg
        ));
        Ok(FnValue { reg, ty: ret })
    }

    /// Reserve `bytes` from the arena, returning the pointer.
    ///
    /// Overflow is checked rather than assumed: running out of arena ends
    /// the program with a message, which is a far better failure than
    /// quietly writing past the buffer.
    pub(crate) fn emit_alloc(&self, bytes: usize, fb: &mut FnBuilder, module: &mut ModuleBuilder) -> String {
        self.emit_alloc_bytes(&bytes.to_string(), fb, module)
    }

    /// As `emit_alloc`, but for a size only known at run time.
    /// An argument that must be a string, emitted and checked.
    pub(crate) fn emit_string_arg(
        &self,
        e: &Expr,
        of: &str,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<String, CompileError> {
        let v = self.emit_expr(e, fb, registry, module)?;
        self.require(v.ty, LlvmType::I8Ptr, of)?;
        Ok(v.reg)
    }

    /// How long a NUL-terminated string is.
    pub(crate) fn emit_strlen(&self, s: &str, fb: &mut FnBuilder, module: &mut ModuleBuilder) -> String {
        module.externs.insert("declare i64 @strlen(ptr)");
        let n = fb.fresh_temp();
        fb.line(format!("{n} = call i64 @strlen(ptr {s})"));
        n
    }

    /// `count` bytes from `src` to `dst`.
    pub(crate) fn emit_memcpy(
        &self,
        dst: &str,
        src: &str,
        count: &str,
        fb: &mut FnBuilder,
        module: &mut ModuleBuilder,
    ) {
        module.externs.insert("declare ptr @memcpy(ptr, ptr, i64)");
        let done = fb.fresh_temp();
        fb.line(format!(
            "{done} = call ptr @memcpy(ptr {dst}, ptr {src}, i64 {count})"
        ));
    }

    pub(crate) fn emit_alloc_bytes(
        &self,
        bytes: &str,
        fb: &mut FnBuilder,
        module: &mut ModuleBuilder,
    ) -> String {
        module.needs_heap = true;
        module.externs.insert("declare ptr @malloc(i64)");
        module.externs.insert("declare void @free(ptr)");
        let ptr = fb.fresh_temp();
        fb.line(format!("{ptr} = call ptr @.ats_alloc(i64 {bytes})"));
        ptr
    }

    /// Build a datatype value: one allocation, the tag, then the fields.
    pub(crate) fn emit_ctor(
        &self,
        name: &str,
        info: &CtorInfo,
        args: &[Expr],
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
                values.push(FnValue {
                    reg: zero_literal(*want).to_string(),
                    ty: *want,
                });
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
        Ok(self.emit_ctor_from_values(info, &values, fb, module))
    }

    /// Build a datatype value from field values already in registers.
    ///
    /// Split out of `emit_ctor` so that a shim standing in for a library
    /// routine can build one too: it has the fields as values rather
    /// than as expressions, and there is nothing else different about
    /// the record it needs.
    pub(crate) fn emit_ctor_from_values(
        &self,
        info: &CtorInfo,
        values: &[FnValue],
        fb: &mut FnBuilder,
        module: &mut ModuleBuilder,
    ) -> FnValue {
        let ptr = self.emit_alloc(WORD * (1 + info.width), fb, module);
        fb.line(format!("store i64 {}, ptr {ptr}", info.tag));
        for (i, v) in values.iter().enumerate() {
            let addr = self.emit_field_address(&ptr, i, fb);
            fb.line(format!("store {} {}, ptr {addr}", llvm_ty_str(v.ty), v.reg));
        }
        FnValue {
            reg: ptr,
            ty: LlvmType::Data(info.datatype),
        }
    }

    /// The address of field `i` of a datatype value: past the tag, then
    /// `i` words in.
    pub(crate) fn emit_field_address(&self, base: &str, i: usize, fb: &mut FnBuilder) -> String {
        self.emit_slot_address(base, i + 1, fb)
    }

    /// The address of word `i` of a record.  A tuple has no tag, so its
    /// first component is word zero.
    pub(crate) fn emit_slot_address(&self, base: &str, i: usize, fb: &mut FnBuilder) -> String {
        if i == 0 {
            return base.to_string();
        }
        let addr = fb.fresh_temp();
        fb.line(format!(
            "{addr} = getelementptr i8, ptr {base}, i64 {}",
            WORD * i
        ));
        addr
    }
}
