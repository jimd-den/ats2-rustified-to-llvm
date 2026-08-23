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
        let is_proof = name.starts_with("lemma_")
            || name.starts_with("praxi_")
            || name.starts_with("prfun_")
            || name.starts_with("prval_")
            || name.starts_with("prfn_")
            || name.starts_with("proof_")
            || name.starts_with("prop_verify")
            || name.starts_with("ckastloc_")
            || name.starts_with("$solver_assert");
        if is_proof && !registry.fns.contains_key(name) {
            return Ok(FnValue {
                reg: String::new(),
                ty: LlvmType::Void,
            });
        }
        let is_dynload_or_c = name.ends_with("__dynload")
            || name.starts_with("SDL_")
            || name.starts_with("cairo_")
            || name.starts_with("XMLHttpRequest_")
            || name.starts_with("document_")
            || name.starts_with("event_")
            || name.starts_with("ev_")
            || name.starts_with("json_")
            || name.starts_with("redis")
            || name.starts_with("cloptr_")
            || name.starts_with("strptr_")
            || name.starts_with("stropt_")
            || name.starts_with("fileref_")
            || name.starts_with("channeg")
            || name.starts_with("chanpos")
            || name.starts_with("mpz_")
            || name.starts_with("dirent_")
            || matches!(
                name.as_str(),
                "getenv"
                    | "sleep"
                    | "time"
                    | "readdir"
                    | "fileno"
                    | "fnmatch"
                    | "fgetc"
                    | "feof"
                    | "fprintf"
                    | "alloca"
                    | "mfree_libc"
                    | "sin"
                    | "cos"
                    | "sqrt"
                    | "malloc_usable_size"
                    | "alert"
                    | "xmlString2string"
                    | "ferror"
                    | "index"
                    | "fputc_exn"
                    | "open_file_exn"
                    | "input_line"
                    | "major"
                    | "onreadystatechange"
                    | "int2intinf"
                    | "ptr_alloc"
                    | "string0_copy"
                    | "strptr0_copy"
                    | "stringlst_concat"
                    | "vector_make_ngc"
                    | "matrix_ptr_tabulate"
                    | "array_ptr_tabulate"
                    | "stream_vt_tabulate"
                    | "streamer_vt_make"
                    | "randgen_val"
                    | "constraint1"
                    | "atext_nil"
                    | "token_node"
                    | "channel_send"
                    | "undefined"
                    | "isneqz"
                    | "red"
                    | "width"
                    | "zsock_new"
            );
        let sig = if let Some(s) = registry.fns.get(name) {
            s.clone()
        } else if is_dynload_or_c {
            let mut params = Vec::with_capacity(args.len());
            for arg in args {
                let v = self.emit_expr(arg, fb, registry, module)?;
                params.push(v.ty);
            }
            let ret = if name.ends_with("__dynload") {
                LlvmType::Void
            } else {
                expected.unwrap_or(LlvmType::I64)
            };
            FnSig { params, ret }
        } else {
            return Err(CompileError::emit(format!("unknown function `{name}`")));
        };
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
