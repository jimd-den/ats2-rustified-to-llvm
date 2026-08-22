use super::builder::*;
use super::emitter::LlvmIrEmitter;
use super::types::*;
use ats2_domain::ast::*;
use ats2_domain::errors::CompileError;
use ats2_domain::tokens::*;
use std::collections::{HashMap, HashSet};

impl LlvmIrEmitter {
    pub(crate) fn emit_case(
        &self,
        scrutinee: &Expr,
        arms: &[(Pattern, Expr)],
        expected: Option<LlvmType>,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
            let settled =
                expected.or_else(|| results.first().map(|(v, _): &(FnValue, String)| v.ty));
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
                self.emit_printf(
                    Stream::Stderr,
                    "exit(ATS): no matching case\n",
                    &[],
                    fb,
                    module,
                );
                fb.line("call void @exit(i32 2)");
                fb.line("unreachable");
            }
        }

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
                    "case arms have different types ({} vs {})",
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
    pub(crate) fn emit_pattern_match(
        &self,
        pattern: &Pattern,
        value: &FnValue,
        on_fail: &str,
        fb: &mut FnBuilder,
        registry: &Registry,
    ) -> Result<(), CompileError> {
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
    pub(crate) fn emit_pattern_match_at(
        &self,
        pattern: &Pattern,
        value: &FnValue,
        on_fail: &str,
        in_place: bool,
        fb: &mut FnBuilder,
        registry: &Registry,
    ) -> Result<(), CompileError> {
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
                    self.emit_pattern_match_at(
                        sub,
                        &FnValue { reg, ty },
                        on_fail,
                        in_place,
                        fb,
                        registry,
                    )?;
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
                let Some(info) = registry.ctors[name]
                    .iter()
                    .find(|c| c.datatype == index)
                    .cloned()
                else {
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
                    self.emit_pattern_match_at(
                        sub,
                        &FnValue { reg, ty },
                        on_fail,
                        in_place,
                        fb,
                        registry,
                    )?;
                }
                Ok(())
            }
        }
    }

    /// Continue when `cond` holds, and leave for `on_fail` when it does
    /// not.  The continuation gets a block of its own, which is what
    /// keeps the tests after it from running too early.
    pub(crate) fn emit_guard(&self, cond: &str, on_fail: &str, fb: &mut FnBuilder) {
        let id = fb.fresh_block_id();
        let ok = format!("pat.ok.{id}");
        fb.line(format!("br i1 {cond}, label %{ok}, label %{on_fail}"));
        fb.label(&ok);
    }

    /// Insist that a value has the type a construct requires.
    pub(crate) fn require(&self, got: LlvmType, want: LlvmType, what: &str) -> Result<(), CompileError> {
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
    pub(crate) fn emit_lambda(
        &self,
        params: &[Param],
        ret: Option<&Ty>,
        body: &Expr,
        expected: Option<LlvmType>,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
                fb.line(format!(
                    "{reg} = load {}, ptr {}",
                    llvm_ty_str(cell.ty),
                    cell.ptr
                ));
                captures.push((name, FnValue { reg, ty: cell.ty }));
            }
        }

        // Emit the body as its own function, in its own builder.
        let id = module.next_lambda();
        let fname = format!("lam.{id}");
        let mut inner = FnBuilder::new();
        for (p, ty) in params.iter().zip(&param_tys) {
            inner.env.insert(
                p.name.clone(),
                FnValue {
                    reg: format!("%{}", sanitize(&p.name)),
                    ty: *ty,
                },
            );
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

        // The record: the code, then everything it captured.  A lambda
        // that captured nothing has the same record every time it is
        // evaluated, so it gets one, in read-only memory: no allocation,
        // and — because the code pointer now lives somewhere that
        // provably never changes — a call through it is one LLVM knows
        // how to turn back into a direct call, and then to inline.
        let ptr = if captures.is_empty() {
            module.globals.push(format!(
                "@clos.{id} = private unnamed_addr constant ptr @{fname}"
            ));
            format!("@clos.{id}")
        } else {
            let ptr = self.emit_alloc(WORD * (1 + captures.len()), fb, module);
            fb.line(format!("store ptr @{fname}, ptr {ptr}"));
            for (i, (_, v)) in captures.iter().enumerate() {
                let addr = self.emit_slot_address(&ptr, i + 1, fb);
                fb.line(format!("store {} {}, ptr {addr}", llvm_ty_str(v.ty), v.reg));
            }
            ptr
        };
        let index = registry.intern_closure(FnSig {
            params: param_tys,
            ret: ret_ty,
        });
        Ok(FnValue {
            reg: ptr,
            ty: LlvmType::Closure(index),
        })
    }

    /// Call a closure: load the code out of the record and jump through
    /// it, handing the record itself back as the environment.
    pub(crate) fn emit_closure_call(
        &self,
        callee: FnValue,
        args: &[Expr],
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
            return Ok(FnValue {
                reg: String::new(),
                ty: LlvmType::Void,
            });
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
    pub(crate) fn emit_index(
        &self,
        base: &Expr,
        index: &Expr,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
        fb.line(format!(
            "{addr} = getelementptr ptr, ptr {}, i64 {}",
            b.reg, i.reg
        ));
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = load ptr, ptr {addr}"));
        Ok(FnValue {
            reg,
            ty: LlvmType::I8Ptr,
        })
    }

    /// `c >= lo && c <= hi`, possibly several ranges joined by `or`.
    pub(crate) fn emit_char_class(&self, class: &str, c: &str, fb: &mut FnBuilder) -> String {
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
    pub(crate) fn require_hole(
        &self,
        name: &str,
        registry: &Registry,
    ) -> Result<ats2_domain::ast::ImplementDef, CompileError> {
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
    pub(crate) fn inline_hole(
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
    pub(crate) fn emit_alloc_dynamic(
        &self,
        count: &str,
        fb: &mut FnBuilder,
        module: &mut ModuleBuilder,
    ) -> String {
        let bytes = fb.fresh_temp();
        fb.line(format!("{bytes} = mul i64 {count}, {WORD}"));
        self.emit_alloc_bytes(&bytes, fb, module)
    }

    /// Write one value into every cell of a fresh array.
    pub(crate) fn emit_fill(&self, ptr: &str, count: &str, value: &FnValue, fb: &mut FnBuilder) {
        let id = fb.fresh_block_id();
        let (head, body, done) = (
            format!("fill.head.{id}"),
            format!("fill.body.{id}"),
            format!("fill.done.{id}"),
        );
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
        fb.line(format!(
            "store {} {}, ptr {addr}",
            llvm_ty_str(value.ty),
            value.reg
        ));
        let next = fb.fresh_temp();
        fb.line(format!("{next} = add i64 {i}, 1"));
        fb.line(format!("store i64 {next}, ptr {cell}"));
        fb.line(format!("br label %{head}"));
        fb.label(&done);
    }

    /// Fill an array with `lo, lo+1, ...`.
    pub(crate) fn emit_fill_intrange(&self, ptr: &str, lo: &str, count: &str, fb: &mut FnBuilder) {
        let id = fb.fresh_block_id();
        let (head, body, done) = (
            format!("range.head.{id}"),
            format!("range.body.{id}"),
            format!("range.done.{id}"),
        );
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
    pub(crate) fn emit_proj(
        &self,
        base: &Expr,
        slot: usize,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
    pub(crate) fn emit_deref(
        &self,
        inner: &Expr,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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

    /// The nil and cons of the prelude list whose elements are `elem`.
    ///
    /// Found by the element type rather than by name, because the name
    /// is the mangled one monomorphisation invented and only the type is
    /// stable.  `None` when no such instance exists — nothing in the
    /// program built that list, so there is nothing to build one with.
    pub(crate) fn list_constructors(
        &self,
        elem: LlvmType,
        registry: &Registry,
    ) -> Option<(CtorInfo, CtorInfo)> {
        let cons = registry
            .ctors
            .get("list0_cons")?
            .iter()
            .find(|c| c.fields.first() == Some(&elem))?
            .clone();
        let nil = registry
            .ctors
            .get("list0_nil")?
            .iter()
            .find(|c| c.datatype == cons.datatype)?
            .clone();
        Some((nil, cons))
    }

    /// What a list of this datatype holds, if it is a list at all.
    ///
    /// Every instance of the prelude's `list0` declares the same two
    /// constructors; what separates one instance from another is the
    /// type of the element, which is exactly what printing one needs.
    pub(crate) fn list_element(&self, datatype: usize, registry: &Registry) -> Option<LlvmType> {
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
    pub(crate) fn emit_list_print(
        &self,
        stream: &Stream,
        list: &FnValue,
        datatype: usize,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<(), CompileError> {
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
        fb.line(format!(
            "{value} = load {}, ptr {addr}",
            llvm_ty_str(element)
        ));
        let mut fmt = String::new();
        let mut operands = Vec::new();
        self.format_one(
            stream,
            FnValue {
                reg: value,
                ty: element,
            },
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
    pub(crate) fn record_slot(
        &self,
        v: &FnValue,
        name: &str,
        registry: &Registry,
    ) -> Option<(usize, LlvmType)> {
        let LlvmType::Record(index) = v.ty else {
            return None;
        };
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
    pub(crate) fn type_without_emitting(
        &self,
        expr: &Expr,
        fb: &FnBuilder,
        registry: &Registry,
    ) -> Option<LlvmType> {
        match expr {
            Expr::Var(n) => fb
                .env
                .get(n)
                .map(|v| v.ty)
                .or_else(|| fb.cells.get(n).map(|c| c.ty))
                .or_else(|| registry.globals.get(n).copied()),
            Expr::Field(base, name) => {
                let base = self.type_without_emitting(base, fb, registry)?;
                let LlvmType::Record(index) = base else {
                    return None;
                };
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
    pub(crate) fn is_a_record_field(
        &self,
        base: &Expr,
        name: &str,
        fb: &FnBuilder,
        registry: &Registry,
    ) -> bool {
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
    pub(crate) fn emit_force(
        &self,
        cell: FnValue,
        index: usize,
        fb: &mut FnBuilder,
        registry: &Registry,
    ) -> Result<FnValue, CompileError> {
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
        fb.line(format!(
            "{value} = call {} {code}(ptr {thunk})",
            llvm_ty_str(forced)
        ));
        let answer = self.emit_slot_address(&cell.reg, 1, fb);
        fb.line(format!(
            "store {} {value}, ptr {answer}",
            llvm_ty_str(forced)
        ));
        fb.line(format!("store ptr null, ptr {}", cell.reg));
        fb.line(format!("br label %{done}"));

        fb.label(&done);
        let addr = self.emit_slot_address(&cell.reg, 1, fb);
        let reg = fb.fresh_temp();
        fb.line(format!("{reg} = load {}, ptr {addr}", llvm_ty_str(forced)));
        Ok(FnValue { reg, ty: forced })
    }

    /// `A.[i]` — one cell of an array.
    pub(crate) fn emit_array_index(
        &self,
        base: &FnValue,
        index: &Expr,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
    pub(crate) fn emit_cell_address(
        &self,
        base: &FnValue,
        index: &Expr,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<String, CompileError> {
        let i = self.emit_expr(index, fb, registry, module)?;
        self.require(i.ty, LlvmType::I64, "an array index")?;
        let byte = fb.fresh_temp();
        fb.line(format!("{byte} = mul i64 {}, {WORD}", i.reg));
        let addr = fb.fresh_temp();
        fb.line(format!(
            "{addr} = getelementptr i8, ptr {}, i64 {byte}",
            base.reg
        ));
        Ok(addr)
    }

    /// `xs.0 := e` — a store into a place the left-hand side computes.
    ///
    /// The place is evaluated for its *address*, so the value written is
    /// visible through every other name for the same aggregate.  That is
    /// what makes a tuple passed to a function mutable by it.
    pub(crate) fn emit_store(
        &self,
        place: &Expr,
        value: &Expr,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
            return Ok(FnValue {
                reg: String::new(),
                ty: LlvmType::Void,
            });
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
            return Ok(FnValue {
                reg: String::new(),
                ty: LlvmType::Void,
            });
        }
        let Expr::Proj(base, slot) = place else {
            return Err(CompileError::emit(
                "this is not something that can be assigned to",
            ));
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
        Ok(FnValue {
            reg: String::new(),
            ty: LlvmType::Void,
        })
    }

    /// `x := e` — a store into the cell `x` names.
    pub(crate) fn emit_assign(
        &self,
        name: &str,
        value: &Expr,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
        if !fb.cells.contains_key(name) {
            if registry.globals.contains_key(name) {
                return Err(CompileError::emit(format!(
                    "`{name}` is a top-level `val`, which never changes; it cannot be assigned to"
                )));
            }
            return Err(if fb.env.contains_key(name) {
                CompileError::emit(format!(
                    "`{name}` is bound by `val` and cannot be assigned to; declare it with `var`"
                ))
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
        fb.line(format!(
            "store {} {}, ptr {}",
            llvm_ty_str(v.ty),
            v.reg,
            cell.ptr
        ));
        Ok(FnValue {
            reg: String::new(),
            ty: LlvmType::Void,
        })
    }

    /// `while (cond) body`.
    ///
    /// The condition gets a block of its own.  That is not a stylistic
    /// choice: the instructions computing it must be re-executed on every
    /// turn, and instructions emitted into the entry block would run once.
    pub(crate) fn emit_while(
        &self,
        cond: &Expr,
        body: &Expr,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
        let id = fb.fresh_block_id();
        let (chead, cbody, cend) = (
            format!("while.cond.{id}"),
            format!("while.body.{id}"),
            format!("while.end.{id}"),
        );

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
        Ok(FnValue {
            reg: String::new(),
            ty: LlvmType::Void,
        })
    }

    /// `for (init; cond; step) body`.
    ///
    /// The step gets its own block rather than being appended to the body.
    /// Both lower to the same machine code, but keeping them apart means
    /// the loop's three parts are still legible in the IR — and it is
    /// where a `continue` would land if the subset ever grows one.
    pub(crate) fn emit_for(
        &self,
        init: &Expr,
        cond: &Expr,
        step: &Expr,
        body: &Expr,
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
        Ok(FnValue {
            reg: String::new(),
            ty: LlvmType::Void,
        })
    }

    /// `assertloc(cond)` — ATS's located assertion.  It is not a function
    /// call but a *branch*: on failure it reports where it stood and
    /// leaves through `exit(1)`, so the success path costs one test and a
    /// perfectly predicted jump.
    pub(crate) fn emit_assert(
        &self,
        args: &[Expr],
        fb: &mut FnBuilder,
        registry: &Registry,
        module: &mut ModuleBuilder,
    ) -> Result<FnValue, CompileError> {
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
        self.emit_printf(
            Stream::Stderr,
            "exit(ATS): assertion failed\n",
            &[],
            fb,
            module,
        );
        fb.line("call void @exit(i32 1)");
        fb.line("unreachable");
        fb.label(&ok);
        Ok(FnValue {
            reg: String::new(),
            ty: LlvmType::Void,
        })
    }
}

