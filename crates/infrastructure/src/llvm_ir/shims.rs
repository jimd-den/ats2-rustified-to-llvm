use super::builder::*;
use super::emitter::*;
use super::types::*;
use ats2_domain::ast::*;
use ats2_domain::errors::CompileError;

impl LlvmIrEmitter {
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
            | "g1int_nmod" | "g0int_ndiv" | "g1int_ndiv" | "g0float_add" | "g1float_add"
            | "g0float_sub" | "g1float_sub" | "g0float_mul" | "g1float_mul" | "g0float_div"
            | "g1float_div" | "g0double_add" | "g0double_sub" | "g0double_mul" | "g0double_div" => {
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
            "g0int_lt" | "g1int_lt" | "g0int_lte" | "g1int_lte" | "g0int_gt" | "g1int_gt"
            | "g0int_gte" | "g1int_gte" | "g0int_eq" | "g1int_eq" | "g0int_neq" | "g1int_neq"
            | "g0float_lt" | "g1float_lt" | "g0float_lte" | "g1float_lte" | "g0float_gt"
            | "g1float_gt" | "g0float_gte" | "g1float_gte" | "g0float_eq" | "g1float_eq"
            | "g0float_neq" | "g1float_neq" | "g0double_lt" | "g0double_lte" | "g0double_gt"
            | "g0double_gte" | "g0double_eq" | "g0double_neq" | "lt_int_int" => {
                let [a, b] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes two values")));
                };
                let op = if name.ends_with("_lt") || name.ends_with("lt_int_int") {
                    BinOp::Lt
                } else if name.ends_with("_lte") {
                    BinOp::Le
                } else if name.ends_with("_gt") {
                    BinOp::Gt
                } else if name.ends_with("_gte") {
                    BinOp::Ge
                } else if name.ends_with("_eq") {
                    BinOp::Eq
                } else {
                    BinOp::Ne
                };
                Ok(Some(self.emit_binop(op, a, b, fb, registry, module)?))
            }
            "print" | "println" => {
                let [x] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one value")));
                };
                self.emit_format(
                    &Stream::Stdout,
                    std::slice::from_ref(x),
                    name == "println",
                    fb,
                    registry,
                    module,
                )?;
                Ok(Some(FnValue {
                    reg: "".into(),
                    ty: LlvmType::Void,
                }))
            }
            "g0i2i" | "g1i2i" | "cast2size" | "c2uc" => {
                let [x] = args else {
                    return Err(CompileError::emit(format!("`{name}` takes one value")));
                };
                let v = self.emit_expr(x, fb, registry, module)?;
                Ok(Some(v))
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
}
