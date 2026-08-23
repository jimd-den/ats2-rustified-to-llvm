use super::builder::*;
use super::emitter::*;
use super::types::*;
use ats2_domain::ast::*;
use ats2_domain::errors::CompileError;

impl LlvmIrEmitter {
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

}

