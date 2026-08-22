use super::emitter::LlvmIrEmitter;
use super::types::*;
use ats2_domain::ast::*;
use ats2_domain::errors::CompileError;
use ats2_domain::tokens::*;
use std::collections::{HashMap, HashSet};

pub(crate) struct ModuleBuilder {
    pub(crate) lines: Vec<String>,
    pub(crate) strings: Vec<String>,
    pub(crate) formats: Vec<String>,
    pub(crate) string_index: HashMap<String, usize>,
    /// Storage for the program's top-level values.
    pub(crate) globals: Vec<String>,
    /// The libc functions a shim reached for, declared only if used.
    pub(crate) externs: std::collections::BTreeSet<&'static str>,
    /// Whether anything in the program allocates, and so needs the arena.
    pub(crate) needs_heap: bool,
    /// Whether the program raises or catches, and so needs the exception
    /// runtime (setjmp/longjmp and a thrown-value cell).
    pub(crate) needs_exn: bool,
    /// How many lambdas have been given names.
    pub(crate) lambdas: usize,
}

impl ModuleBuilder {
    pub(crate) fn new() -> Self {
        Self {
            lines: Vec::new(),
            strings: Vec::new(),
            formats: Vec::new(),
            string_index: HashMap::new(),
            globals: Vec::new(),
            externs: std::collections::BTreeSet::new(),
            needs_heap: false,
            needs_exn: false,
            lambdas: 0,
        }
    }

    /// A fresh name for a lifted lambda body.
    pub(crate) fn next_lambda(&mut self) -> usize {
        let id = self.lambdas;
        self.lambdas += 1;
        id
    }

    pub(crate) fn add_string(&mut self, s: &str) -> String {
        if let Some(&i) = self.string_index.get(s) {
            return format!("@.str.{i}");
        }
        let i = self.strings.len();
        self.strings.push(s.to_string());
        self.string_index.insert(s.to_string(), i);
        format!("@.str.{i}")
    }

    pub(crate) fn add_format(&mut self, f: &str) -> String {
        let i = self.formats.len();
        self.formats.push(f.to_string());
        format!("@.fmt.{i}")
    }

    pub(crate) fn render(&self) -> String {
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
        if self.needs_exn {
            // The current exception frame and the raised value, shared
            // between every `try` and `$raise`.
            out.push_str("@ats2_cur = internal global ptr null\n");
            out.push_str("@ats2_exval = internal global ptr null\n");
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
            out.push_str(&format!(
                "@.heap = internal global [{HEAP_BYTES} x i8] zeroinitializer\n"
            ));
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
            out.push_str(&format!(
                "@.str.{i} = private unnamed_addr constant [{len} x i8] c\"{}\\00\"\n",
                llvm_escape(s)
            ));
        }
        for (i, f) in self.formats.iter().enumerate() {
            let len = f.len() + 1;
            out.push_str(&format!(
                "@.fmt.{i} = private unnamed_addr constant [{len} x i8] c\"{}\\00\"\n",
                llvm_escape(f)
            ));
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
pub(crate) struct FnBuilder {
    pub(crate) lines: Vec<String>,
    pub(crate) temps: usize,
    pub(crate) block_ids: usize,
    pub(crate) env: HashMap<String, FnValue>,
    /// The label of the block instructions are landing in right now.
    ///
    /// A `phi` must name the block control *actually* arrived from, which
    /// is not necessarily the block a branch started in: if the branch
    /// contains its own `if`, the arm ends in that inner merge block.
    /// Tracking the open block is what makes nested conditionals — the
    /// shape every recursive ATS function has — come out correct.
    pub(crate) cur_block: String,
    /// The `var` cells in scope: name → the pointer holding it.
    ///
    /// A cell is looked up before the SSA environment, so a `var` shadows
    /// a `val` of the same name exactly as the source says it should.
    pub(crate) cells: HashMap<String, Cell>,
    /// The exit label of each enclosing loop, innermost last.
    ///
    /// `$break` needs to know where to go, and only the loop knows.
    /// Keeping a stack rather than a single label is what makes a
    /// `$break` inside a nested loop leave the *inner* one, which is
    /// what every language with the construct means by it.
    pub(crate) loop_exits: Vec<String>,
    /// Every `alloca`, collected separately from the instruction stream.
    ///
    /// LLVM permits an `alloca` anywhere, but one that sits inside a loop
    /// body allocates afresh on every turn and grows the stack without
    /// bound.  Hoisting them all into the entry block is the standard
    /// remedy and costs nothing: the storage a function needs is known
    /// once, on entry.
    pub(crate) allocas: Vec<String>,
}

/// A `var` cell: the pointer its storage lives behind, and the type of
/// the value inside it.
#[derive(Debug, Clone)]
pub(crate) struct Cell {
    pub(crate) ptr: String,
    pub(crate) ty: LlvmType,
}

impl FnBuilder {
    pub(crate) fn new() -> Self {
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
    pub(crate) fn alloca(&mut self, name: &str, ty: LlvmType) -> String {
        let mut ptr = format!("%{}.cell", sanitize(name));
        let mut k = 0;
        while self
            .allocas
            .iter()
            .any(|a| a.starts_with(&format!("{ptr} ")))
        {
            k += 1;
            ptr = format!("%{}.cell.{k}", sanitize(name));
        }
        self.allocas
            .push(format!("{ptr} = alloca {}", llvm_ty_str(ty)));
        ptr
    }

    /// Open a new basic block, and remember that it is now the open one.
    pub(crate) fn label(&mut self, name: &str) {
        self.lines.push(format!("{name}:"));
        self.cur_block = name.to_string();
    }

    pub(crate) fn line(&mut self, s: impl Into<String>) {
        self.lines.push(s.into());
    }

    pub(crate) fn fresh_temp(&mut self) -> String {
        let r = format!("%t.{}", self.temps);
        self.temps += 1;
        r
    }

    /// One id shared by the whole branch trio of a construct.
    pub(crate) fn fresh_block_id(&mut self) -> usize {
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
pub(crate) fn push_line(text: &mut String, line: &str) {
    if is_label(line) {
        text.push('\n');
    } else {
        text.push_str("\n  ");
    }
    text.push_str(line);
}

/// Whether an emitted line opens a basic block rather than doing work.
pub(crate) fn is_label(line: &str) -> bool {
    line.ends_with(':') && !line.contains(char::is_whitespace)
}

/// Emit one `fun` definition as an LLVM function.
pub(crate) fn emit_function(
    f: &ats2_domain::ast::FunDef,
    registry: &Registry,
    module: &mut ModuleBuilder,
) -> Result<(), CompileError> {
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
    let value =
        LlvmIrEmitter.emit_expr_expecting(&f.body, Some(sig.ret), &mut fb, registry, module)?;
    if value.ty != sig.ret && sig.ret != LlvmType::Void && value.ty != LlvmType::Never {
        let help = if sig.ret == LlvmType::I8Ptr {
            format!(" (did you forget the return type annotation `: <type>` before `=` in `fun {}(...): <type> = ...`?)", f.name)
        } else {
            String::new()
        };
        return Err(CompileError::emit(format!(
            "function `{}` body has type {}, annotation says {}{}",
            f.name,
            llvm_ty_str(value.ty),
            llvm_ty_str(sig.ret),
            help
        )));
    }
    let params: Vec<String> = f
        .params
        .iter()
        .zip(&sig.params)
        .enumerate()
        .map(|(i, (p, ty))| {
            let ty = if is_by_ref(i) {
                "ptr"
            } else {
                llvm_ty_str(*ty)
            };
            format!("{ty} %{}", sanitize(&p.name))
        })
        .collect();
    let mut text = format!(
        "define {} @{}({}) {{",
        llvm_ty_str(sig.ret),
        sanitize(&f.name),
        params.join(", ")
    );
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
pub(crate) fn ret_instruction(ret: LlvmType, value: &FnValue) -> String {
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
pub(crate) fn emit_main(
    im: &ats2_domain::ast::ImplementDef,
    inits: &[&ats2_domain::ast::ValDef],
    registry: &Registry,
    module: &mut ModuleBuilder,
) -> Result<(), CompileError> {
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
        let value =
            LlvmIrEmitter.emit_expr_expecting(&v.value, Some(ty), &mut fb, registry, module)?;
        if value.ty != ty {
            return Err(CompileError::emit(format!(
                "`{}` is declared as {} but its value is {}",
                v.name,
                llvm_ty_str(ty),
                llvm_ty_str(value.ty)
            )));
        }
        fb.line(format!(
            "store {} {}, ptr @{}",
            llvm_ty_str(ty),
            value.reg,
            sanitize(&v.name)
        ));
    }
    // C hands `main` an `i32` argument count; every `int` in the subset is
    // an `i64`, so the count is widened once on entry and the ATS name is
    // bound to the widened value.
    let takes_argv = im.params.len() == 2;
    if takes_argv {
        fb.env.insert(
            im.params[0].name.clone(),
            FnValue {
                reg: format!("%{}", sanitize(&im.params[0].name)),
                ty: LlvmType::I64,
            },
        );
        fb.env.insert(
            im.params[1].name.clone(),
            FnValue {
                reg: format!("%{}", sanitize(&im.params[1].name)),
                ty: LlvmType::Argv,
            },
        );
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

