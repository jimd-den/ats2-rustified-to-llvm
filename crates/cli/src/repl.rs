//! # ats2repl — interactive ATS2 REPL shell
//!
//! Evaluates ATS2 expressions and statements on the fly via LLVM IR JIT / host execution,
//! maintains persistent, transactional language sessions, supports multi-line inputs,
//! and provides an optional Socratic AI mentor (via OpenRouter) that critiques and coaches
//! without writing code for the user.

use std::io::{self, BufRead, Write};
use std::path::Path;

use ats2_application::checking::Strictness;
use ats2_application::ports::{AdvisorContext, AdvisorPort};
use ats2_application::use_cases::repl_session::{ReplResponse, ReplSession};
use ats2_domain::errors::CompileError;
use ats2_infrastructure::advisor::OpenRouterAdvisor;
use ats2_infrastructure::llvm_ir::LlvmIrEmitter;
use ats2_infrastructure::parser::Parser;
use ats2_infrastructure::runner::HostRunner;

const BANNER: &str = "\
============================================================
  ats2repl — ATS2 Interactive REPL (Rustified to LLVM)
============================================================
  💡 Think in ATS2: Commit to your static types & invariants first!
     1. Separate Statics (sorts, proofs, erased) from Dynamics (runtime code)
     2. Commit to signatures & pre/post-conditions BEFORE writing the body
     3. Track resources linearly with views

  • Type `:teach` to explore interactive lessons on Thinking in ATS2
  • Type `:commit <signature>` to formulate and check a spec first
  • Type `:explain` or `:ask <q>` for Socratic mentor guidance (via OpenRouter)
  • Type `:help` for available commands, `:quit` to exit
";

const HELP_TEXT: &str = "\
ats2repl commands:
  :help, :h             Show this help text
  :teach, :lesson [1-5] Interactive lessons on Thinking in ATS2 & Commit-First
  :commit <signature>   Commit & check a type specification before implementing
  :type <expr>, :t      Inspect the type of an expression
  :ir                   Display generated LLVM IR for current session
  :source, :s           Display accumulated session source code
  :load <file>, :l      Load and execute an ATS2 source file (.dats / .sats)
  :strict               Enable strict verification mode
  :permissive           Enable permissive verification mode
  :reset, :clear, :r    Reset the session environment
  :quit, :exit, :q      Exit the REPL

Socratic Mentor (OpenRouter) commands:
  :explain, :why        Ask mentor to explain the last error or concept Socratically
  :ask <question>       Ask mentor any conceptual ATS2 question
  :critique             Ask mentor to critique the current session's code
  :mentor on|off        Toggle automatic coaching on compiler errors
  :model <name>         Switch OpenRouter model (default: openrouter/auto)

Thinking in ATS2 (Commit-First) examples:
  ats2> :teach 1
  ats2> :commit fun fact{n:nat}(n: int(n)): int
  ats2> val x = 42
  ats2> fun double(n: int): int = n * 2
  ats2> double(x)
";

const TEACH_GUIDE: &str = "\
╔══════════════════════════════════════════════════════════════════════════╗
║               THINKING IN ATS2 — COMMIT FIRST TUTORIAL                   ║
╚══════════════════════════════════════════════════════════════════════════╝
ATS2 separates verification from runtime computation:
  1. The Static Layer: Sorts, Props, and Invariants (erased at runtime)
  2. The Dynamic Layer: Expressions and LLVM Execution (computes at runtime)

Choose a lesson to begin (:teach <1-5>):
  :teach 1   -> Static vs Dynamic Divide & Return Annotations
  :teach 2   -> Refinement Sorts & Quantifiers ({n:nat})
  :teach 3   -> Commit-First: Specification Before Implementation
  :teach 4   -> Theorem Proving & Termination Metrics (<n>)
  :teach 5   -> Linear Types & Zero-Cost Resource Views (view@L)
";

pub mod line_reader;
use line_reader::LineReader;

pub fn run_repl<R: BufRead, W: Write>(input: R, output: W) -> io::Result<()> {
    let advisor = OpenRouterAdvisor::new();
    run_repl_with_advisor(input, output, advisor)
}

pub fn run_repl_with_advisor<R: BufRead, W: Write, A: AdvisorPort>(
    mut input: R,
    mut output: W,
    mut advisor: A,
) -> io::Result<()> {
    let parser = Parser;
    let emitter = LlvmIrEmitter;
    let runner = HostRunner;
    let mut session = ReplSession::new(parser, emitter, runner, Strictness::default());
    let mut line_reader = LineReader::new();

    let mut auto_mentor = false;
    let mut last_submission = String::new();
    let mut last_errors = Vec::new();

    writeln!(output, "{BANNER}")?;
    output.flush()?;

    let mut buffer = String::new();

    loop {
        let prompt = if buffer.is_empty() {
            "ats2> "
        } else {
            " ...> "
        };

        let line_opt = line_reader.read_line(prompt, &mut input, &mut output)?;
        let line = match line_opt {
            Some(l) => l,
            None => {
                writeln!(output, "Goodbye!")?;
                break;
            }
        };

        let trimmed = line.trim_end();

        // Empty line while in multi-line continuation forces submission of accumulated buffer
        let force_submit = trimmed.is_empty() && !buffer.is_empty();

        // Handle single-line commands only when not in multi-line continuation
        if buffer.is_empty() && trimmed.starts_with(':') {
            if trimmed == ":quit" || trimmed == ":exit" || trimmed == ":q" {
                writeln!(output, "Goodbye!")?;
                break;
            }
            handle_command(
                trimmed,
                &mut session,
                &mut advisor,
                &mut auto_mentor,
                &last_submission,
                &last_errors,
                &mut output,
            )?;
            continue;
        }

        // Check for line continuation or open blocks
        buffer.push_str(trimmed);
        buffer.push('\n');

        if force_submit || is_input_complete(&buffer) {
            let submission = buffer.trim();
            if !submission.is_empty() {
                last_submission = submission.to_string();
                last_errors.clear();

                evaluate_submission(
                    submission,
                    &mut session,
                    &advisor,
                    auto_mentor,
                    &mut last_errors,
                    &mut output,
                )?;
            }
            buffer.clear();
        }
    }

    Ok(())
}

fn handle_command<W: Write, A: AdvisorPort>(
    cmd: &str,
    session: &mut ReplSession<Parser, LlvmIrEmitter, HostRunner>,
    advisor: &mut A,
    auto_mentor: &mut bool,
    last_submission: &str,
    last_errors: &[CompileError],
    output: &mut W,
) -> io::Result<()> {
    let mut parts = cmd.splitn(2, char::is_whitespace);
    let name = parts.next().unwrap_or("");
    let arg = parts.next().map(str::trim).unwrap_or("");

    match name {
        ":help" | ":h" => {
            writeln!(output, "{HELP_TEXT}")?;
        }
        ":teach" | ":lesson" => {
            handle_teach_command(arg, output)?;
        }
        ":commit" => {
            handle_commit_command(arg, session, advisor, output)?;
        }
        ":reset" | ":clear" | ":r" => {
            session.reset();
            writeln!(output, "Session reset: environment cleared.")?;
        }
        ":source" | ":s" => {
            let src = session.source();
            if src.is_empty() {
                writeln!(output, "(no definitions in current session)")?;
            } else {
                writeln!(output, "--- Current Session Source ---")?;
                writeln!(output, "{src}")?;
                writeln!(output, "------------------------------")?;
            }
        }
        ":ir" => match session.emit_ir() {
            Ok(ir) => {
                writeln!(output, "--- Emitted LLVM IR ---")?;
                writeln!(output, "{ir}")?;
                writeln!(output, "-----------------------")?;
            }
            Err(e) => {
                writeln!(output, "error emitting IR: {e}")?;
            }
        },
        ":strict" => {
            session.set_strictness(Strictness::Strict);
            writeln!(output, "Strict verification mode enabled.")?;
        }
        ":permissive" => {
            session.set_strictness(Strictness::Permissive);
            writeln!(output, "Permissive verification mode enabled.")?;
        }
        ":type" | ":t" => {
            if arg.is_empty() {
                writeln!(output, "Usage: :type <expression>")?;
            } else {
                match session.type_of(arg) {
                    Ok(ty) => writeln!(output, "type: {ty}")?,
                    Err(errors) => report_errors(&errors, output)?,
                }
            }
        }
        ":load" | ":l" => {
            if arg.is_empty() {
                writeln!(output, "Usage: :load <path>")?;
            } else {
                load_file(arg, session, output)?;
            }
        }
        ":mentor" => match arg {
            "on" => {
                *auto_mentor = true;
                writeln!(output, "Automatic mentor feedback on errors ENABLED.")?;
            }
            "off" => {
                *auto_mentor = false;
                writeln!(output, "Automatic mentor feedback on errors DISABLED.")?;
            }
            _ => {
                writeln!(output, "Usage: :mentor on | :mentor off")?;
            }
        },
        ":explain" | ":why" => {
            if last_submission.is_empty() && last_errors.is_empty() {
                writeln!(output, "(no recent submission or error to explain)")?;
            } else {
                writeln!(output, "[Consulting Socratic Mentor via OpenRouter...]")?;
                output.flush()?;

                let ctx = AdvisorContext {
                    session_source: session.source(),
                    last_submission,
                    last_errors,
                    user_query: if arg.is_empty() { None } else { Some(arg) },
                };

                match advisor.advise(&ctx) {
                    Ok(advice) => {
                        writeln!(output, "\n💡 Mentor Guidance:\n{advice}\n")?;
                    }
                    Err(err) => {
                        writeln!(output, "Mentor unavailable: {err}")?;
                    }
                }
            }
        }
        ":ask" => {
            if arg.is_empty() {
                writeln!(output, "Usage: :ask <question>")?;
            } else {
                writeln!(output, "[Consulting Socratic Mentor via OpenRouter...]")?;
                output.flush()?;

                let ctx = AdvisorContext {
                    session_source: session.source(),
                    last_submission,
                    last_errors,
                    user_query: Some(arg),
                };

                match advisor.advise(&ctx) {
                    Ok(advice) => {
                        writeln!(output, "\n💡 Mentor Answer:\n{advice}\n")?;
                    }
                    Err(err) => {
                        writeln!(output, "Mentor unavailable: {err}")?;
                    }
                }
            }
        }
        ":critique" => {
            if session.source().is_empty() && last_submission.is_empty() {
                writeln!(output, "(no code in session to critique)")?;
            } else {
                writeln!(output, "[Reviewing code with Socratic Mentor...]")?;
                output.flush()?;

                let ctx = AdvisorContext {
                    session_source: session.source(),
                    last_submission,
                    last_errors,
                    user_query: Some("Please review the session's code and types, point out any invariant subtleties or style improvements, but do not write code."),
                };

                match advisor.advise(&ctx) {
                    Ok(advice) => {
                        writeln!(output, "\n💡 Code Critique:\n{advice}\n")?;
                    }
                    Err(err) => {
                        writeln!(output, "Mentor unavailable: {err}")?;
                    }
                }
            }
        }
        ":model" => {
            if arg.is_empty() {
                writeln!(output, "Usage: :model <openrouter_model_name> (e.g. :model openrouter/auto)")?;
            } else {
                // Configurable via env var
                unsafe {
                    std::env::set_var("OPENROUTER_MODEL", arg);
                }
                writeln!(output, "OpenRouter model set to `{arg}`.")?;
            }
        }
        other => {
            writeln!(
                output,
                "Unknown command `{other}`. Type `:help` for available commands."
            )?;
        }
    }
    output.flush()?;
    Ok(())
}

fn load_file<W: Write>(
    path_str: &str,
    session: &mut ReplSession<Parser, LlvmIrEmitter, HostRunner>,
    output: &mut W,
) -> io::Result<()> {
    let path = Path::new(path_str);
    match std::fs::read_to_string(path) {
        Ok(content) => match session.load_source(&content) {
            Ok(update) => {
                writeln!(
                    output,
                    "Loaded `{path_str}`: +{} definitions ({} total).",
                    update.added_definitions, update.total_definitions
                )?;
            }
            Err(errors) => {
                writeln!(output, "Errors loading `{path_str}`:")?;
                report_errors(&errors, output)?;
            }
        },
        Err(e) => {
            writeln!(output, "Cannot read file `{path_str}`: {e}")?;
        }
    }
    Ok(())
}

fn evaluate_submission<W: Write, A: AdvisorPort>(
    snippet: &str,
    session: &mut ReplSession<Parser, LlvmIrEmitter, HostRunner>,
    advisor: &A,
    auto_mentor: bool,
    last_errors_out: &mut Vec<CompileError>,
    output: &mut W,
) -> io::Result<()> {
    match session.submit(snippet) {
        Ok(ReplResponse::Definition(update)) => {
            if update.added_definitions > 0 {
                writeln!(
                    output,
                    "[defined: +{} definition{}, {} total]",
                    update.added_definitions,
                    if update.added_definitions == 1 {
                        ""
                    } else {
                        "s"
                    },
                    update.total_definitions
                )?;
            } else {
                writeln!(
                    output,
                    "[checked: {} total definitions]",
                    update.total_definitions
                )?;
            }
        }
        Ok(ReplResponse::Evaluated(exec)) => {
            if !exec.stdout.is_empty() {
                write!(output, "{}", exec.stdout)?;
                if !exec.stdout.ends_with('\n') {
                    writeln!(output)?;
                }
            }
            if !exec.stderr.is_empty() {
                write!(output, "[stderr] {}", exec.stderr)?;
                if !exec.stderr.ends_with('\n') {
                    writeln!(output)?;
                }
            }
            if !exec.success && exec.exit_code != 0 {
                writeln!(output, "[process exited with code {}]", exec.exit_code)?;
            }
        }
        Err(errors) => {
            *last_errors_out = errors.clone();
            report_errors(&errors, output)?;

            if auto_mentor {
                let ctx = AdvisorContext {
                    session_source: session.source(),
                    last_submission: snippet,
                    last_errors: &errors,
                    user_query: None,
                };
                if let Ok(advice) = advisor.advise(&ctx) {
                    writeln!(output, "\n💡 Mentor Coaching:\n{advice}\n")?;
                }
            }
        }
    }
    output.flush()?;
    Ok(())
}

fn report_errors<W: Write>(errors: &[CompileError], output: &mut W) -> io::Result<()> {
    for err in errors {
        if let Some(span) = err.span() {
            writeln!(
                output,
                "error[{:?}] at {}:{}: {}",
                err.kind(),
                span.start.line,
                span.start.column,
                err.message()
            )?;
        } else {
            writeln!(output, "error[{:?}]: {}", err.kind(), err.message())?;
        }
    }
    Ok(())
}

/// Determines if an input buffer contains a balanced, complete ATS statement or expression.
pub fn is_input_complete(buffer: &str) -> bool {
    let trimmed = buffer.trim_end();
    if trimmed.ends_with('\\') {
        return false;
    }

    let mut parens = 0isize;
    let mut braces = 0isize;
    let mut brackets = 0isize;
    let mut in_string = false;
    let mut escaped = false;

    let chars: Vec<char> = trimmed.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        let c = chars[i];
        if in_string {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }

        match c {
            '"' => in_string = true,
            '(' => parens += 1,
            ')' => parens = parens.saturating_sub(1),
            '{' => braces += 1,
            '}' => braces = braces.saturating_sub(1),
            '[' => brackets += 1,
            ']' => brackets = brackets.saturating_sub(1),
            _ => {}
        }
        i += 1;
    }

    if in_string || parens > 0 || braces > 0 || brackets > 0 {
        return false;
    }

    // Heuristics for unclosed `let ... in ...` without `end`
    let count_let = count_word(trimmed, "let");
    let count_end = count_word(trimmed, "end");
    if count_let > count_end {
        return false;
    }

    true
}

fn count_word(text: &str, word: &str) -> usize {
    text.split(|c: char| !c.is_alphanumeric() && c != '_')
        .filter(|w| *w == word)
        .count()
}

fn handle_teach_command<W: Write>(arg: &str, output: &mut W) -> io::Result<()> {
    match arg {
        "1" | "basics" => {
            writeln!(output, "{}", "--- Lesson 1: Static vs Dynamic Divide & Return Annotations ---
In ATS2, code is split into two distinct worlds:
  1. The STATIC world: Types, sorts, props, and proofs. These are 100% erased
     at compile-time and incur ZERO runtime overhead.
  2. The DYNAMIC world: Values, functions, and effects that execute on LLVM.

Golden Rule for Writing Functions in ATS2:
  Every function header MUST specify an explicit return type `: <type>` before `=`,
  e.g.:
    fun add(a: int, b: int): int = a + b

  If you omit `: <type>`, ATS2 defaults the return type to `ptr`, causing
  type mismatch errors!

Try this in the REPL:
  ats2> fun square(x: int): int = x * x
  ats2> square(6)
")?;
        }
        "2" | "statics" | "sorts" => {
            writeln!(output, "{}", "--- Lesson 2: Refinement Sorts & Universal Quantifiers ---
In ATS2, static types can be indexed by static integers, booleans, and addresses!
  • `int(n)` is the singleton type representing the exact integer `n`.
  • `{n: nat}` or `{n: int | n >= 0}` quantifies over all non-negative static ints.

Example of Dependent Types:
  `fun is_even{n: int}(x: int(n)): bool(n % 2 == 0)`

Try this in the REPL:
  ats2> fun double{n: int}(x: int(n)): int(2 * n) = x * 2
  ats2> double(21)
")?;
        }
        "3" | "commit" | "commit-first" => {
            writeln!(output, "{}", "--- Lesson 3: Commit-First Thinking (Specification Before Code) ---
In ATS2, you design by committing to static properties BEFORE implementing bodies:
  Step 1: Write down your types, invariants, and function contracts (`:commit <sig>`).
  Step 2: Ask: 'What invariants must hold for all inputs?'
  Step 3: Implement the dynamic body to satisfy the static specification.

Example:
  ats2> :commit fun factorial{n: nat}(n: int(n)): [r: int | r >= 1] int(r)
  ats2> fun factorial{n: nat}(n: int(n)): int = if n == 0 then 1 else n * factorial(n - 1)
")?;
        }
        "4" | "proofs" | "termination" => {
            writeln!(output, "{}", "--- Lesson 4: Theorem Proving & Termination Metrics ---
ATS2 enforces total correctness:
  • Termination metrics: `<n>` guarantees recursion strictly decreases towards a base case.
  • Proof functions (`prfn`) and theorem witnesses (`prval`) allow constructing mathematical
    proofs that are completely erased during LLVM compilation!

Try this in the REPL:
  ats2> fun fib{n: nat}(n: int(n)): int = if n <= 1 then n else fib(n-1) + fib(n-2)
")?;
        }
        "5" | "views" | "linear" => {
            writeln!(output, "{}", "--- Lesson 5: Linear Types & Zero-Cost Resource Views ---
ATS2 linear types enable memory safety with NO garbage collector:
  • `view @ L`: Proof that memory at address `L` is currently owned.
  • `ptr(L)`: Pointer to address `L`.
  • Combining them: `(view @ L | ptr(L))` gives safe access to raw memory!
  • Resources MUST be consumed or freed exactly once (no leaks, no use-after-free).
")?;
        }
        _ => {
            writeln!(output, "{TEACH_GUIDE}")?;
        }
    }
    Ok(())
}

fn handle_commit_command<W: Write, A: AdvisorPort>(
    spec: &str,
    session: &mut ReplSession<Parser, LlvmIrEmitter, HostRunner>,
    advisor: &A,
    output: &mut W,
) -> io::Result<()> {
    if spec.is_empty() {
        writeln!(output, "Usage: :commit <function signature or type declaration>
Example: :commit fun fact{{n: nat}}(n: int(n)): int")?;
        return Ok(());
    }

    writeln!(output, "🔍 Analyzing type commitment / specification:
  `{spec}`
")?;

    if (spec.starts_with("fun ") || spec.starts_with("fn ")) && !spec.contains(':') {
        writeln!(output, "⚠️  Warning: Missing return type annotation!
   In ATS2, function headers require an explicit `: <type>` before `=`. Without it, ATS2 defaults to `ptr`.
")?;
    }

    if spec.contains('{') && spec.contains('}') {
        writeln!(output, "✅ Universal static quantifier detected (e.g. `{{n: nat}}`).")?;
        writeln!(output, "   Static properties will be fully verified and erased at runtime.")?;
    }

    let ctx = AdvisorContext {
        session_source: session.source(),
        last_submission: spec,
        last_errors: &[],
        user_query: Some("The user is committing to this type signature / specification first before writing the body. Please briefly evaluate this signature Socratically: what invariants does it guarantee, and what edge cases should they think about when implementing the body? (Do NOT write the code)."),
    };

    if let Ok(advice) = advisor.advise(&ctx) {
        writeln!(output, "
💡 Socratic Feedback on Commitment:
{advice}")?;
    } else {
        writeln!(output, "Ready to implement! Now enter the function body matching this specification.")?;
    }

    Ok(())
}

fn main() -> io::Result<()> {
    let stdin = io::stdin();
    let stdout = io::stdout();
    run_repl(stdin.lock(), stdout.lock())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    struct FakeTestAdvisor;

    impl AdvisorPort for FakeTestAdvisor {
        fn advise(&self, _context: &AdvisorContext) -> Result<String, String> {
            Ok("Notice the quantifier `{n: nat}` constraint.".into())
        }
    }

    #[test]
    fn input_completion_detects_unclosed_delimiters() {
        assert!(!is_input_complete("fun fact(n: int): int = ("));
        assert!(!is_input_complete("let val x = 1"));
        assert!(!is_input_complete("val x = \"unterminated string"));
        assert!(!is_input_complete("val x = 10 \\"));

        assert!(is_input_complete("1 + 2"));
        assert!(is_input_complete("let val x = 1 in x end"));
        assert!(is_input_complete("fun f(): int = 1"));
    }

    #[test]
    fn repl_processes_commands_and_expressions() {
        let input_data = ":help\n:source\nfun inc(x: int): int = x + 1\ninc(41)\n:quit\n";
        let input = Cursor::new(input_data);
        let mut output = Vec::new();

        let _ = run_repl_with_advisor(input, &mut output, FakeTestAdvisor);
        let out_str = String::from_utf8_lossy(&output);

        assert!(out_str.contains("ats2repl commands:"), "got:\n{out_str}");
        assert!(out_str.contains("[defined: +1 definition, 1 total]"), "got:\n{out_str}");
        assert!(out_str.contains("42"), "got:\n{out_str}");
    }

    #[test]
    fn repl_handles_mentor_commands() {
        let input_data = "fun bad_fn(x: int): int = x\n:explain\n:ask how does linearity work?\n:critique\n:quit\n";
        let input = Cursor::new(input_data);
        let mut output = Vec::new();

        let _ = run_repl_with_advisor(input, &mut output, FakeTestAdvisor);
        let out_str = String::from_utf8_lossy(&output);

        assert!(out_str.contains("Mentor Guidance:"), "got:\n{out_str}");
        assert!(out_str.contains("Mentor Answer:"), "got:\n{out_str}");
        assert!(out_str.contains("Code Critique:"), "got:\n{out_str}");
        assert!(out_str.contains("quantifier `{n: nat}`"), "got:\n{out_str}");
    }

    #[test]
    fn repl_handles_teach_and_commit_commands() {
        let input_data = ":teach\n:teach 1\n:teach 3\n:commit fun fact{n: nat}(n: int(n)): int\n:quit\n";
        let input = Cursor::new(input_data);
        let mut output = Vec::new();

        let _ = run_repl_with_advisor(input, &mut output, FakeTestAdvisor);
        let out_str = String::from_utf8_lossy(&output);

        assert!(out_str.contains("THINKING IN ATS2 — COMMIT FIRST TUTORIAL"), "got:\n{out_str}");
        assert!(out_str.contains("Lesson 1: Static vs Dynamic Divide"), "got:\n{out_str}");
        assert!(out_str.contains("Lesson 3: Commit-First Thinking"), "got:\n{out_str}");
        assert!(out_str.contains("Analyzing type commitment / specification:"), "got:\n{out_str}");
        assert!(out_str.contains("Universal static quantifier detected"), "got:\n{out_str}");
    }
}
