//! # ats2-harness — compile every ATS file in a tree, and say where each stopped
//!
//! The corpus scorer asks of thirty-six files whether they compile and run.
//! This asks the same question of *every* `.dats` file in a tree — the whole
//! Postiats source, say — and answers two questions: at which stage each file
//! stopped, and which missing capability stopped the most files.  A file
//! that dies in the lexer is a different thing from one that dies in the
//! checker, but a list of five thousand unique diagnostics is not a roadmap
//! either.  Diagnostics are therefore assigned stable feature codes and
//! ranked by the number of files they affect.
//!
//! Stages, in order: parse → staload → check → linearity → emit.
//! `ir` means the file reached LLVM IR; every other name is where it
//! stopped.  Both a strict and a permissive pass are recorded, because
//! "cannot yet prove" (strict) and "cannot even lower" (permissive) are
//! two different gaps.
//!
//! ```text
//! ats2-harness [ROOT] [--dir DIR] [--limit N] [--workers N] [--top N] [--sats]
//! ```
//!
//! `ROOT` defaults to the `ATS-Postiats` checkout beside this workspace.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{mpsc, Arc};
use std::time::{Duration, Instant};

use ats2_application::checking::{check_program, Strictness};
use ats2_application::elaboration;
use ats2_application::linearity::check_linearity;
use ats2_application::modules;
use ats2_application::ports::ParserPort;
use ats2_domain::ast::Program;
use ats2_domain::errors::{CompileError, ErrorKind};
use ats2_infrastructure::llvm_ir::LlvmIrEmitter;
use ats2_infrastructure::parser::Parser;
use ats2_infrastructure::sources::FileSources;

/// Real Postiats units are substantially more recursive than the examples.
/// A generous virtual stack prevents one deep parse from aborting the process.
const COMPILE_STACK_BYTES: usize = 256 * 1024 * 1024;

/// One stop on the pipeline, or the far end of it.
///
/// The order is the pipeline order; `Timeout` sorts last and is kept out
/// of the cumulative ladder because it answers nothing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Stage {
    Read,
    Lex,
    Parse,
    Staload,
    Check,
    Linear,
    Emit,
    Ir,
    Timeout,
    Crash,
}

impl Stage {
    const REAL: [Stage; 7] = [
        Stage::Read,
        Stage::Lex,
        Stage::Parse,
        Stage::Staload,
        Stage::Check,
        Stage::Linear,
        Stage::Emit,
    ];

    fn label(self) -> &'static str {
        match self {
            Stage::Read => "read",
            Stage::Lex => "lex",
            Stage::Parse => "parse",
            Stage::Staload => "staload",
            Stage::Check => "check",
            Stage::Linear => "linearity",
            Stage::Emit => "emit",
            Stage::Ir => "ir",
            Stage::Timeout => "timeout",
            Stage::Crash => "crash",
        }
    }

    fn from_label(label: &str) -> Option<Self> {
        Some(match label {
            "read" => Stage::Read,
            "lex" => Stage::Lex,
            "parse" => Stage::Parse,
            "staload" => Stage::Staload,
            "check" => Stage::Check,
            "linearity" => Stage::Linear,
            "emit" => Stage::Emit,
            "ir" => Stage::Ir,
            "timeout" => Stage::Timeout,
            "crash" => Stage::Crash,
            _ => return None,
        })
    }
}

/// The result for one file under both checking policies.
struct Outcome {
    strict: Stage,
    permissive: Stage,
    message: String,
    /// Every independently observable failure, not merely the one that
    /// stopped the strict pipeline.  Once a program resolves, checking,
    /// linearity and emission can all be attempted and can all teach us
    /// something about work still to do.
    failures: Vec<Failure>,
}

#[derive(Debug, Clone)]
struct Failure {
    stage: Stage,
    /// `strict`, `permissive`, or `common` for passes shared by both.
    lane: &'static str,
    code: String,
    message: String,
}

impl Failure {
    fn from_error(error: &CompileError, lane: &'static str) -> Self {
        let stage = stage_of(error.kind());
        Self {
            stage,
            lane,
            code: feature_code(stage, error.message()),
            message: error.to_string(),
        }
    }

    fn target(stage: Stage, lane: &'static str, message: impl Into<String>) -> Self {
        let message = message.into();
        Self {
            stage,
            lane,
            code: feature_code(stage, &message),
            message,
        }
    }
}

/// Parse, resolve, check and lower one file.  The two policies share the
/// parse, the module walk, the linearity pass and the emission — only the
/// dependent check differs — so the work is done once and judged twice.
fn compile(path: &Path, distribution: &Path, prelude: &Program) -> Outcome {
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            let failure = Failure::target(Stage::Read, "common", e.to_string());
            return Outcome {
                strict: Stage::Read,
                permissive: Stage::Read,
                message: failure.message.clone(),
                failures: vec![failure],
            };
        }
    };

    let parsed = match Parser::parse(&source) {
        Ok(p) => p,
        Err(errs) => {
            let stage = stage_of(errs[0].kind());
            let failures = errs
                .iter()
                .map(|e| Failure::from_error(e, "common"))
                .collect();
            return Outcome {
                strict: stage,
                permissive: stage,
                message: errs[0].to_string(),
                failures,
            };
        }
    };

    let loader = FileSources::at(path).including_distribution(distribution);
    let modules = match modules::resolve_modules(parsed, &Parser, &loader) {
        Ok(p) => p,
        Err(errs) => {
            // A `staload` that names no file is a target error; anything
            // else here is a dependency that failed to parse.
            let stage = match errs[0].kind() {
                ErrorKind::Target => Stage::Staload,
                k => stage_of(k),
            };
            let failures = errs
                .iter()
                .map(|e| {
                    if e.kind() == ErrorKind::Target {
                        Failure::target(Stage::Staload, "common", e.to_string())
                    } else {
                        Failure::from_error(e, "common")
                    }
                })
                .collect();
            return Outcome {
                strict: stage,
                permissive: stage,
                message: errs[0].to_string(),
                failures,
            };
        }
    };
    let resolved = match elaboration::elaborate(modules, prelude) {
        Ok(program) => program.into_program(),
        Err(errs) => {
            let failures = errs
                .iter()
                .map(|error| Failure::from_error(error, "common"))
                .collect();
            return Outcome {
                strict: Stage::Emit,
                permissive: Stage::Emit,
                message: errs[0].to_string(),
                failures,
            };
        }
    };

    let strict_check = check_program(&resolved, prelude, Strictness::Strict);
    let permissive_check = check_program(&resolved, prelude, Strictness::Permissive);
    let linear = check_linearity(&resolved, prelude);
    let emit = LlvmIrEmitter::emit(&resolved);

    let (strict, message) = stop_after(&strict_check, &linear, &emit);
    let (permissive, _) = stop_after(&permissive_check, &linear, &emit);
    let mut failures = Vec::new();
    failures.extend(
        strict_check
            .iter()
            .map(|e| Failure::from_error(e, "strict")),
    );
    failures.extend(
        permissive_check
            .iter()
            .map(|e| Failure::from_error(e, "permissive")),
    );
    failures.extend(linear.iter().map(|e| Failure::from_error(e, "common")));
    if let Err(e) = &emit {
        failures.push(Failure::from_error(e, "common"));
    }

    Outcome {
        strict,
        permissive,
        message,
        failures,
    }
}

/// Where the pipeline stopped, given the three trailing error lists and
/// the emission result.
fn stop_after(
    check: &[CompileError],
    linear: &[CompileError],
    emit: &Result<String, CompileError>,
) -> (Stage, String) {
    if let Some(e) = check.first() {
        return (Stage::Check, e.to_string());
    }
    if let Some(e) = linear.first() {
        return (Stage::Linear, e.to_string());
    }
    match emit {
        Ok(_) => (Stage::Ir, String::new()),
        Err(e) => (Stage::Emit, e.to_string()),
    }
}

/// The stage an error kind names.
fn stage_of(kind: ErrorKind) -> Stage {
    match kind {
        ErrorKind::Lex => Stage::Lex,
        ErrorKind::Parse => Stage::Parse,
        ErrorKind::Emit => Stage::Emit,
        ErrorKind::Check => Stage::Check,
        ErrorKind::Linear => Stage::Linear,
        ErrorKind::Target => Stage::Staload,
    }
}

/// Turn a diagnostic into a stable capability name.
///
/// Explicit rules name known language gaps.  The fallback strips source
/// identifiers and numbers from the diagnostic, then produces a deterministic
/// slug.  A new diagnostic is therefore grouped immediately; promoting a
/// common fallback slug to an explicit semantic name is a small local change.
fn feature_code(stage: Stage, message: &str) -> String {
    let lower = message.to_ascii_lowercase();
    let known = [
        ("pattern guards", "syntax.pattern_guards"),
        ("higher-order function", "runtime.first_class_functions"),
        (
            "function types are not supported",
            "runtime.first_class_functions",
        ),
        ("tuple types are not supported", "runtime.tuple_types"),
        (
            "string comparison is not supported",
            "runtime.string_comparison",
        ),
        (
            "string patterns are not supported",
            "runtime.string_patterns",
        ),
        (
            "pattern binding is not supported",
            "syntax.pattern_bindings",
        ),
        ("unsupported macro", "runtime.macros"),
        ("unsupported type", "runtime.type_representation"),
        ("used as a value", "runtime.first_class_functions"),
        ("undefined variable", "resolution.undefined_name"),
        ("unknown function", "resolution.unknown_function"),
        ("unknown constructor", "resolution.unknown_constructor"),
        ("unknown macro", "resolution.unknown_macro"),
        ("no such file", "modules.missing_file"),
        ("cannot run clang", "toolchain.clang_unavailable"),
        ("timed out", "harness.timeout"),
    ];
    if let Some((_, code)) = known.iter().find(|(needle, _)| lower.contains(needle)) {
        return (*code).to_string();
    }
    format!("{}.{}", stage.label(), diagnostic_slug(message))
}

/// Normalize the variable parts of a diagnostic before making its slug.
fn diagnostic_slug(message: &str) -> String {
    let mut normalized = String::new();
    let mut quote: Option<char> = None;
    let mut in_number = false;
    for ch in message.chars().flat_map(char::to_lowercase) {
        if let Some(q) = quote {
            if ch == q {
                quote = None;
                normalized.push_str(" name ");
            }
            continue;
        }
        if matches!(ch, '`' | '"' | '\'') {
            quote = Some(ch);
            continue;
        }
        if ch.is_ascii_digit() {
            if !in_number {
                normalized.push_str(" number ");
                in_number = true;
            }
            continue;
        }
        in_number = false;
        normalized.push(if ch.is_alphanumeric() { ch } else { ' ' });
    }

    let words: Vec<&str> = normalized.split_whitespace().take(10).collect();
    if words.is_empty() {
        "unknown".into()
    } else {
        words.join("_")
    }
}

/// Every `.dats` (and, if asked, `.sats`) file under `root`, optionally
/// restricted to a subdirectory.
fn collect(root: &Path, subdir: Option<&Path>, include_sats: bool) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let Ok(ft) = entry.file_type() else { continue };
            let path = entry.path();
            let is_dir = ft.is_dir() && !ft.is_symlink();
            if is_dir {
                if path.file_name().and_then(|n| n.to_str()) == Some(".git") {
                    continue;
                }
                stack.push(path);
                continue;
            }
            if !ft.is_file() {
                continue;
            }
            let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
            if ext != "dats" && !(include_sats && ext == "sats") {
                continue;
            }
            if let Some(d) = subdir {
                if !path.starts_with(d) {
                    continue;
                }
            }
            out.push(path);
        }
    }
    out.sort();
    out
}

fn stopped(stage: Stage, message: impl Into<String>) -> Outcome {
    let failure = Failure::target(stage, "common", message);
    Outcome {
        strict: stage,
        permissive: stage,
        message: failure.message.clone(),
        failures: vec![failure],
    }
}

fn encode(text: &str) -> String {
    text.as_bytes().iter().map(|b| format!("{b:02x}")).collect()
}

fn decode(text: &str) -> Option<String> {
    if !text.len().is_multiple_of(2) {
        return None;
    }
    let bytes = (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).ok())
        .collect::<Option<Vec<_>>>()?;
    String::from_utf8(bytes).ok()
}

fn write_outcome(outcome: &Outcome) {
    println!(
        "outcome\t{}\t{}\t{}",
        outcome.strict.label(),
        outcome.permissive.label(),
        encode(&outcome.message)
    );
    for failure in &outcome.failures {
        println!(
            "failure\t{}\t{}\t{}\t{}",
            failure.stage.label(),
            failure.lane,
            encode(&failure.code),
            encode(&failure.message)
        );
    }
}

fn read_outcome(bytes: &[u8]) -> Option<Outcome> {
    let text = std::str::from_utf8(bytes).ok()?;
    let mut lines = text.lines();
    let header: Vec<&str> = lines.next()?.split('\t').collect();
    if header.len() != 4 || header[0] != "outcome" {
        return None;
    }
    let strict = Stage::from_label(header[1])?;
    let permissive = Stage::from_label(header[2])?;
    let message = decode(header[3])?;
    let mut failures = Vec::new();
    for line in lines {
        let fields: Vec<&str> = line.split('\t').collect();
        if fields.len() != 5 || fields[0] != "failure" {
            return None;
        }
        let lane = match fields[2] {
            "strict" => "strict",
            "permissive" => "permissive",
            "common" => "common",
            _ => return None,
        };
        failures.push(Failure {
            stage: Stage::from_label(fields[1])?,
            lane,
            code: decode(fields[3])?,
            message: decode(fields[4])?,
        });
    }
    Some(Outcome {
        strict,
        permissive,
        message,
        failures,
    })
}

/// Compile one file in a subprocess. Stack overflow and other fatal runtime
/// errors abort only this child and become corpus data rather than killing the
/// complete run.
fn compile_isolated(path: &Path, distribution: &Path, timeout: Duration) -> Outcome {
    let executable = match std::env::current_exe() {
        Ok(path) => path,
        Err(error) => return stopped(Stage::Crash, format!("cannot locate harness: {error}")),
    };
    let mut child = match Command::new(executable)
        .arg("--one")
        .arg(path)
        .arg(distribution)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(error) => return stopped(Stage::Crash, format!("cannot start harness child: {error}")),
    };
    let started = Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let output = match child.wait_with_output() {
                    Ok(output) => output,
                    Err(error) => {
                        return stopped(
                            Stage::Crash,
                            format!("cannot collect harness child: {error}"),
                        );
                    }
                };
                if status.success() {
                    return read_outcome(&output.stdout).unwrap_or_else(|| {
                        stopped(Stage::Crash, "harness child returned malformed data")
                    });
                }
                let stderr = String::from_utf8_lossy(&output.stderr);
                let message = if stderr.contains("stack overflow") {
                    "compile worker stack overflow".to_string()
                } else {
                    format!(
                        "compile worker exited with {status}: {}",
                        truncate(&stderr, 160)
                    )
                };
                return stopped(Stage::Crash, message);
            }
            Ok(None) if started.elapsed() < timeout => {
                std::thread::sleep(Duration::from_millis(10));
            }
            Ok(None) => {
                let _ = child.kill();
                let _ = child.wait();
                return stopped(Stage::Timeout, "timed out");
            }
            Err(error) => {
                return stopped(
                    Stage::Crash,
                    format!("cannot inspect harness child: {error}"),
                );
            }
        }
    }
}

/// Run the tree, `workers` isolated subprocesses at a time.
fn run(
    files: &[PathBuf],
    distribution: &Path,
    workers: usize,
    timeout: Duration,
) -> Vec<(PathBuf, Outcome)> {
    let next = Arc::new(AtomicUsize::new(0));
    let (tx, rx) = mpsc::channel();
    let n = workers.max(1).min(files.len().max(1));
    std::thread::scope(|scope| {
        for _ in 0..n {
            let next = Arc::clone(&next);
            let tx = tx.clone();
            let files: &[PathBuf] = files;
            let distribution = distribution.to_path_buf();
            scope.spawn(move || loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= files.len() {
                    break;
                }
                let path = files[i].clone();
                let outcome = compile_isolated(&path, &distribution, timeout);
                let _ = tx.send((path, outcome));
            });
        }
        drop(tx);
    });
    rx.into_iter().collect()
}

/// The first path component relative to `root` — the "package" a file
/// belongs to in the report.
fn top_dir(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .ok()
        .and_then(|p| p.components().next())
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .unwrap_or_else(|| "<root>".into())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.first().map(String::as_str) == Some("--one") {
        let Some(path) = args.get(1).map(PathBuf::from) else {
            write_outcome(&stopped(Stage::Crash, "missing path for harness child"));
            return;
        };
        let Some(distribution) = args.get(2).map(PathBuf::from) else {
            write_outcome(&stopped(
                Stage::Crash,
                "missing distribution root for harness child",
            ));
            return;
        };
        let worker = std::thread::Builder::new()
            .name("ats2-compile".into())
            .stack_size(COMPILE_STACK_BYTES)
            .spawn(move || {
                let prelude = Parser.prelude();
                compile(&path, &distribution, &prelude)
            });
        let outcome = match worker {
            Ok(worker) => worker
                .join()
                .unwrap_or_else(|_| stopped(Stage::Crash, "compile worker panicked")),
            Err(error) => stopped(
                Stage::Crash,
                format!("could not start compile worker: {error}"),
            ),
        };
        write_outcome(&outcome);
        return;
    }
    let mut root: Option<PathBuf> = None;
    let mut subdir: Option<PathBuf> = None;
    let mut limit: Option<usize> = None;
    let mut workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(8);
    let mut top = 30usize;
    let mut include_sats = false;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--dir" => subdir = it.next().map(PathBuf::from),
            "--limit" => limit = it.next().and_then(|s| s.parse().ok()),
            "--workers" => workers = it.next().and_then(|s| s.parse().ok()).unwrap_or(workers),
            "--top" => top = it.next().and_then(|s| s.parse().ok()).unwrap_or(top),
            "--sats" => include_sats = true,
            other if !other.starts_with("--") => root = Some(PathBuf::from(other)),
            other => {
                eprintln!("unknown flag `{other}`");
                std::process::exit(2);
            }
        }
    }
    let root = root.unwrap_or_else(|| {
        let here = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        here.join("..").join("..").join("ATS-Postiats")
    });
    let root = root.canonicalize().unwrap_or_else(|e| {
        eprintln!("cannot resolve {}: {e}", root.display());
        std::process::exit(2);
    });
    if !root.is_dir() {
        eprintln!("not a directory: {}", root.display());
        std::process::exit(2);
    }
    let subdir = subdir.as_ref().map(|d| root.join(d));

    let files = collect(&root, subdir.as_deref(), include_sats);
    if let Some(limit) = limit {
        eprintln!("limiting to {limit} of {} files", files.len());
    }
    let files: Vec<PathBuf> = files
        .into_iter()
        .take(limit.unwrap_or(usize::MAX))
        .collect();
    if files.is_empty() {
        eprintln!("no .dats files under {}", root.display());
        std::process::exit(2);
    }

    eprintln!(
        "compiling {} files under {} with {} workers",
        files.len(),
        root.display(),
        workers
    );

    let started = Instant::now();
    let results = run(&files, &root, workers, Duration::from_secs(20));
    let elapsed = started.elapsed();

    report(&root, &files, &results, elapsed, top);
}

/// Print the summary and write the per-file CSV.
fn report(
    root: &Path,
    files: &[PathBuf],
    results: &[(PathBuf, Outcome)],
    elapsed: Duration,
    top: usize,
) {
    let total = files.len();
    let mut strict: BTreeMap<Stage, usize> = BTreeMap::new();
    let mut permissive: BTreeMap<Stage, usize> = BTreeMap::new();
    let mut by_dir: BTreeMap<String, BTreeMap<Stage, usize>> = BTreeMap::new();
    let mut samples: BTreeMap<Stage, Vec<String>> = BTreeMap::new();

    for (path, o) in results {
        *strict.entry(o.strict).or_insert(0) += 1;
        *permissive.entry(o.permissive).or_insert(0) += 1;
        *by_dir
            .entry(top_dir(root, path))
            .or_default()
            .entry(o.strict)
            .or_insert(0) += 1;
        if o.strict != Stage::Ir {
            let v = samples.entry(o.strict).or_default();
            if v.len() < 6 && !v.contains(&o.message) {
                v.push(o.message.clone());
            }
        }
    }

    // Write the per-file ledger first: a reader piping this report into
    // `head` or `less` still deserves the file, and printing may be cut
    // short by a closed pipe.
    let csv = "ats2-harness-failures.csv";
    let mut w = String::from(
        "path,topdir,strict,permissive,strict_code,permissive_code,all_gap_codes,message\n",
    );
    for (path, o) in results {
        if o.strict == Stage::Ir && o.permissive == Stage::Ir {
            continue;
        }
        let strict_code = primary_code(o, true).unwrap_or("");
        let permissive_code = primary_code(o, false).unwrap_or("");
        let all_codes = unique_codes(o).join(";");
        w.push_str(&csv_row(&[
            &path.display().to_string(),
            &top_dir(root, path),
            o.strict.label(),
            o.permissive.label(),
            strict_code,
            permissive_code,
            &all_codes,
            &o.message,
        ]));
    }
    let csv_written = std::fs::write(csv, w).is_ok();

    let gaps = aggregate_gaps(results);
    let gaps_csv = "ats2-harness-gaps.csv";
    let mut gap_rows =
        String::from("code,stage,affected_files,strict_blockers,permissive_blockers,sample\n");
    for gap in &gaps {
        gap_rows.push_str(&csv_row(&[
            &gap.code,
            gap.stage.label(),
            &gap.files.len().to_string(),
            &gap.strict_blockers.to_string(),
            &gap.permissive_blockers.to_string(),
            gap.samples.first().map(String::as_str).unwrap_or(""),
        ]));
    }
    let gaps_written = std::fs::write(gaps_csv, gap_rows).is_ok();

    // The files that made it all the way to IR, for a follow-up pass
    // that asks whether they also link and run.
    let ir_paths: Vec<String> = results
        .iter()
        .filter(|(_, o)| o.strict == Stage::Ir)
        .map(|(p, _)| p.display().to_string())
        .collect();
    let ir_written = std::fs::write("ats2-harness-ir.txt", ir_paths.join("\n") + "\n").is_ok();

    let count = |m: &BTreeMap<Stage, usize>, s: Stage| m.get(&s).copied().unwrap_or(0);
    let pct = |n: usize| (n as f64 * 100.0) / (total as f64);

    println!(
        "ats2-harness: {} files in {} ({}s)",
        total,
        root.display(),
        elapsed.as_secs()
    );
    println!();
    println!("=== how far files get (cumulative) ===");
    println!("{:<16} {:>10} {:>10}", "reached", "strict", "permissive");
    let ladder: [(&str, Stage); 5] = [
        ("parsed", Stage::Staload),
        ("resolved", Stage::Check),
        ("checked", Stage::Linear),
        ("linear-ok", Stage::Emit),
        ("emitted (IR)", Stage::Ir),
    ];
    let strict_reach = cumulative(&strict, total);
    let perm_reach = cumulative(&permissive, total);
    for (name, floor) in ladder {
        let s = strict_reach.get(&floor).copied().unwrap_or(0);
        let p = perm_reach.get(&floor).copied().unwrap_or(0);
        println!(
            "{name:<16} {:>8} ({:>5.1}%) {:>8} ({:>5.1}%)",
            s,
            pct(s),
            p,
            pct(p)
        );
    }

    println!();
    println!("=== first failure stage (strict) ===");
    for s in Stage::REAL {
        let n = count(&strict, s);
        if n > 0 {
            println!("  {:<10} {:>5} ({:.1}%)", s.label(), n, pct(n));
        }
    }
    let to = count(&strict, Stage::Timeout);
    if to > 0 {
        println!("  {:<10} {:>5} ({:.1}%)", "timeout", to, pct(to));
    }
    let crashes = count(&strict, Stage::Crash);
    if crashes > 0 {
        println!("  {:<10} {:>5} ({:.1}%)", "crash", crashes, pct(crashes));
    }

    println!();
    println!("=== capability gaps ranked by strict blockers ===");
    println!(
        "{:<46} {:>8} {:>8} {:>8}",
        "gap", "files", "strict", "permissive"
    );
    for gap in gaps.iter().take(top) {
        println!(
            "{:<46} {:>8} {:>8} {:>8}",
            truncate(&gap.code, 46),
            gap.files.len(),
            gap.strict_blockers,
            gap.permissive_blockers,
        );
        if let Some(sample) = gap.samples.first() {
            println!("  {}", truncate(sample, 104));
        }
    }

    println!();
    println!("=== per top-level directory (strict) ===");
    println!(
        "{:<14} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6}",
        "dir",
        "lex",
        "parse",
        "staload",
        "check",
        "linear",
        "emit",
        "ir",
        "timeout",
        "crash",
        "total"
    );
    for (dir, m) in &by_dir {
        println!(
            "{:<14} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6}",
            dir,
            count(m, Stage::Lex),
            count(m, Stage::Parse),
            count(m, Stage::Staload),
            count(m, Stage::Check),
            count(m, Stage::Linear),
            count(m, Stage::Emit),
            count(m, Stage::Ir),
            count(m, Stage::Timeout),
            count(m, Stage::Crash),
            m.values().sum::<usize>(),
        );
    }

    println!();
    println!("=== sample messages per stage ===");
    for s in Stage::REAL {
        if let Some(msgs) = samples.get(&s) {
            println!("  {}:", s.label());
            for msg in msgs {
                println!("    - {}", truncate(msg, 110));
            }
        }
    }

    if csv_written {
        println!();
        println!("non-IR files written to {csv}");
    }
    if gaps_written {
        println!("ranked capability gaps written to {gaps_csv}");
    }
    if ir_written {
        println!("IR files listed in ats2-harness-ir.txt");
    }
}

/// The gap responsible for the first failure under one checking policy.
fn primary_code(outcome: &Outcome, strict: bool) -> Option<&str> {
    let stopped = if strict {
        outcome.strict
    } else {
        outcome.permissive
    };
    let lane = if strict { "strict" } else { "permissive" };
    outcome
        .failures
        .iter()
        .find(|f| f.stage == stopped && (f.lane == "common" || f.lane == lane))
        .map(|f| f.code.as_str())
}

fn unique_codes(outcome: &Outcome) -> Vec<String> {
    outcome
        .failures
        .iter()
        .map(|f| f.code.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

struct Gap {
    code: String,
    stage: Stage,
    files: BTreeSet<PathBuf>,
    strict_blockers: usize,
    permissive_blockers: usize,
    samples: Vec<String>,
}

fn aggregate_gaps(results: &[(PathBuf, Outcome)]) -> Vec<Gap> {
    let mut by_code: BTreeMap<String, Gap> = BTreeMap::new();
    for (path, outcome) in results {
        let strict_code = primary_code(outcome, true);
        let permissive_code = primary_code(outcome, false);
        let mut seen = BTreeSet::new();
        for failure in &outcome.failures {
            if !seen.insert(failure.code.clone()) {
                continue;
            }
            let gap = by_code.entry(failure.code.clone()).or_insert_with(|| Gap {
                code: failure.code.clone(),
                stage: failure.stage,
                files: BTreeSet::new(),
                strict_blockers: 0,
                permissive_blockers: 0,
                samples: Vec::new(),
            });
            gap.files.insert(path.clone());
            if strict_code == Some(failure.code.as_str()) {
                gap.strict_blockers += 1;
            }
            if permissive_code == Some(failure.code.as_str()) {
                gap.permissive_blockers += 1;
            }
            if gap.samples.len() < 3 && !gap.samples.contains(&failure.message) {
                gap.samples.push(failure.message.clone());
            }
        }
    }
    let mut gaps: Vec<Gap> = by_code.into_values().collect();
    gaps.sort_by(|a, b| {
        b.strict_blockers
            .cmp(&a.strict_blockers)
            .then_with(|| b.permissive_blockers.cmp(&a.permissive_blockers))
            .then_with(|| b.files.len().cmp(&a.files.len()))
            .then_with(|| a.code.cmp(&b.code))
    });
    gaps
}

/// "Reached at least this stage": files not stopped by anything earlier.
fn cumulative(counts: &BTreeMap<Stage, usize>, total: usize) -> BTreeMap<Stage, usize> {
    let mut reached = BTreeMap::new();
    // A timeout or fatal child crash does not reveal which stage the file
    // reached, so it must not be credited as having passed any stage.
    let mut so_far = total
        - counts.get(&Stage::Timeout).copied().unwrap_or(0)
        - counts.get(&Stage::Crash).copied().unwrap_or(0);
    for s in Stage::REAL {
        so_far -= counts.get(&s).copied().unwrap_or(0);
        reached.insert(s, so_far);
    }
    reached.insert(Stage::Ir, so_far);
    reached
}

fn truncate(s: &str, n: usize) -> String {
    if s.chars().count() <= n {
        s.to_string()
    } else {
        let cut: String = s.chars().take(n).collect();
        format!("{cut}…")
    }
}

fn csv_row(fields: &[&str]) -> String {
    let mut out = String::new();
    for (i, f) in fields.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push('"');
        out.push_str(&f.replace('"', "\"\"").replace('\n', " "));
        out.push('"');
    }
    out.push('\n');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn failure(stage: Stage, lane: &'static str, code: &str) -> Failure {
        Failure {
            stage,
            lane,
            code: code.into(),
            message: format!("diagnostic for {code}"),
        }
    }

    #[test]
    fn known_language_gaps_have_semantic_codes() {
        assert_eq!(
            feature_code(
                Stage::Emit,
                "function `visit` used as a value; higher-order functions are not supported yet"
            ),
            "runtime.first_class_functions"
        );
        assert_eq!(
            feature_code(
                Stage::Parse,
                "pattern guards (`when`) are not supported yet"
            ),
            "syntax.pattern_guards"
        );
    }

    #[test]
    fn fallback_codes_ignore_identifiers_and_source_numbers() {
        let a = feature_code(Stage::Parse, "expected `then` after value `foo` at 12");
        let b = feature_code(Stage::Parse, "expected `then` after value `bar` at 99");
        assert_eq!(a, b);
        assert!(a.starts_with("parse."));
    }

    #[test]
    fn policy_specific_primary_failures_are_kept_apart() {
        let outcome = Outcome {
            strict: Stage::Check,
            permissive: Stage::Emit,
            message: "strict stopped in checking".into(),
            failures: vec![
                failure(Stage::Check, "strict", "check.unknown"),
                failure(Stage::Emit, "common", "runtime.missing"),
            ],
        };
        assert_eq!(primary_code(&outcome, true), Some("check.unknown"));
        assert_eq!(primary_code(&outcome, false), Some("runtime.missing"));
    }

    #[test]
    fn gap_ranking_counts_files_not_repeated_diagnostics() {
        let outcome = Outcome {
            strict: Stage::Check,
            permissive: Stage::Check,
            message: "same gap under both policies".into(),
            failures: vec![
                failure(Stage::Check, "strict", "check.same"),
                failure(Stage::Check, "strict", "check.same"),
                failure(Stage::Check, "permissive", "check.same"),
            ],
        };
        let results = vec![(PathBuf::from("one.dats"), outcome)];
        let gaps = aggregate_gaps(&results);
        assert_eq!(gaps.len(), 1);
        assert_eq!(gaps[0].files.len(), 1);
        assert_eq!(gaps[0].strict_blockers, 1);
        assert_eq!(gaps[0].permissive_blockers, 1);
    }

    #[test]
    fn csv_escapes_quotes_and_newlines() {
        assert_eq!(csv_row(&["a", "b\"c\nd"]), "\"a\",\"b\"\"c d\"\n");
    }

    #[test]
    fn crashes_are_not_counted_as_reaching_compiler_stages() {
        let counts = BTreeMap::from([(Stage::Crash, 1), (Stage::Ir, 1)]);
        let reached = cumulative(&counts, 2);
        assert_eq!(reached[&Stage::Staload], 1);
        assert_eq!(reached[&Stage::Ir], 1);
    }

    #[test]
    fn child_protocol_round_trips_arbitrary_diagnostics() {
        let outcome = Outcome {
            strict: Stage::Check,
            permissive: Stage::Ir,
            message: "quoted \"message\"\nsecond line".into(),
            failures: vec![failure(Stage::Check, "strict", "check.example")],
        };
        let mut wire = format!(
            "outcome\t{}\t{}\t{}\n",
            outcome.strict.label(),
            outcome.permissive.label(),
            encode(&outcome.message)
        );
        for failure in &outcome.failures {
            wire.push_str(&format!(
                "failure\t{}\t{}\t{}\t{}\n",
                failure.stage.label(),
                failure.lane,
                encode(&failure.code),
                encode(&failure.message)
            ));
        }
        let decoded = read_outcome(wire.as_bytes()).expect("valid wire outcome");
        assert_eq!(decoded.strict, Stage::Check);
        assert_eq!(decoded.permissive, Stage::Ir);
        assert_eq!(decoded.message, outcome.message);
        assert_eq!(decoded.failures[0].code, "check.example");
    }
}
