//! # ats2-harness — compile every ATS file in a tree, and say where each stopped
//!
//! The corpus scorer asks of thirty-six files whether they compile and run.
//! This asks the same question of *every* `.dats` file in a tree — the whole
//! Postiats source, say — and answers it more precisely: at which stage of
//! the pipeline the file stopped.  A file that dies in the lexer is a
//! different thing from one that dies in the checker, and a completeness
//! number that cannot tell them apart is not a number.
//!
//! Stages, in order: parse → staload → check → linearity → emit.
//! `ir` means the file reached LLVM IR; every other name is where it
//! stopped.  Both a strict and a permissive pass are recorded, because
//! "cannot yet prove" (strict) and "cannot even lower" (permissive) are
//! two different gaps.
//!
//! ```text
//! ats2-harness [ROOT] [--dir DIR] [--limit N] [--workers N] [--sats]
//! ```
//!
//! `ROOT` defaults to the `ATS-Postiats` checkout beside this workspace.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{mpsc, Arc};
use std::time::{Duration, Instant};

use ats2_application::checking::{check_program, Strictness};
use ats2_application::linearity::check_linearity;
use ats2_application::modules;
use ats2_application::ports::ParserPort;
use ats2_domain::ast::Program;
use ats2_domain::errors::{CompileError, ErrorKind};
use ats2_infrastructure::llvm_ir::LlvmIrEmitter;
use ats2_infrastructure::parser::Parser;
use ats2_infrastructure::sources::FileSources;

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
        }
    }
}

/// The result for one file under both checking policies.
struct Outcome {
    strict: Stage,
    permissive: Stage,
    message: String,
}

/// Parse, resolve, check and lower one file.  The two policies share the
/// parse, the module walk, the linearity pass and the emission — only the
/// dependent check differs — so the work is done once and judged twice.
fn compile(path: &Path, prelude: &Program) -> Outcome {
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            return Outcome {
                strict: Stage::Read,
                permissive: Stage::Read,
                message: e.to_string(),
            }
        }
    };

    let parsed = match Parser::parse(&source) {
        Ok(p) => p,
        Err(errs) => {
            let stage = stage_of(errs[0].kind());
            return Outcome {
                strict: stage,
                permissive: stage,
                message: errs[0].to_string(),
            };
        }
    };

    let loader = FileSources::at(path);
    let resolved = match modules::resolve(parsed, &Parser, &loader) {
        Ok(p) => p,
        Err(errs) => {
            // A `staload` that names no file is a target error; anything
            // else here is a dependency that failed to parse.
            let stage = match errs[0].kind() {
                ErrorKind::Target => Stage::Staload,
                k => stage_of(k),
            };
            return Outcome {
                strict: stage,
                permissive: stage,
                message: errs[0].to_string(),
            };
        }
    };

    let strict_check = check_program(&resolved, prelude, Strictness::Strict);
    let permissive_check = check_program(&resolved, prelude, Strictness::Permissive);
    let linear = check_linearity(&resolved, prelude);
    let emit = LlvmIrEmitter::emit(&resolved);

    let (strict, message) = stop_after(&strict_check, &linear, &emit);
    let (permissive, _) = stop_after(&permissive_check, &linear, &emit);

    Outcome {
        strict,
        permissive,
        message,
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

/// Run the tree, `workers` files at a time, abandoning any file that does
/// not finish within `timeout`.
fn run(
    files: &[PathBuf],
    prelude: Arc<Program>,
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
            let prelude = Arc::clone(&prelude);
            let files: &[PathBuf] = files;
            scope.spawn(move || loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= files.len() {
                    break;
                }
                let path = files[i].clone();
                // The compile runs detached so a pathological file cannot
                // stall the whole harness; past `timeout` it is abandoned.
                let (tx2, rx2) = mpsc::channel();
                let path2 = path.clone();
                let prelude2 = Arc::clone(&prelude);
                std::thread::spawn(move || {
                    let _ = tx2.send(compile(&path2, &prelude2));
                });
                let outcome = match rx2.recv_timeout(timeout) {
                    Ok(o) => o,
                    Err(_) => Outcome {
                        strict: Stage::Timeout,
                        permissive: Stage::Timeout,
                        message: "timed out".into(),
                    },
                };
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
    let mut root: Option<PathBuf> = None;
    let mut subdir: Option<PathBuf> = None;
    let mut limit: Option<usize> = None;
    let mut workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(8);
    let mut include_sats = false;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--dir" => subdir = it.next().map(PathBuf::from),
            "--limit" => limit = it.next().and_then(|s| s.parse().ok()),
            "--workers" => workers = it.next().and_then(|s| s.parse().ok()).unwrap_or(workers),
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
    let root = root
        .canonicalize()
        .unwrap_or_else(|e| {
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
    let files: Vec<PathBuf> = files.into_iter().take(limit.unwrap_or(usize::MAX)).collect();
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

    let prelude = Arc::new(Parser.prelude());
    let started = Instant::now();
    let results = run(&files, prelude, workers, Duration::from_secs(20));
    let elapsed = started.elapsed();

    report(&root, &files, &results, elapsed);
}

/// Print the summary and write the per-file CSV.
fn report(root: &Path, files: &[PathBuf], results: &[(PathBuf, Outcome)], elapsed: Duration) {
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
    let mut w = String::from("path,topdir,strict,permissive,message\n");
    for (path, o) in results {
        if o.strict == Stage::Ir && o.permissive == Stage::Ir {
            continue;
        }
        w.push_str(&csv_row(&[
            &path.display().to_string(),
            &top_dir(root, path),
            o.strict.label(),
            o.permissive.label(),
            &o.message,
        ]));
    }
    let csv_written = std::fs::write(csv, w).is_ok();

    // The files that made it all the way to IR, for a follow-up pass
    // that asks whether they also link and run.
    let ir_paths: Vec<String> = results
        .iter()
        .filter(|(_, o)| o.strict == Stage::Ir)
        .map(|(p, _)| p.display().to_string())
        .collect();
    let ir_written =
        std::fs::write("ats2-harness-ir.txt", ir_paths.join("\n") + "\n").is_ok();

    let count = |m: &BTreeMap<Stage, usize>, s: Stage| m.get(&s).copied().unwrap_or(0);
    let pct = |n: usize| (n as f64 * 100.0) / (total as f64);

    println!("ats2-harness: {} files in {} ({}s)", total, root.display(), elapsed.as_secs());
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
        println!("{name:<16} {:>8} ({:>5.1}%) {:>8} ({:>5.1}%)", s, pct(s), p, pct(p));
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

    println!();
    println!("=== per top-level directory (strict) ===");
    println!(
        "{:<14} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6}",
        "dir", "lex", "parse", "staload", "check", "linear", "emit", "ir", "total"
    );
    for (dir, m) in &by_dir {
        println!(
            "{:<14} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6}",
            dir,
            count(m, Stage::Lex),
            count(m, Stage::Parse),
            count(m, Stage::Staload),
            count(m, Stage::Check),
            count(m, Stage::Linear),
            count(m, Stage::Emit),
            count(m, Stage::Ir),
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
    if ir_written {
        println!("IR files listed in ats2-harness-ir.txt");
    }
}

/// "Reached at least this stage": files not stopped by anything earlier.
fn cumulative(counts: &BTreeMap<Stage, usize>, total: usize) -> BTreeMap<Stage, usize> {
    let mut reached = BTreeMap::new();
    let mut so_far = total;
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
