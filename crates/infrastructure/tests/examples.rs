//! # The example suite — every sample compiles *and computes*
//!
//! *Literate note.*  The unit tests pin each component and `end_to_end.rs`
//! pins the assembly of them.  This file pins something else again: that
//! the programs shipped in `examples/` still mean what they meant.
//!
//! Reading the emitted IR would not do it.  IR that *looks* right can
//! still compute the wrong number — a `phi` naming the wrong predecessor
//! block produces perfectly well-formed IR that silently returns the
//! wrong value.  So each sample is compiled, executed under `lli`, and
//! its output compared byte for byte against the `.expected` file beside
//! it.  A sample and its expectation are a single test case; adding a
//! program to `examples/` adds a case here with no code change.
//!
//! The suite is skipped when `lli` is not installed, in the same spirit
//! as the `lli` test in `end_to_end.rs`: a missing LLVM toolchain is a
//! fact about the machine, not a defect in the compiler.

use std::path::{Path, PathBuf};
use std::process::Command;

use ats2_infrastructure::llvm_ir::LlvmIrEmitter;
use ats2_infrastructure::parser::Parser;

fn examples_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples").canonicalize().expect("examples/ exists")
}

fn lli_available() -> bool {
    Command::new("lli").arg("--version").output().is_ok()
}

/// Compile one sample to IR, run it, and return what it printed.
fn run_sample(dats: &Path) -> String {
    let source = std::fs::read_to_string(dats).expect("read the sample");
    let program = Parser::parse(&source).unwrap_or_else(|errs| {
        panic!("{}: parse failed: {}", dats.display(), errs[0]);
    });
    let ir = LlvmIrEmitter::emit(&program).unwrap_or_else(|e| {
        panic!("{}: emit failed: {e}", dats.display());
    });

    let stem = dats.file_stem().expect("a file stem").to_string_lossy().to_string();
    let ir_path = std::env::temp_dir().join(format!("ats2llvm-ex-{}-{}.ll", stem, std::process::id()));
    std::fs::write(&ir_path, &ir).expect("write the IR");
    let out = Command::new("lli").arg(&ir_path).output().expect("run lli");
    let _ = std::fs::remove_file(&ir_path);

    assert!(
        out.status.success(),
        "{}: the program exited with {}\nstderr: {}",
        dats.display(),
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("the samples print UTF-8")
}

#[test]
fn every_example_compiles_and_prints_what_it_should() {
    if !lli_available() {
        eprintln!("skipping: lli not on PATH");
        return;
    }
    let dir = examples_dir();
    let mut samples: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read examples/")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|e| e == "dats"))
        .collect();
    samples.sort();
    assert!(!samples.is_empty(), "no samples found in {}", dir.display());

    for dats in samples {
        let expected_path = dats.with_extension("expected");
        let expected = std::fs::read_to_string(&expected_path).unwrap_or_else(|_| {
            panic!("{} has no .expected file beside it", dats.display());
        });
        let actual = run_sample(&dats);
        assert_eq!(
            actual,
            expected,
            "{} printed something other than its .expected file",
            dats.display()
        );
    }
}

/// The samples are the documentation, so a sample without an expectation
/// (or an expectation without a sample) is itself a defect.
#[test]
fn every_sample_is_paired_with_an_expectation() {
    let dir = examples_dir();
    for entry in std::fs::read_dir(&dir).expect("read examples/") {
        let path = entry.expect("a directory entry").path();
        match path.extension().and_then(|e| e.to_str()) {
            Some("dats") => assert!(
                path.with_extension("expected").exists(),
                "{} has no .expected file",
                path.display()
            ),
            Some("expected") => assert!(
                path.with_extension("dats").exists(),
                "{} has no .dats file",
                path.display()
            ),
            _ => {}
        }
    }
}
