//! # I/O adapters — the file system, through a port
//!
//! *Literate note.*  The domain never heard of files; the application only
//! names them.  Here, at last, a path is actually touched.  `FileOutput`
//! is the `OutputPort` implementation used by the executable use case and
//! by the CLI when asked to persist IR.

use std::path::Path;

use ats2_application::ports::OutputPort;

/// Writes text to a path using `std::fs`.
pub struct FileOutput;

impl OutputPort for FileOutput {
    fn write(&self, path: &Path, contents: &str) -> Result<(), String> {
        std::fs::write(path, contents).map_err(|e| e.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    fn temp_path(tag: &str) -> std::path::PathBuf {
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        std::env::temp_dir().join(format!("ats2llvm-io-test-{tag}-{}-{}", std::process::id(), n))
    }

    #[test]
    fn writes_contents_to_a_path() {
        let path = temp_path("ok");
        let result = FileOutput.write(&path, "ir text");
        assert!(result.is_ok());
        let read_back = std::fs::read_to_string(&path).expect("read back");
        assert_eq!(read_back, "ir text");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn reports_failures_as_free_form_strings() {
        let nowhere = std::env::temp_dir().join("no-such-dir-xyz").join("out.ll");
        let err = FileOutput.write(&nowhere, "x").expect_err("should fail");
        assert!(!err.is_empty());
    }
}
