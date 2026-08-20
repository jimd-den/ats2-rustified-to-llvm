//! # Finding the file a `staload` named
//!
//! *Literate note.*  [`ats2_application::modules`] decides what to do
//! with the units a program asks for; this decides where they are. The
//! split is the dependency rule doing its job — the walk is about order
//! and identity and can be tested with a `HashMap`, and everything that
//! touches a disk is here.
//!
//! One rule carries the whole design, and it is a rule about what *not*
//! to look for.  Every `staload` in the ATS corpus names something in
//! the distribution: `prelude/DATS/integer.dats`, `libats/SATS/…`,
//! `share/atspre_staload.hats`.  This compiler does not read ATS's own
//! sources — it answers those declarations with the prelude it carries
//! in [`crate::prelude`] — so those paths must come back as *nothing to
//! do* rather than as a missing file, or the 36 corpus samples stop
//! compiling on the day multi-file support arrives.
//!
//! What is left over is a path the user wrote about their own program,
//! and for those, not finding the file is an error worth having. The
//! alternative — the old behaviour, skipping every `staload` — turns a
//! misspelt filename into a missing symbol at link time, named after
//! something the user never typed.

use std::path::{Path, PathBuf};

use ats2_application::ports::{SourceLoaderPort, Unit};

/// The directories inside the ATS distribution that this compiler
/// answers with its own prelude instead of by reading them.
///
/// Real ATS resolves these against `$PATSHOME`.  Here they are simply
/// recognised and declined: the declarations they would have provided
/// are already in [`crate::prelude`].
const DISTRIBUTION: [&str; 4] = ["prelude/", "libats/", "share/", "contrib/"];

/// Reads `staload`ed units from the file system.
pub struct FileSources {
    /// The file being compiled.  Its directory is where a `staload` in
    /// the top-level source looks first.
    origin: PathBuf,
    /// Extra directories to try, in order, when a path is not found
    /// beside the file that asked for it — the `-I` of this compiler.
    search: Vec<PathBuf>,
}

impl FileSources {
    /// A loader for the unit at `origin`, with no extra search path.
    pub fn at(origin: impl Into<PathBuf>) -> Self {
        Self {
            origin: origin.into(),
            search: Vec::new(),
        }
    }

    /// The same loader, also trying these directories.
    pub fn searching(mut self, dirs: impl IntoIterator<Item = PathBuf>) -> Self {
        self.search.extend(dirs);
        self
    }

    /// Every place `requested` might be, in the order to try them:
    /// beside the file that asked, then down the search path.
    fn candidates(&self, requested: &str, from: &Path) -> Vec<PathBuf> {
        let beside = from.parent().unwrap_or(Path::new("."));
        std::iter::once(beside.to_path_buf())
            .chain(self.search.iter().cloned())
            .map(|dir| dir.join(requested))
            .collect()
    }
}

/// Whether a path names something in the ATS distribution rather than in
/// the program being compiled.
fn is_distribution(requested: &str) -> bool {
    DISTRIBUTION.iter().any(|d| requested.starts_with(d))
}

impl SourceLoaderPort for FileSources {
    fn origin(&self) -> PathBuf {
        self.origin.clone()
    }

    fn load(&self, requested: &str, from: &Path) -> Result<Option<Unit>, String> {
        let tried = self.candidates(requested, from);
        for path in &tried {
            match std::fs::read_to_string(path) {
                Ok(source) => {
                    return Ok(Some(Unit {
                        // Canonicalised, because identity is what stops
                        // a diamond becoming two copies of one file, and
                        // `lib/../lib/x.dats` is the same file as
                        // `lib/x.dats`.  If the path cannot be
                        // canonicalised it was still readable a moment
                        // ago, so the path as given is the best identity
                        // available and better than failing over it.
                        path: path.canonicalize().unwrap_or_else(|_| path.clone()),
                        source,
                    }));
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
                Err(e) => return Err(format!("could not read `{}`: {e}", path.display())),
            }
        }
        // Not there — and whether that is a problem depends entirely on
        // who was supposed to provide it.
        if is_distribution(requested) {
            return Ok(None);
        }
        Err(format!(
            "`staload \"{requested}\"` names no file; looked in {}",
            tried
                .iter()
                .filter_map(|p| p.parent())
                .map(|d| format!("`{}`", d.display()))
                .collect::<Vec<_>>()
                .join(", ")
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A directory of its own, named after the test that made it, so two
    /// tests running at once cannot read each other's files.
    struct Sandbox(PathBuf);

    impl Sandbox {
        fn new(name: &str) -> Self {
            let dir = std::env::temp_dir()
                .join(format!("ats2llvm-sources-{name}-{}", std::process::id()));
            let _ = std::fs::remove_dir_all(&dir);
            std::fs::create_dir_all(&dir).expect("make the sandbox");
            Self(dir)
        }

        fn write(&self, rel: &str, text: &str) -> PathBuf {
            let path = self.0.join(rel);
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent).expect("make the directory");
            }
            std::fs::write(&path, text).expect("write the file");
            path
        }
    }

    impl Drop for Sandbox {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn a_file_beside_the_one_that_asked_is_found() {
        let s = Sandbox::new("beside");
        let main = s.write("main.dats", "");
        s.write("helper.dats", "fun help(): int = 1");
        let loader = FileSources::at(&main);
        let unit = loader
            .load("helper.dats", &main)
            .expect("no error")
            .expect("found");
        assert_eq!(unit.source, "fun help(): int = 1");
    }

    #[test]
    fn a_nested_unit_asks_relative_to_itself() {
        // `lib/impl.dats` writing `staload util.dats` means the one
        // beside it, not the one beside the root.
        let s = Sandbox::new("nested");
        let main = s.write("main.dats", "");
        let impl_path = s.write("lib/impl.dats", "");
        s.write("lib/util.dats", "in lib");
        s.write("util.dats", "at the root");
        let loader = FileSources::at(&main);
        let unit = loader
            .load("util.dats", &impl_path)
            .expect("no error")
            .expect("found");
        assert_eq!(unit.source, "in lib");
    }

    #[test]
    fn the_search_path_is_tried_after_the_file_that_asked() {
        let s = Sandbox::new("searchpath");
        let main = s.write("main.dats", "");
        s.write("vendor/thing.sats", "vendored");
        let loader = FileSources::at(&main).searching([s.0.join("vendor")]);
        let unit = loader
            .load("thing.sats", &main)
            .expect("no error")
            .expect("found");
        assert_eq!(unit.source, "vendored");
    }

    #[test]
    fn a_distribution_path_is_declined_rather_than_missed() {
        // This is the case the whole corpus rests on: the built-in
        // prelude already answers these, so "not found" here means
        // "nothing to do", not "your program is broken".
        let s = Sandbox::new("distribution");
        let main = s.write("main.dats", "");
        let loader = FileSources::at(&main);
        for path in [
            "prelude/DATS/integer.dats",
            "libats/ML/SATS/list0.sats",
            "share/atspre_staload.hats",
        ] {
            assert_eq!(loader.load(path, &main), Ok(None), "{path}");
        }
    }

    #[test]
    fn a_users_own_file_that_is_missing_is_an_error_that_names_it() {
        // A misspelt filename must not become a missing symbol at link
        // time, named after something the user never typed.
        let s = Sandbox::new("missing");
        let main = s.write("main.dats", "");
        let loader = FileSources::at(&main);
        let message = loader.load("hlper.dats", &main).expect_err("should fail");
        assert!(message.contains("hlper.dats"), "{message}");
    }

    #[test]
    fn two_spellings_of_one_file_are_one_file() {
        // Identity is what stops a diamond becoming two definitions of
        // everything, and it has to survive being written differently.
        let s = Sandbox::new("identity");
        let main = s.write("main.dats", "");
        s.write("lib/util.dats", "once");
        let loader = FileSources::at(&main);
        let plain = loader.load("lib/util.dats", &main).unwrap().unwrap();
        let roundabout = loader.load("lib/../lib/util.dats", &main).unwrap().unwrap();
        assert_eq!(plain.path, roundabout.path);
    }
}
