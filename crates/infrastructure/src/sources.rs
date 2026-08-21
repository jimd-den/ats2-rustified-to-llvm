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

use ats2_application::ports::{
    SourceLoaderPort, SourcePathResolution, SourcePathResolverPort, Unit,
};

/// The directories inside the ATS distribution that this compiler
/// answers with its own prelude instead of by reading them.
///
/// Real ATS resolves these against `$PATSHOME`.  Here they are simply
/// recognised and declined: the declarations they would have provided
/// are already in [`crate::prelude`].
const DISTRIBUTION: [&str; 7] = [
    "prelude/",
    "libats/",
    "libatsdoc/",
    "libc/",
    "share/",
    "contrib/",
    "utils/",
];

/// Postiats package defaults, relative to `$PATSHOME`.
const PATH_MACROS: &[(&str, &str)] = &[
    ("$PATSHOME", "."),
    ("$PATSPRE", "prelude"),
    ("$PATSLIBATS", "libats"),
    ("$PATSLIBATSLIBC", "libats/libc"),
    ("$LIBATSCC", "contrib/libatscc"),
    ("$LIBATSML", "libats/ML"),
    ("$LIBATSCC2JS", "contrib/libatscc2js"),
    ("$LIBATSCC2PY3", "contrib/libatscc2py3"),
    ("$LIBATSCC2ERL", "contrib/libatscc2erl"),
    ("$LIBATSCC2PL", "contrib/libatscc2pl"),
    ("$LIBATSCC2PHP", "contrib/libatscc2php"),
    ("$LIBATSCC2R34", "contrib/libatscc2r34"),
    ("$LIBATSCC2CLJ", "contrib/libatscc2clj"),
    ("$LIBATSCC2SCM", "contrib/libatscc2scm"),
    ("$ATSCNTRB", "contrib/atscntrb"),
    ("$CATSPARSEMIT", "contrib/CATS-parsemit"),
    ("$EXTSOLVE", "contrib/ATS-extsolve"),
    ("$PATSOLVE", "contrib/ATS-extsolve"),
    ("$SMT_LIBZ3", "contrib/atscntrb/atscntrb-smt-libz3"),
    ("$HX_CSTREAM", "contrib/atscntrb/atscntrb-hx-cstream"),
    ("$CSTREAM", "contrib/atscntrb/atscntrb-hx-cstream"),
    ("$ATEXTING", "utils/atexting"),
    ("$LIBCAIRO", "contrib/atscntrb/atscntrb-hx-libcairo"),
    ("$LIBATSHWXI", "contrib/libats-hwxi"),
    ("$HIREDIS", "contrib/atscntrb/atscntrb-hx-hiredis"),
    ("$SDL2", "contrib/atscntrb/atscntrb-hx-sdl2"),
    ("$OPENSSL", "contrib/atscntrb/atscntrb-hx-openssl"),
    ("$HX_INTINF", "contrib/atscntrb/atscntrb-hx-intinf"),
    // The `atscntrb` add-ons and the testing library, all of which live
    // inside the distribution.
    ("$MYTESTING", "contrib/atscntrb/atscntrb-hx-mytesting"),
    ("$LIBJSONC", "contrib/atscntrb/atscntrb-hx-libjson-c"),
    ("$LIBGMP", "contrib/atscntrb/atscntrb-hx-libgmp"),
    ("$INTINF", "contrib/atscntrb/atscntrb-hx-intinf"),
    ("$LIBPCRE", "contrib/atscntrb/atscntrb-hx-libpcre"),
    ("$PATSCONTRIB", "contrib"),
];

/// Resolves path macros according to a Postiats installation.
pub struct PostiatsPaths {
    root: Option<PathBuf>,
}

impl PostiatsPaths {
    fn builtin() -> Self {
        Self { root: None }
    }

    /// Resolve package defaults relative to this Postiats distribution.
    pub fn at(root: impl Into<PathBuf>) -> Self {
        Self {
            root: Some(root.into()),
        }
    }

    fn macro_value(&self, name: &str) -> Option<PathBuf> {
        let environment = name.strip_prefix('$').unwrap_or(name);
        if let Some(value) = std::env::var_os(environment) {
            return Some(PathBuf::from(value));
        }
        PATH_MACROS
            .iter()
            .find(|(candidate, _)| *candidate == name)
            .map(|(_, relative)| match &self.root {
                Some(root) => root.join(relative),
                None => PathBuf::from(relative),
            })
    }
}

impl SourcePathResolverPort for PostiatsPaths {
    fn resolve(&self, requested: &str, _from: &Path) -> Result<SourcePathResolution, String> {
        // ATS permits a backslash-newline inside a quoted path. The lexer has
        // already erased the newline by this point, leaving `\ `; remove the
        // continuation and its indentation before interpreting the path.
        let mut normalized = String::with_capacity(requested.len());
        let mut chars = requested.chars().peekable();
        while let Some(ch) = chars.next() {
            if ch == '\\' && chars.peek().is_some_and(|next| next.is_whitespace()) {
                while chars.peek().is_some_and(|next| next.is_whitespace()) {
                    chars.next();
                }
            } else {
                normalized.push(ch);
            }
        }

        let (name, suffix) = if let Some(rest) = normalized.strip_prefix("{$") {
            let Some(close) = rest.find('}') else {
                return Err(format!("unterminated path macro in `{requested}`"));
            };
            (&rest[..close], &rest[close + 1..])
        } else if let Some(rest) = normalized.strip_prefix('$') {
            let end = rest
                .find(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
                .unwrap_or(rest.len());
            (&rest[..end], &rest[end..])
        } else {
            return Ok(SourcePathResolution::Path(PathBuf::from(normalized)));
        };
        let name = format!("${}", name.trim_start_matches('$'));
        let Some(base) = self.macro_value(&name) else {
            return Ok(if self.root.is_some() {
                SourcePathResolution::External
            } else {
                SourcePathResolution::Path(PathBuf::from(normalized))
            });
        };
        let suffix = suffix.trim_start_matches('/');
        Ok(SourcePathResolution::Distribution(base.join(suffix)))
    }
}

/// Reads `staload`ed units from the file system.
pub struct FileSources {
    /// The file being compiled.  Its directory is where a `staload` in
    /// the top-level source looks first.
    origin: PathBuf,
    /// Extra directories to try, in order, when a path is not found
    /// beside the file that asked for it — the `-I` of this compiler.
    search: Vec<PathBuf>,
    paths: Box<dyn SourcePathResolverPort>,
}

impl FileSources {
    /// A loader for the unit at `origin`, with no extra search path.
    pub fn at(origin: impl Into<PathBuf>) -> Self {
        Self {
            origin: origin.into(),
            search: Vec::new(),
            paths: Box::new(PostiatsPaths::builtin()),
        }
    }

    /// The same loader, also trying these directories.
    pub fn searching(mut self, dirs: impl IntoIterator<Item = PathBuf>) -> Self {
        self.search.extend(dirs);
        self
    }

    /// Read distribution units from `root` instead of answering them solely
    /// from the built-in prelude.
    pub fn including_distribution(mut self, root: impl Into<PathBuf>) -> Self {
        let root = root.into();
        self.search.push(root.clone());
        self.paths = Box::new(PostiatsPaths::at(root));
        self
    }

    /// Resolve ATS path expressions with the supplied environment adapter.
    pub fn resolving_with(mut self, paths: impl SourcePathResolverPort + 'static) -> Self {
        self.paths = Box::new(paths);
        self
    }

    /// Every place `requested` might be, in the order to try them:
    /// beside the file that asked, then down the search path.
    fn candidates(&self, requested: &Path, from: &Path) -> Vec<PathBuf> {
        if requested.is_absolute() {
            return vec![requested.to_path_buf()];
        }
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
        let resolution = self.paths.resolve(requested, from)?;
        let (requested, distribution) = match resolution {
            SourcePathResolution::Path(path) => (path, false),
            SourcePathResolution::Distribution(path) => (path, true),
            SourcePathResolution::External => return Ok(None),
        };
        let tried = self.candidates(&requested, from);
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
        // A distribution path may be logical rather than physical. Corpus
        // mode reads the real file when one exists, but a miss still falls
        // back to the built-in prelude instead of becoming a user-path error.
        if distribution || requested.to_str().is_some_and(is_distribution) {
            return Ok(None);
        }
        Err(format!(
            "`staload \"{}\"` names no file; looked in {}",
            requested.display(),
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
    fn a_libc_staload_is_a_library_path_and_is_declined() {
        // `staload "libc/SATS/stdio.sats"` names ATS's own libc binding,
        // which lives under `libats/` in the distribution.  It is not a
        // file the program owns, so it is recognised and declined — the
        // prelude answers it — rather than reported as missing.
        let s = Sandbox::new("libc");
        let main = s.write("main.dats", "");
        let loader = FileSources::at(&main);
        let result = loader
            .load("libc/SATS/stdio.sats", &main)
            .expect("no error");
        assert!(result.is_none(), "a distribution path should be declined");
    }

    #[test]
    fn corpus_mode_reads_a_real_distribution_unit() {
        let s = Sandbox::new("distribution");
        let main = s.write("examples/main.dats", "");
        s.write("libats/SATS/thing.sats", "fun thing(): int");
        let loader = FileSources::at(&main).including_distribution(&s.0);
        let unit = loader
            .load("libats/SATS/thing.sats", &main)
            .expect("no error")
            .expect("distribution source is loaded");
        assert_eq!(unit.source, "fun thing(): int");
    }

    #[test]
    fn a_macro_staload_path_lies_in_the_distribution_and_is_declined() {
        // `staload "{$EXTSOLVE}/SATS/ilist.sats"` names a macro the ATS
        // build defines, pointing at a directory inside the distribution
        // (`contrib/ATS-extsolve`).  The macro is expanded, and the
        // result is a distribution path like any other: declined so the
        // prelude answers it, not reported as missing.
        let s = Sandbox::new("macropath");
        let main = s.write("main.dats", "");
        let loader = FileSources::at(&main);
        let result = loader
            .load("{$EXTSOLVE}/SATS/ilist.sats", &main)
            .expect("no error");
        assert!(
            result.is_none(),
            "a distribution macro path should be declined"
        );

        // A macro this compiler does not know is left as it was written,
        // and still says where it looked when it cannot find a file.
        let err = loader
            .load("{$UNKNOWN_LIB}/SATS/x.sats", &main)
            .expect_err("an unknown macro is not silently dropped");
        assert!(err.contains("names no file"), "got: {err}");
    }

    #[test]
    fn corpus_mode_resolves_a_package_macro_to_the_real_distribution_unit() {
        let s = Sandbox::new("package-macro");
        let main = s.write("examples/main.dats", "");
        s.write(
            "contrib/ATS-extsolve/SATS/patsolve_cnstrnt.sats",
            "fun solve(): int",
        );
        let loader = FileSources::at(&main).including_distribution(&s.0);
        let unit = loader
            .load("{$PATSOLVE}/SATS/patsolve_cnstrnt.sats", &main)
            .expect("resolve package path")
            .expect("read package source");
        assert_eq!(unit.source, "fun solve(): int");
    }

    #[test]
    fn corpus_mode_treats_an_unknown_build_macro_as_external() {
        let s = Sandbox::new("external-macro");
        let main = s.write("examples/main.dats", "");
        let loader = FileSources::at(&main).including_distribution(&s.0);
        assert_eq!(
            loader.load("{$SITE_PACKAGE}/SATS/api.sats", &main),
            Ok(None)
        );
        assert_eq!(
            loader.load("$PATSHOMELOCS\\ /site-package/api.sats", &main),
            Ok(None)
        );
    }

    #[test]
    fn a_continued_distribution_path_is_normalized_before_searching() {
        let s = Sandbox::new("continued-path");
        let main = s.write("examples/main.dats", "");
        s.write("share/atspre_staload.hats", "fun loaded(): int");
        let loader = FileSources::at(&main).including_distribution(&s.0);
        let unit = loader
            .load("share\\ /atspre_staload.hats", &main)
            .expect("resolve continued path")
            .expect("read distribution unit");
        assert_eq!(unit.source, "fun loaded(): int");
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
