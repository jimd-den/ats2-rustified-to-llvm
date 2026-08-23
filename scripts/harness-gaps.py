#!/usr/bin/env python3
"""harness-gaps.py — what stops this compiler on the whole Postiats tree?

Compiles every `.dats` under the given roots (default: all of
ATS-Postiats) twice — once strictly, once permissively — and buckets the
first error of each run by a normalised form of its message.

`strict_blockers` is what the default reading refuses; `permissive_blockers`
is what remains once "cannot prove" is allowed to pass, and so is the
count of gaps that are *not* merely missing proofs.  A code with a high
strict count and a zero permissive count is a checker-strength problem;
one where the two agree is a real hole in the parser or emitter.

  usage: scripts/harness-gaps.py [--jobs N] [--timeout S] [-o out.csv] [root ...]
"""
import argparse, concurrent.futures as cf, csv, os, re, subprocess, sys, collections

BIN = "target/release/ats2llvm"


def normalise(msg: str) -> str:
    """A message with its particulars replaced by placeholders."""
    m = msg.strip().splitlines()[0] if msg.strip() else "unknown"
    stage = "unknown"
    for prefix, name in (
        ("constraint error", "check"),
        ("resource error", "linearity"),
        ("parse error", "parse"),
        ("lex error", "lex"),
        ("target error", "staload"),
        ("emit error", "emit"),
    ):
        if m.startswith(prefix):
            stage = name
            break
    body = m.split(":", 1)[1] if ":" in m else m
    body = re.sub(r"`[^`]*`", " name ", body)
    body = re.sub(r"\b\d+\b", " number ", body)
    body = re.sub(r"[^a-z0-9]+", "_", body.lower()).strip("_")
    words = [w for w in body.split("_") if w][:10]
    code = f"{stage}.{'_'.join(words)}" if words else f"{stage}.unknown"
    return stage, code



def include_roots(path: str, tree_root: str) -> list[str]:
    """The directories a project build would have had on its search path.

    ATS resolves a `staload` beside the including file first, then along
    whatever `-I` the build supplied.  Compiling one file in isolation
    gives it only the first, so a sibling `SATS/` or a package's own root
    goes missing and every name it declared reads as undefined.  What a
    build would have passed is recoverable from the tree: the package
    directory (the nearest ancestor holding a `package.json`), that
    package's conventional source directories, and the distribution root.
    """
    roots: list[str] = []
    d = os.path.dirname(os.path.abspath(path))
    here = d
    stop = os.path.abspath(tree_root)
    pkg = None
    while here.startswith(stop) and here != os.path.dirname(here):
        if os.path.exists(os.path.join(here, "package.json")):
            pkg = here
            break
        here = os.path.dirname(here)
    for base in filter(None, (d, os.path.dirname(d), pkg)):
        for sub in ("", "SATS", "DATS", "HATS"):
            cand = os.path.join(base, sub) if sub else base
            if os.path.isdir(cand) and cand not in roots:
                roots.append(cand)
    if os.path.isdir(stop) and stop not in roots:
        roots.append(stop)
    return roots

def classify(path: str, timeout: int, roots: list[str]):
    """(stage, code, sample) for the strict run and the permissive one."""
    out = {}
    for mode, flags in (("strict", []), ("permissive", ["--permissive"])):
        try:
            r = subprocess.run(
                [BIN, path, "--ir", "/dev/null",
                 *(a for r in roots for a in ("-I", r)), *flags],
                capture_output=True, text=True, timeout=timeout,
            )
            text = (r.stderr or "") + (r.stdout or "")
            if r.returncode == 0:
                out[mode] = None
                continue
            first = next(
                (l for l in text.splitlines()
                 if re.match(r"\s*(constraint|resource|parse|lex|target|emit) error", l)),
                text.strip().splitlines()[0] if text.strip() else "unknown failure",
            )
            out[mode] = (*normalise(first), first.strip())
        except subprocess.TimeoutExpired:
            out[mode] = ("timeout", "harness.timeout", "timed out")
        except Exception as e:  # noqa: BLE001
            out[mode] = ("harness", "harness.crashed", f"{type(e).__name__}: {e}")
    return path, out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("roots", nargs="*", default=["ATS-Postiats"])
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 8)
    ap.add_argument("--timeout", type=int, default=20)
    ap.add_argument("-o", "--out", default="ats2-harness-gaps.csv")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--no-roots", action="store_true",
                    help="compile each file alone, without a project search path")
    a = ap.parse_args()

    if not os.path.exists(BIN):
        print(f"no compiler at {BIN} — run 'cargo build --release' first", file=sys.stderr)
        return 2

    files = sorted(
        os.path.join(d, f)
        for root in a.roots
        for d, _, fs in os.walk(root)
        for f in fs
        if f.endswith(".dats")
    )
    if a.limit:
        files = files[: a.limit]
    print(f"{len(files)} samples, {a.jobs} jobs", file=sys.stderr)

    affected = collections.Counter()
    strict = collections.Counter()
    permissive = collections.Counter()
    sample = {}
    stage_of = {}
    passed_strict = 0

    with cf.ThreadPoolExecutor(max_workers=a.jobs) as ex:
        futs = [
            ex.submit(classify, p, a.timeout,
                      [] if a.no_roots else include_roots(p, a.roots[0]))
            for p in files
        ]
        for i, fut in enumerate(cf.as_completed(futs), 1):
            _, res = fut.result()
            if i % 200 == 0:
                print(f"  {i}/{len(files)}", file=sys.stderr)
            if res["strict"] is None:
                passed_strict += 1
            seen = set()
            for mode in ("strict", "permissive"):
                if res[mode] is None:
                    continue
                st, code, msg = res[mode]
                stage_of[code] = st
                sample.setdefault(code, msg)
                if code not in seen:
                    affected[code] += 1
                    seen.add(code)
                (strict if mode == "strict" else permissive)[code] += 1

    rows = sorted(
        affected,
        key=lambda c: (-strict[c], -permissive[c], -affected[c], c),
    )
    with open(a.out, "w", newline="") as fh:
        w = csv.writer(fh, quoting=csv.QUOTE_ALL)
        w.writerow("code stage affected_files strict_blockers permissive_blockers sample".split())
        for c in rows:
            w.writerow([c, stage_of[c], affected[c], strict[c], permissive[c], sample[c]])

    print(
        f"total={len(files)} strict-pass={passed_strict} "
        f"({100 * passed_strict // max(len(files), 1)}%) codes={len(rows)} -> {a.out}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
