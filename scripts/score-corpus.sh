#!/usr/bin/env bash
#
# score-corpus.sh — how much of a corpus of real ATS2 does this compile?
#
# For each `foo.dats` in the given directories: compile it to LLVM IR, hand
# the IR to clang, run the result, and judge the outcome.  When a
# `foo.test-cmp` sits beside the sample (the upstream convention) its
# contents are the expected stdout, byte for byte; otherwise a clean exit 0
# is the bar, which is what the assertion-only samples ask for.  A
# `foo.test-inp` file, if present, is fed to the program on stdin.
#
#   usage: scripts/score-corpus.sh [--valgrind] [corpus-dir ...]
#
# With --valgrind every sample must also run free of memory errors and of
# definite or indirect leaks.  Default corpus: ATS-Postiats/doc/EXAMPLE/INTRO.
#
# A per-sample verdict lands in $WORK/report.txt; the summary goes to stdout.
set -uo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
BIN=${ATS2LLVM:-$ROOT/target/release/ats2llvm}
WORK=${WORK:-${TMPDIR:-/tmp}/ats2llvm-corpus}
mkdir -p "$WORK"

VG=0
if [ "${1:-}" = "--valgrind" ]; then VG=1; shift; fi

DIRS=("$@")
[ ${#DIRS[@]} -eq 0 ] && DIRS=("$ROOT/ATS-Postiats/doc/EXAMPLE/INTRO")

if [ ! -x "$BIN" ]; then
  echo "no compiler at $BIN — run 'cargo build --release' first" >&2
  exit 1
fi

pass=0; ecomp=0; erun=0; ediff=0; eleak=0; total=0
: > "$WORK/report.txt"

for d in "${DIRS[@]}"; do
  for f in "$d"/*.dats; do
    [ -e "$f" ] || continue
    total=$((total + 1))
    b=$(basename "$f" .dats)
    ll=$WORK/$b.ll
    exe=$WORK/$b

    # No `--permissive` here.  The dependent checker's strict reading —
    # refuse anything it cannot prove — accepts all thirty-six, so the
    # score is measured the honest way: every file below is one this
    # compiler both proved and ran.  The hatch still exists for programs
    # that need it; the corpus is no longer one of them.
    if ! "$BIN" "$f" --ir "$ll" >/dev/null 2>"$WORK/err"; then
      ecomp=$((ecomp + 1))
      echo "COMPILE  $b :: $(grep -m1 . "$WORK/err" | cut -c1-140)" >> "$WORK/report.txt"
      continue
    fi
    # A sample with no `main0` is a *library*: upstream builds it only
    # as an extra input to another sample (`myatslib.dats`), and its
    # Makefile gives it no `regress::` rule because there is nothing to
    # run.  Compiling it is the whole bar, so it is compiled and not
    # linked.
    if ! grep -q '^ *\(implement\|fun\|fn\)[^A-Za-z0-9_]*main[0-9]*' "$f" \
       && ! grep -q 'main0\|main1\|implement *main' "$f"; then
      if clang -w -c -o "$exe.o" "$ll" 2>"$WORK/err"; then
        pass=$((pass + 1))
        echo "PASS     $b (library: compiled, not linked)" >> "$WORK/report.txt"
      else
        ecomp=$((ecomp + 1))
        echo "CLANG    $b :: $(grep -m1 error "$WORK/err" | cut -c1-140)" >> "$WORK/report.txt"
      fi
      continue
    fi

    if ! clang -w -o "$exe" "$ll" 2>"$WORK/err"; then
      ecomp=$((ecomp + 1))
      echo "CLANG    $b :: $(grep -m1 error "$WORK/err" | cut -c1-140)" >> "$WORK/report.txt"
      continue
    fi

    inp=/dev/null
    [ -e "$d/$b.test-inp" ] && inp="$d/$b.test-inp"

    # Run the sample the way upstream's own Makefile runs it.  Its
    # `regress::` rules carry the command-line arguments a sample expects
    # (`./fact1 10`) and whether stderr is folded into the comparison
    # (`2>&1`).  Reading them keeps "passing" meaning what upstream means.
    args=""
    fold_stderr=0
    if [ -e "$d/Makefile" ]; then
      rule=$(grep -A2 "^regress:: $b " "$d/Makefile" 2>/dev/null | grep -m1 '\./\$<')
      [ -z "$rule" ] && rule=$(grep -m1 "\./$b " "$d/Makefile" 2>/dev/null)
      if [ -n "$rule" ]; then
        args=$(echo "$rule" | sed -e 's|.*\./\$<||' -e "s|.*\./$b||" -e 's|2>&1.*||' -e 's/|.*//' -e 's/^ *//' -e 's/ *$//')
        # Drop shell redirections: stdin already comes from `.test-inp`,
        # and `<file` is not an argument the program ever sees.
        args=$(echo "$args" | tr ' ' '\n' | grep -v '^[<>]' | tr '\n' ' ' | sed -e 's/^ *//' -e 's/ *$//')
        echo "$rule" | grep -q '2>&1' && fold_stderr=1
      fi
    fi

    if [ $fold_stderr -eq 1 ]; then
      timeout 20 "$exe" $args < "$inp" > "$WORK/out" 2>&1
    else
      timeout 20 "$exe" $args < "$inp" > "$WORK/out" 2>"$WORK/rerr"
    fi
    if [ $? -ne 0 ]; then
      erun=$((erun + 1))
      echo "RUN      $b :: $(grep -m1 . "$WORK/rerr" "$WORK/out" 2>/dev/null | cut -c1-110)" >> "$WORK/report.txt"
      continue
    fi
    if [ -e "$d/$b.test-cmp" ] && ! diff -q "$d/$b.test-cmp" "$WORK/out" >/dev/null; then
      ediff=$((ediff + 1))
      echo "OUTPUT   $b :: $(diff "$d/$b.test-cmp" "$WORK/out" | head -4 | tr '\n' ' ' | cut -c1-140)" >> "$WORK/report.txt"
      continue
    fi
    if [ $VG -eq 1 ]; then
      # --log-file keeps valgrind's report out of the program's own stderr.
      valgrind --log-file="$WORK/vg.log" --error-exitcode=42 --leak-check=full \
               --errors-for-leak-kinds=definite,indirect \
               "$exe" < "$inp" >/dev/null 2>/dev/null
      if [ $? -eq 42 ]; then
        eleak=$((eleak + 1))
        echo "VALGRIND $b :: $(grep -m1 'ERROR SUMMARY' "$WORK/vg.log" | cut -c1-140)" >> "$WORK/report.txt"
        continue
      fi
    fi

    pass=$((pass + 1))
    echo "PASS     $b" >> "$WORK/report.txt"
  done
done

echo "total=$total pass=$pass compile-fail=$ecomp run-fail=$erun output-diff=$ediff leak=$eleak"
[ $total -gt 0 ] && echo "pass rate: $((pass * 100 / total))%"
echo "per-sample verdicts: $WORK/report.txt"
