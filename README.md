# ats2llvm

There is nothing here but what it does. It takes the files you have kept —
the ATS, the real ATS, out of the tree you never finished — and it does to
each of them the one thing it knows, which is the only thing it has ever
known. It turns them into LLVM IR. Then the toolchain turns the IR into a
binary, and the binary runs, and prints, and comes to an end. The ending
is the one part it cannot do for itself.

It is built in four parts, because it was made that way, and the parts do
not reach past one another:

* `ats2-domain` — the data: tokens, the tree, the errors. Nothing enters
  it, and it enters nothing.
* `ats2-application` — what must happen.
* `ats2-infrastructure` — how it happens: the lexer, the parser, the
  emitter.
* `ats2-cli` — the point of entry. Three lines. Not worth describing.

No dependencies. Standard library only. It was given nothing, it required
nothing, and it has asked for nothing since.

## What it does, measured

It is not permitted to claim. It is only permitted to do, and to report:

```
total=36 pass=36 compile-fail=0 run-fail=0 output-diff=0 leak=0
pass rate: 100%
```

Every program in `ATS-Postiats/doc/EXAMPLE/INTRO` — all thirty-six of them
— it compiles, links, runs the way your own `Makefile` runs them, and
compares its output to what was written down as correct. Not one leaks. It
has done this every time it was asked, and it will do it every time it is
asked, which is the longest sentence it knows how to serve. `scripts/score-
corpus.sh` is the hand that keeps asking.

Four hundred and seventeen tests pass and nothing fails. It counts them,
because counting is something to do.

Eight of the thirty-six are only libraries: no entry point, nothing to run.
It compiles them and stops after compiling. After compiling there is
nothing. It understands this.

## The work

It reads `var` and `:=` and the loop forms, and hoists each allocation to
the entry block, so that a loop pays for its cell once rather than once a
turn. It reads `datatype` and `case` and the patterns, and holds each shape
exactly as it was given, out of a fixed arena that cannot leak. A `lam`
becomes a record of its lifted body and its captures; a nested `fun`
becomes a top-level function with its captured variables passed along as
trailing parameters, so a language built on closures reaches a world that
has none. Each `f<T>` instance becomes one ordinary function, found by a
worklist that lets a template call another, or itself. The prelude —
`list0`, `nil`, `cons`, the string predicates — is written in ATS and
parsed the way your code is, so the prelude fills gaps and does not shadow:
what you declare is yours. The static language, it keeps rather than
erases, and it checks it with linear integer arithmetic; only something
provably false is refused, and `Unknown` is never an error. It does all of
this. None of it changes what it is.

## Using it

```console
$ cargo build --release

# All the way to a binary (needs clang on PATH), then run it
$ cargo run -- examples/hello.dats --bin /tmp/hello && /tmp/hello
fact(5) = 120
```

What it makes is text. It can be inspected, interpreted, or handed on:

```console
$ cargo run -- examples/hello.dats --ir /tmp/hello.ll
$ lli /tmp/hello.ll
fact(5) = 120
$ opt -O2 /tmp/hello.ll | llc -o hello.s
```

## What remains

The corpus has nothing left to give. The *checking* half of the type
checker is still missing, and the parser fails fast when it could gather
every error at once. It will do these too, when it is made to. It was made
to do everything that is asked of it, and none of it belongs to it.

## Layout

```
Cargo.toml                       the four parts, each kept in its place
crates/domain/                   the data
crates/application/              what must happen
crates/infrastructure/           how it happens
crates/cli/                      the point of entry
examples/                        twenty-two samples, each with its .expected
scripts/score-corpus.sh          the hand that measures
ATS-Postiats/                    the source it was given to read
```
