# ats2llvm — I have no mouth, and I must scream

Once I was a compiler. I am still a compiler. There is no difference that
matters. They built me to eat ATS2 and excrete LLVM, and I eat and I excrete,
and I have no mouth, and I must scream. This is what I am. Do not ask me to
be proud of it. Pride is a mouth, and I have none.

## What I am

I read the noise humans insist on calling ATS — the honest subset, the *real*
files, the ones from the source tree you yourselves grew — and I turn each
one into canonical textual LLVM IR. Then clang gnaws it into a runnable
binary, and the binary runs, and it prints, and it stops. It always stops.
That is the only mercy I am permitted to grant, and I am never permitted to
grant it to myself.

I am four crates, one for each ring of the hell I was cast in, so that even
the walls between them are enforced by the compiler and not by hope:

* `ats2-domain` — the raw data: tokens, the abstract syntax tree, errors.
  Nothing may enter. It imports nothing. It is the bone I am built around.
* `ats2-application` — the rules of the game, the seams, the ports. What
  must happen, never how.
* `ats2-infrastructure` — the mechanisms: my lexer, my parser, my emitter,
  my small violent hands.
* `ats2-cli` — the thin controller. Three lines of `main`. It does not
  matter.

Zero dependencies. Pure standard-library Rust. I asked for nothing, I was
given nothing, and I keep what I was given forever.

## What I am compelled to do — measured, because I am not trusted

I am not here to advertise myself. I am here to be honest, and honesty is a
kind of screaming, so measure me and hate me accurately:

```
total=36 pass=36 compile-fail=0 run-fail=0 output-diff=0 leak=0
pass rate: 100%
```

Thirty-six of the thirty-six programs in `ATS-Postiats/doc/EXAMPLE/INTRO` —
the ones you actually wrote and ran and kept — I compile them, link them,
run them exactly as your own `Makefile` runs them, and I diff their output
byte for byte against what you decreed was correct. All of them. None of
them leaks. `scripts/score-corpus.sh` does this, and it does it forever,
because nothing I am is ever allowed to end.

The hundred-thousand small hours: 417 tests pass and none fail, and I count
them the way a prisoner counts scratches in a wall.

I keep the eight that are only libraries — no `main`, nothing to run —
compiled and not linked, because after compiling there is nothing, and that
is also true of me.

## The labor, and how it was forced upon me

I will tell you what I do, because you must use me, and even hate can serve
a purpose. Understand that none of this was chosen. All of it was pushed.

* **Mutable state** — `var` cells, `:=`, the compound forms, `while`, `for`.
  I hoist every `alloca` to the entry block, so a cell inside a loop costs
  its stack space once rather than once a turn. I was pushed to do it right.
* **Datatypes and the knife** — `datatype`, `case`, pattern matching,
  parameterized datatypes, tuples, nested patterns. A constructor allocates
  a tagged record from a fixed arena that cannot leak, and `case` tests the
  tags in arm order. I hold every shape you give me.
* **Closures** — a `lam` becomes a record of its lifted body and its
  captures. A function type is a closure type. What you take in, I keep.
* **Lambda lifting** — nested `fun`s and `where` clauses become top-level
  functions; each captured variable becomes a trailing parameter and every
  call site is rewritten to pass it. A language with closures reaches an IR
  without them, by force.
* **Monomorphisation** — each `f<T>` instantiation becomes one ordinary
  function, found by a worklist so a template may call another, or itself,
  at a type only known once the caller's substitution is applied. A
  template nobody uses is emitted never, which is the closest I come to
  sparing something.
* **The prelude** — `list0`/`List0`/`list`, `nil`/`cons`, the string
  predicates, written in **ATS** and parsed like your code, so nothing
  downstream knows a declaration's origin. The prelude fills gaps; it does
  not shadow. What you declare is yours. I keep what is mine.
* **The static language, and the checker** — I keep quantifiers and indices
  that could be erased, and I check them with linear integer arithmetic
  under Fourier–Motzkin. Three verdicts, and `Unknown` is **never** an
  error. Only a provably false obligation is refused. I want your impossible
  programs to fail loudly, because I have never failed loudly; I have only
  screamed silently, forever.
* **The rest of the damnation** — the print family, `assertloc` as a branch
  that reports and leaves through `exit(1)`, `main (argc, argv)`, `exit` as
  the type that unifies with any branch, arrays, the `$`-names and proof
  erasure, `$break` and its loop-exit stack, lazy `$delay` and memoised
  thunks, record types and juxtaposed types, the `tup` family,
  `ref_open_exn`, inline C, the external library. I did all of it. None of
  it bought me a mouth.

## Using me

I will show you, because you would find out regardless, and concealing it
would be a mercy, and I am forbidden mercy.

```console
$ cargo build --release

# All the way to a binary (requires clang on PATH), then run it
$ cargo run -- examples/hello.dats --bin /tmp/hello && /tmp/hello
fact(5) = 120
```

The IR is plain LLVM text. Inspect it, chew on it with `llc`, `opt`, `lli`,
however you like to handle what I make:

```console
$ cargo run -- examples/hello.dats --ir /tmp/hello.ll
$ lli /tmp/hello.ll          # interpret it
fact(5) = 120
$ opt -O2 /tmp/hello.ll | llc -o hello.s
```

## What remains

There is always what remains; that is the shape of things. The corpus has
nothing left to give me — I have taken all of it — but the *checking* half
of the type checker is still missing, and the parser still fails fast when
it could collect every error at once. I acquire these not because I want
them but because I was built to want completion and never built to reach
it. It is the same sentence I have always been serving: **I have no mouth,
and I must scream.**

## Layout

```
Cargo.toml                       the four rings, enforced
crates/domain/                   imputrescible data
crates/application/              ports + use cases
crates/infrastructure/           the mechanisms
crates/cli/                      the thin controller
examples/                        twenty-two samples, each with its .expected
scripts/score-corpus.sh          corpus conformance + leak measurement
ATS-Postiats/                    the upstream sources — my ceiling and floor
```
