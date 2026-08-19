# ats2llvm — an ATS2 → LLVM compiler, Rustified

A from-scratch compiler foundation for a clean-architecture ATS2 front-end.
It reads a pragmatically chosen subset of [ATS2](https://github.com/githwxi/ATS-Postiats)
and lowers it to **canonical textual LLVM IR**, which the host toolchain
(`clang`) turns into a runnable binary.

```
hello.dats ──▶ lexer ──▶ parser ──▶ LLVM IR emitter ──▶ hello.ll ──▶ clang ──▶ hello
```

**Zero external dependencies.** Pure, standard-library Rust.  No Nom, no
Chumsky, no Inkwell — the lexer, parser, and IR emitter are ours, tested,
and explained in prose (each source file begins with a *literate* note on
the design decisions that shaped it).

---

## The architecture (one crate per Clean Architecture ring)

The dependency rule is enforced **by the compiler**, not by convention:
each layer is a separate crate and may import only the rings beneath it.

```
┌──────────────────────────────────────────────────────────────────┐
│ ats2-cli            the ats2llvm binary: a thin controller        │
│   └─▶ ats2-infrastructure   mechanisms: lexer, parser, IR         │
│        emitter, adapters (clang, fs, stderr), CLI                 │
│        └─▶ ats2-application  use cases + ports (abstract traits)  │
│             └─▶ ats2-domain   imputrescible data: tokens, AST,    │
│                               errors — imports nothing            │
└──────────────────────────────────────────────────────────────────┘
```

### ats2-domain — the data
* `tokens.rs` — the 49-token vocabulary (keywords, literals, operators),
  `Pos`/`Span` geometry for diagnostics.
* `ast.rs` — `Program`, `Def` (datatype / fun / implement), types, and the
  expression tree (`if`, `let`, `lam`, `println!`, operator families).
* `errors.rs` — `CompileError` with a stage kind (Lex/Parse/Emit/Target),
  an optional span, and a message.  Errors are **data**: rendering is a
  pure `Display` impl, presentation lives outside.
* No I/O, no CLI vocabulary, no mention of LLVM.  Nothing to rot.

### ats2-application — the business rules
* `ports.rs` — five abstract seams: `ParserPort`, `LlvmEmitterPort`,
  `ToolchainPort`, `OutputPort`, `DiagnosticsPort`.  Object-safe, so the
  use cases accept either generics or `dyn` references.
* `use_cases/` — `ParseUseCase`, `CompileToIrUseCase`,
  `CompileExecutableUseCase`.  Each is a tiny orchestrator: call the ports
  in order, translate port failures into domain errors, return domain
  values.  The orchestration *contract* (e.g. "the emitter is never called
  when parsing failed"; "a failed IR write prevents linking") is pinned by
  tests using in-memory fakes with shared event logs.

### ats2-infrastructure — the mechanisms
* `lexer.rs` — hand-rolled scanner: nested `(* … *)` comments, `//` line
  comments, hex literals, primed identifiers (`x'`), raw string interiors,
  byte-accurate spans, multi-error lexing.
* `parser.rs` — recursive-descent with precedence climbing.  The grammar,
  operator table, and every targeted error message ("template parameters
  are not supported yet", "termination metrics are not supported yet") are
  in its literate header.
* `infer.rs` — enough type inference to name the instance a bare template
  call means, by matching a parameter's declared type against the
  argument's actual one.  It infers but does not check, so it can only
  turn failing programs into working ones.
* `prelude.rs` — the declarations every ATS program assumes it has,
  written in ATS and parsed like user code: `list0` and its constructors,
  `list0_is_nil`/`list0_length`, the string predicates, and the line
  reader.  A definition is included only when something reaches it, so an
  unused prelude costs nothing.
* `mono.rs` — monomorphisation: each `f<T>` instantiation becomes one
  ordinary function, found by a worklist so that a template may call
  another (or itself) at a type only known once the caller's substitution
  is applied.  Nothing is emitted for a template nobody uses.
* `lift.rs` — lambda lifting for *named* nested functions (a `lam` cannot
  be lifted this way and becomes a closure instead): nested `fun`s and `where` clauses become
  top-level functions, each captured variable becoming a trailing
  parameter and each call site rewritten to pass it.  A sibling group
  shares one capture list so mutual recursion forwards cleanly.
* `llvm_ir.rs` — the pure AST→IR function.  `int→i64`, `bool→i1`,
  `string→ptr`; `if`→branches+`phi`; `andalso`/`orelse`→*short-circuit*
  branches (ATS semantics); `main0`→`@main`; `println!`→`printf` with a
  synthesized format constant.  Emits modern *opaque-pointer* IR that
  clang/llc accept verbatim.
* `adapters.rs`, `io.rs`, `toolchain.rs`, `diagnostics.rs`, `cli.rs` —
  the port implementations and the controller.

### ats2-cli — the binary
* `main.rs` — three lines: convert argv, hand it to the controller, exit.

## The grammar (supported subset of ATS2)

```text
program   := toplevel*
toplevel  := def | directive | "local" toplevel* "in" toplevel* "end"
directive := "staload" … | "#include" … | "#define" name expr | "typedef" … | …
def       := datatype-def | fun-def | implement-def
datatype  := "datatype" name ty-params? "=" ctor ("|" ctor)*
fun-def   := ("fun"|"fn") name params+ ":" type "=" expr      (params may be curried)
implement := "implement" name "(" params ")" (":" type)? "=" expr  (main0 → @main)
type      := name | name "(" type, … ")" | "(" type, … ")" | type "->" type
expr      := literals | name | call | macro-call | if/then/else[?] | let/in/end
           | { … } blocks (desugar to let) | lam | ~expr | binary ops
           | "()" | expr "where" "{" decls "}" | nested "fun" definitions
           | name ":=" expr | name ":=" op expr | while-loop | for-loop
decl      := "val" pat (":" type)? "=" expr | "var" name ":" type ("=" expr)?
while     := "while" "(" expr ")" expr
for       := "for" "(" expr ";" expr ";" expr ")" expr
ops       := orelse < andalso < = <> < <= > >= < + - < * / mod < unary ~
```

The `print` family — `print!`, `println!`, `prerr!`, `prerrln!`, `fprint!`,
`fprintln!` — spells its destination and its trailing newline into the
macro's name.  String literals become format text; `int`, `string`, and
`bool` expressions become `%ld`, `%s`, and a `select` between the words
`true` and `false`.  Each call collapses to one `printf`/`fprintf`.

`assertloc(cond)` is not a call but a branch: on failure it reports and
leaves through `exit(1)`, so the success path costs one predicted jump.

Nested `fun` definitions and `where { … }` clauses are **lambda-lifted**:
each captured variable becomes a trailing parameter and every call site is
rewritten to pass it, which is how a language with closures reaches an IR
without them.

## TDD discipline

Every component was built in the mandated RED → GREEN → REFACTOR loop,
and the transcript shows each phase:

| cycle | component              | RED (tests written first)                    | GREEN        |
|------:|------------------------|----------------------------------------------|--------------|
| 1     | domain tokens          | 11 tests vs `unimplemented!()` stubs         | 11 pass      |
| 2     | domain errors          | 8 tests vs stubs                             | +8 pass      |
| 3     | domain AST             | 17 tests vs stubs (incl. `Ty::App` later)    | +13 pass     |
| 4     | application ports      | 9 contract tests vs *no traits* (compiler RED)| 9 pass      |
| 5     | application use cases  | 9 orchestration tests vs stubs               | +9 pass      |
| 6     | infra lexer            | 24 tests vs stub (two spec bugs caught!)     | 24 pass      |
| 7     | infra parser           | 37 tests vs stub (grammar gaps fixed)        | +37 pass     |
| 8     | infra LLVM IR emitter  | 32 tests vs stub (opaque-pointer fixes)      | +32 pass     |
| 9     | infra adapters/io/clang| 12 tests vs stubs                           | +12 pass     |
| 10    | infra CLI              | 7 tests vs stub                              | +7 pass      |
| 11    | integration            | e2e + CLI smoke (lli executes the IR!)       | 9 pass       |

Later cycles extended the front end to reach real upstream ATS2 sources:

| cycle | component               | what it added                                     |
|------:|-------------------------|---------------------------------------------------|
| 12    | directives              | `staload`, `#include`, `#define`, `local`, `typedef` and friends: parsed, then ignored or turned into constants |
| 13    | statements              | a `void` type, `val () = e`, `let ... in end`, the one-armed `if`, `assertloc` |
| 14    | the print family        | `print!`/`println!`/`prerr!`/`prerrln!`/`fprint!`/`fprintln!`, and bools printing as words |
| 15    | lambda lifting          | nested `fun`s and `where { ... }`, with captures becoming parameters |
| 16    | currying                | `fun f (a) (b)` and its call sites, flattened |
| 17    | the example suite       | ten samples, each compiled, executed, and diffed against its `.expected` |
| 18–21 | mutable state           | `var` cells, `:=` and the compound `:=+`, `while`, `for` — 27 tests, written before a line of it existed |
| 22–25 | the grammar of real ATS | `$`-names, `&`/`!`/`?` type modifiers, tuple types, `(a; b)` sequencing, `_`, template arguments, brace-aware skipping |
| 26–29 | the command line        | `e: t` ascription, `xs[i]`, `main (argc, argv)`, the prelude shims (`g0string2int`, `string_length`, `g1ofg0`), indexed types erasing to their base |
| 30–31 | entry points and bottom | `main` returning an exit code; `exit` as a *never* type that unifies with any branch |
| 32–34 | datatypes               | patterns in the domain, `case` in the parser, tagged-union lowering with an arena that cannot leak |
| 35    | file I/O                | `FILEref`, the standard streams, `fileref_getc`/`putc`/`open_exn`/`close`, `fprint!` to any stream, `fileref_load` scanning into a cell |
| 36–37 | declarations            | `extern fun` as a real signature, so an `implement` may leave its parameters untyped |
| 38    | templates               | `fun{a:t@ype}` / `implement{a}` / `f<int>(…)`, expanded by a demand-driven monomorphisation pass |
| 39    | datatype syntax         | `C of (t, u)`, datatype type parameters with sorts |
| 40    | parameterized datatypes | instances built on demand, and expected-type propagation so a bare `nil()` knows which list it builds |
| 41    | tuples, nested patterns | tuple values/types/patterns, and a pattern matcher that short-circuits so nesting is safe |
| 42    | inference               | enough type inference to name the instance a bare template call means |
| 43    | the prelude             | `list0`/`List0`/`list` and `nil`/`cons`, built in and written in ATS |
| 44    | characters              | `char` as a byte, character literals and patterns, `print_char`/`char2int` |
| 45    | floating point          | `double` with its own arithmetic and ordered comparisons |
| 46    | `macdef` and `overload` | a lexical alias for an expression, and a function to fall back on when an operator's operands do not fit |
| 47    | prelude functions       | written in ATS, pulled in only when something calls them; line reading straight into the arena |
| 48    | closures                | `lam` as a code pointer plus its captures, function types, indirect calls |
| 49    | top-level values        | `val` outside any body: storage plus an initializer run before `main` |
| 50    | simultaneous bindings   | `val a = e1 and b = e2` — one declaration, several bindings |
| 51    | tuple projection        | `xs.0`, and `xs.0 := e` as a store into a place rather than a name |
| 52    | `typedef`               | a name for a type, expanded where it is used |
| 53    | proof erasure           | `(pf \| v)` in types, expressions, patterns and argument lists |
| 54    | the static language     | quantifiers and indices parsed and *kept*: `{n:nat \| n > 0}`, `int(n+1)`, `[r:int]` |
| 55    | the constraint checker  | linear integer arithmetic, Fourier–Motzkin, three verdicts |
| 56    | arrays                  | `arrayptr(t)`, `@[t][n]`, `A.[i]` and `A.[i] := e`, arena-allocated |
| 57    | template holes          | `implement f$fwork<t> (...)`, inlined at the use site so the environment stays the caller's |
| 58    | strings as pointers     | `string_test_at`, `s.tail()`, `ptr_add`, `$UN.cast`, the character classes |
| 59    | juxtaposition and dots  | `succ i`, `s.tail()`, `$UN.cast`, `a :=: b`, `!p` |
| 60    | `$break`                | a loop-exit stack, so a break leaves the innermost loop |

**404 tests, 0 failures, 0 warnings**, plus every sample verified leak-free
under valgrind.

## What it compiles, measured

Claims about a compiler's coverage should be reproducible, so coverage is
measured rather than asserted:

```console
$ cargo build --release
$ scripts/score-corpus.sh --valgrind
total=36 pass=14 compile-fail=22 run-fail=0 output-diff=0 leak=0
pass rate: 38%
```

The script compiles every sample in a corpus, links it, runs it, and — where
upstream ships a `.test-cmp` file — diffs the output byte for byte; with
`--valgrind` each one must also run free of leaks and memory errors.  Samples are run the way upstream's own Makefile runs them — with the same
command-line arguments, and folding stderr into the comparison where the
`regress::` rule does.  On `doc/EXAMPLE/INTRO` it currently gets **8 of 36**
upstream programs (`acker1`, `acker2`, `acker3`, `f91`, `fact1`,
`fact_uninterp`, `fib1`, `hello`) all the way to correct output, up from
zero.

The other thirty are blocked on whole subsystems rather than on details, and
most are blocked on several at once: mutable `var`s and assignment (13
samples), templates (13), `char`/`string` operations (13), lists with `case`
and pattern matching (8), tuples (8), closures (8), dependent types (8),
arrays and file I/O (8), laziness (4), and `main (argc, argv)` (9).  That
distribution is why the roadmap below is ordered the way it is: no single
feature unlocks the corpus.

## Using it

```console
$ cargo build --release

# LLVM IR to stdout
$ cargo run -- examples/hello.dats

# IR to a file
$ cargo run -- examples/hello.dats --ir /tmp/hello.ll

# All the way to a binary (requires clang on PATH), then run it
$ cargo run -- examples/hello.dats --bin /tmp/hello && /tmp/hello
fact(5) = 120
```

The emitted IR is plain LLVM text — inspect it, feed it to `llc`/`opt`/`lli`
freely:

```console
$ cargo run -- examples/hello.dats --ir /tmp/hello.ll
$ lli /tmp/hello.ll          # interpret it
fact(5) = 120
$ opt -O2 /tmp/hello.ll | llc -o hello.s    # optimize & assemble
```

## Roadmap (ordered by how much of the corpus each unlocks)

1. ~~**Mutable `var`s, `:=`, and the loop forms**~~ — **done.**  `var`
   allocates a cell, `:=` stores into it, and `while`/`for` each keep
   their condition in a block of its own.  Every `alloca` is hoisted to
   the entry block, so a cell inside a loop costs stack space once rather
   than once per turn.  This cleared the biggest single blocker, though
   the samples behind it are held up by the subsystems below as well.
2. **String operations** — indexing, `string_foreach`, and the rest of the
   prelude's string surface.  (`char` itself now exists.)
3. ~~**Datatypes, `case`, and pattern matching**~~ — **done** for
   user-declared datatypes: constructors allocate a tagged record from a
   fixed arena, and `case` tests tags in arm order.  Still missing: nested
   patterns, guards, and `case` over tuples.
4. ~~**Parameterized datatypes**~~ — **done.**  `datatype list0(a)` is
   instantiated per element type on demand, and expected-type propagation
   settles which instance a bare `nil()` builds.
5. ~~**Tuples** and **nested patterns**~~ — **done**, including the
   short-circuiting the nesting requires.
6. ~~**Closures**~~ — **done.**  A `lam` becomes a record holding its
   lifted body and its captures; a function type is a closure type.
7. **A full type checker** — so ill-typed programs fail before emission
   rather than at the LLVM boundary.  The *inference* half now exists
   (`infer.rs`), because monomorphisation needed it; what is missing is
   the checking half.
8. **All-parse-errors collection** — the parser still fails fast.
9. **Dependent types and laziness** — the long tail.

## Layout

```
Cargo.toml                      workspace: 4 crates, enforced layering
crates/domain/                  imputrescible data
crates/application/             ports + use cases
crates/infrastructure/          lexer, parser, emitter, adapters, CLI
crates/cli/                     the ats2llvm binary
examples/                       twenty-two samples, each with its .expected output
scripts/score-corpus.sh         corpus conformance + leak measurement
ATS-Postiats/                   the upstream ATS2 sources (reference)
```

## The list samples, and what inference bought

`listfuns` now passes, which is worth spelling out because it was the
sample that motivated three separate pieces of work.  It needed all of:

* **parameterized datatypes** — its lists are the prelude's `list0(a)`,
  instantiated at `int` and at `(int, int)`;
* **tuples and nested patterns** — `case+ (xs, ys) of | (cons(x,xs),
  cons(y,ys)) => ...` is a tuple pattern holding two constructor patterns;
* **inference** — it writes `length (xs)` with no instantiation, at two
  different element types, so the instance has to be read off the
  argument.

The inference pass (`infer.rs`) is deliberately small.  It infers, it does
not check: a type it cannot work out is simply unknown, the call is left
alone, and the emitter reports it exactly as before.  A pass built that way
can only turn programs that used to fail into programs that work — it can
never reject one that used to compile — which is what made it safe to add
this late.

The prelude (`prelude.rs`) is the other half.  Real programs never declare
the list they use; they `#include "share/atspre_staload.hats"` and get it.
The few declarations that matter are built in, *written in ATS* and parsed
by the same parser as user code, so nothing downstream knows where a
declaration came from.  A program that declares its own `list0` keeps it:
the prelude fills gaps, it does not shadow.  And because datatypes are
instantiated on demand, a prelude declaration nobody uses costs nothing.

## The static language, and why it is not skipped

For most of its life this compiler treated `{n:nat}`, `int(n)` and
`.<n>.` as noise between the parts that mattered, skipped them, and
emitted correct code anyway.  That is defensible — ATS erases all of it
before anything runs, so a compiler that skips it produces the same
machine code — and it is also missing the point.  `int(n)` is not a
decoration on `int`; it is the reason the type is worth writing.

So the static language now has its own representation
(`ats2-domain/statics.rs`: sorts, static terms, quantifiers), the parser
keeps it (`Ty::Index`, `FunDef::universals`, `FunDef::existentials`), and
`ats2-application/constraints.rs` checks it between parsing and emission
— the last moment at which it still exists.

The checker decides linear arithmetic over the integers, which is what
the corpus actually indexes with.  A goal is proved by showing its
negation unsatisfiable under Fourier–Motzkin elimination over the
rationals; rational unsatisfiability implies integer unsatisfiability, so
every proof is sound, and strict inequalities are tightened first (`n >
0` becomes `n >= 1`) to recover most of what integrality buys.  Products
of two unknowns become opaque variables — the *same* opaque variable each
time, so a claim needing only that `m*n` is itself still goes through.

The verdict has three values, and that is the important design decision.
`Proved` and `Refuted` are the two you expect; `Unknown` covers
everything outside the fragment and everything merely undecided, and it
is **never** an error.  Only a provably false obligation is reported:

```
$ ats2llvm dep_bad.dats
constraint error: `fact` accepts only arguments for which `n >= 0` holds,
and this call needs `~1 >= 0`, which is false
```

This means switching the checker on cannot reject a program that used to
compile — measured, it did not change the corpus score by a single
sample — while a genuinely impossible call is now refused before any code
is emitted.  Index inference is still one-sided: it reads parameters,
literals and arithmetic, and does not yet read the facts a branch
establishes, so `f(x-1)` under `x > 0` is `Unknown` rather than proved.
Strengthening it makes the checker catch more; it cannot make it catch
things wrongly.

## What the remaining samples need

Fourteen of the thirty-six still fail.  Two of them are not reachable
from here at all, and saying so is more useful than leaving them on a
list:

* **`myatslib`** links against an external C library, and **`areverse`**
  needs inline C (`%{^ ... %}`) plus a *contrib* package
  (`atscntrb-hx-mytesting`) for its random numbers.  Neither is a
  language feature this compiler is missing; both are build-system
  reach.

The other twelve are blocked on real subsystems, in order of how many
each would unlock:

* **laziness** (4) — `$delay`, memoised thunks, `!s` forcing, and
  mutually recursive lazy `val rec` globals: `fib_lazy`, `fib_llazy`,
  `sieve_lazy`, `sieve_llazy`.  The largest single block left.
* **the list library** (4) — `$list{t}(...)` literals, `list_vt` linear
  lists with holes in their patterns, `fprint_val<t>` holes:
  `fprintlst2`, `intrange`, `listpermute`, `ordset` (which also needs
  `'{...}` record types).
* **odds and ends** (4) — `fcopy2` (`&b0ytes(n) >> bytes(n)` and
  `ref_open_exn`), `fprtuple` (the `tup` family from
  `prelude/DATS/tuple.dats`), `staref` (a top-level `var` whose type
  must be read off its initializer), `bintree` (juxtaposition in
  *types*, so `bintree a` is an application and inference can read the
  element type off it).
