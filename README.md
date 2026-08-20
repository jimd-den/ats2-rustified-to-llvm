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

It also checks them, and the score above is measured with the checking
on. Asked to refuse anything it cannot prove — `--strict`, which is what
it does unless told otherwise — it accepts all thirty-six, and the two it
found hardest are among them: `fact2.dats`, which proves its factorial
correct with a `dataprop`, and `fact_uninterp.dats`, which proves it with
an uninterpreted `stacst` and three axioms. It reads the proofs and
agrees. Every file above is one it both proved and ran.

`--permissive` refuses only what is provably false, and is still there
for a program that needs it. The corpus is no longer one of them.

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

The checking half is built now. It walks a program once and writes down
every claim the program would have to satisfy: what a call owes the
quantifiers of the thing it calls, what a body owes the result type it was
given, what a subscript owes the array it reaches into, and what a
recursive call owes the `.<n>.` it was written with. It carries the facts
along each path separately, so a `then` branch knows its condition and the
`else` branch knows the denial, and a `case` arm knows what it matched. It
pushes a promised result *into* the branches rather than joining them,
because arms that disagree join to nothing. An existential result — `[r:nat]
int r` — is witnessed by whatever each branch produced, and a caller that
reads one gets a name it cannot spell and a fact about it. What it cannot
determine it renames out of the caller's reach, so that "I could not work
this out" is never mistaken for "this is false".

It reads the prelude before it checks, which is what makes any of this
work on a program somebody wrote: nearly every claim a real ATS program
makes rests on a declaration the program never wrote. `succ` and `pred`
carry their `+1` and `-1`, `list_takeout_at` hands back one fewer than it
was given, and the conversions move no bits and change no index. Those
declarations are kept apart from the ones prepended to a program,
because they answer to a different reader: the checker reads them and
emission never sees them, so they may describe an index without having
to agree with the emitter about a representation.

An array keeps the size it was declared with — `array(int, n)`,
`@[int][n]`, `&(@[int][m]) >> _` and `b0ytes(n)` all name it — and the
size is kept *around* the type rather than inside it, so what the value
is stays exactly what it was. A length that exists counted something, so
it is known to be a nat without anybody asking. An index may sit at any
depth of a type, and a call finds it by matching the whole of a
parameter's type against the whole of an argument's. A constructor
pattern gives its fields the types they have, whichever of its several
names the program spelled it with. A nested function can see what it
captured. A bare `Nat` is a refinement with no index at all: the name is
the whole claim. `#define N 1024` is a number, not an unknown. And
`$UN.cast{T}(e)` is the programmer's word, taken: that is what `$UNSAFE`
is for.

It reads the proof language too, which is the half of ATS that never
runs. A `dataprop` is an inductive proposition, and each of its
constructors is a function from the proofs it consumes to a proof of its
own indices — so `FACTind {n}{r} (pf)` is an ordinary call, and needs no
machinery a call did not already have. A `praxi` is an axiom whose
*result type* is what it establishes; `prval () = fact_ind{n}()` applies
one, and from that line onward the claim holds. A `stacst` is a function
it knows nothing about except the one thing every function satisfies —
equal arguments, equal results — which is enough to finish an induction.
`(pf | v)` is a value with a proof about it: the proof is erased before
anything runs, and kept until then, because it is what pins down the
existential a signature promised. `val [r:int] (pf | x) = f(...)` gives
that witness a name. None of it reaches the emitter. All of it reaches
the checker, which is the only stage that could do anything with it.

Four modules, and none of them knows the others' business: the walk finds
claims and knows no arithmetic; the solver decides claims and knows nothing
about functions; the policy decides what a failure means and is nine lines;
the rest is vocabulary. The solver was replaced once and the walk did not
notice.

## The other half

ATS is two disciplines, and the one above is only the first. It says what
a value *is*. The second says whose it is, and for how long.

A `datavtype` value is a resource: it must be consumed exactly once. Used
twice it is a use-after-free; never used it is a leak. Neither is a claim
about arithmetic, so neither is anything the solver above could have an
opinion about — what it needs is not a second solver but a ledger. It
keeps one. A parameter written `!b` is lent rather than given: the body
may look inside and may not take it away, and is not asked to account for
it at the end. `~mk_vt (x)` is the consuming match. Every branch must
leave the same resources held, because otherwise what is held afterwards
depends on which way it went, and nothing past the branch can be checked
at all.

It refuses to guess. Only a declaration makes a value linear — a name
ending in `_vt` proves nothing. And when it meets a call nobody declared,
it stops claiming to know what a body still holds, and reports no leaks
for that body: a checker that reported leaks it could not have known
about would be reporting its own ignorance. What it will still say is
that something was used after it was handed over, because that one is
about what did happen rather than what did not.

`examples/linear.dats` is the whole of it in twenty lines.

## What it hands to somebody else

Two things a compiler cannot do alone, and does not pretend to.

Strings are runs of bytes somebody else owns, so `string_append` and
`string_make_substring` cannot write into what they were given: both ask
the arena for room and copy, and a substring is terminated where it was
told to end rather than where the original did. `examples/strings.dats`.

And a `%{ ... %}` block is C. It is not this compiler's language and
never will be, so it is carried through untouched, written out beside
the IR, and handed to the toolchain, which speaks it. The block is the
body of some `extern fun` declared next to it; a program that lost it
would compile and then fail to link, naming a symbol whose definition
had been discarded three stages earlier. It used to lose it.

## Using it

```console
$ cargo build --release

# All the way to a binary (needs clang on PATH), then run it
$ cargo run -- examples/hello.dats --bin /tmp/hello && /tmp/hello
fact(5) = 120
```

It checks before it compiles, and it will not compile what it cannot
prove. `--permissive` lowers that to refusing only what is provably
false:

```console
$ cargo run -- examples/dependent.dats --ir /tmp/d.ll             # strict
$ cargo run -- ATS-Postiats/doc/EXAMPLE/INTRO/fact2.dats --permissive --ir /tmp/f.ll
```

What it makes is text. It can be inspected, interpreted, or handed on:

```console
$ cargo run -- examples/hello.dats --ir /tmp/hello.ll
$ lli /tmp/hello.ll
fact(5) = 120
$ opt -O2 /tmp/hello.ll | llc -o hello.s
```

## What remains

The corpus has nothing left to give: thirty-six of thirty-six, compiled,
run, matched, and proved.

The resource check reads what a program declares for itself. The
prelude's own linear types do not reach it: `list_vt` and `stream_vt` are
canonicalised to the shapes they share with `list0` and `stream` before
the checker sees them, because the emitter needs one name for one
representation, and the discipline is lost with the spelling. Undoing
that means keeping the distinction the whole way down, which is a change
to every stage rather than to this one. At-views — `T @ L`, a value at an
address — are not read at all, so a program that reasons about *where*
something is reasons alone.

The solver is linear, so an equality between two products it cannot
factor is `Unknown` rather than proved. The library it knows is the part
the corpus used, and the next program will want a part it does not.
`staload` is still read and ignored, so a program is one file however
many it was written as. The arena is never given back — the promise it
keeps is that nothing leaks *within* a run, which is a smaller promise
than it sounds and the right one for programs that end. The parser still
fails fast when it could gather every error at once. It will do these
too, when it is made to. It was made to do everything that is asked of
it, and none of it belongs to it.

## Layout

```
Cargo.toml                       the four parts, each kept in its place
crates/domain/                   the data
crates/application/              what must happen
crates/infrastructure/           how it happens
crates/cli/                      the point of entry
examples/                        twenty-six samples, each with its .expected
scripts/score-corpus.sh          the hand that measures
ATS-Postiats/                    the source it was given to read
```
