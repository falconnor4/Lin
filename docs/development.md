# Development

## Repository layout

```
src/                 the core engine (C99)
  lin.h              shared declarations and the driver ABI
  parse.c            reader
  type.c             type inference
  main.c             pipeline, definitions, REPL, build
  compile.c          term to net, e-graph optimiser, artifacts
  net.c              net, rules, erasure, parallel reduction
  io.c               driver loading, constructor registry, readback dispatch
  goi.c              Geometry of Interaction diagnostic
std/                 the standard library (Lin)
  std.lin            the prelude
  drivers/           drivers (C) and their loader modules (Lin)
  runtime/           C headers shared by drivers: integer/float semantics, net patterns
test/                the test suite
bench/               benchmarks against C
examples/            example programs
docs/                documentation
flake.nix, Makefile  builds
```

## Building while developing

`nix build` and `nix flake check` see committed files only. For work in
progress, build from the working tree:

```bash
nix develop          # or any shell with cc, libffi and python3
make all             # ./lin and std/drivers/*.so
make test            # build, then run everything
```

## Tests

`test/run_tests.sh` runs the whole suite against `./lin`:

```bash
make test
LIN_BIN=./lin test/run_tests.sh     # the same, without rebuilding
```

### Expectation tests

Most tests are `.lin` files. Each top-level expression prints one line, and the
file states what it must print in `; expect` comments, matched line for line:

```scheme
(add 2 3)
; expect => 5

(getenv "HOME")
; expect => /...
```

A trailing `...` makes the expectation a prefix match. To add a test, write a
`.lin` file in `test/` with its expectations and add it to the list in
`test/run_tests.sh`. The Nix check runs the same script, so there is one list.

### Property and consistency tests

Beyond expectations, the suite checks properties that a single output cannot:

| Test | What it establishes |
|------|---------------------|
| `test/fn_compile.sh` | Compiled functions equal the net's own answers, at every thread count |
| `test/int64.sh`, `test/softfloat.sh` | The pure-Lin arithmetic and the native arithmetic are the same functions, bit for bit |
| `test/no_std.sh` | The language runs with no standard library and no drivers |
| `test/optimality.py` | Reduction step counts match optimal sharing |
| `test/soundness_enum.py` | Results on boolean formulas agree with an independent evaluator |
| `test/erasure.sh` | What a program discards is reclaimed by erasure, and nothing still needed is destroyed |
| `test/wave_parallel.sh`, `test/parallel_guard.py` | Parallel reduction gives the same nets as sequential |
| `test/driver_abi.sh` | A driver built against another ABI version is refused |
| `test/aot_equiv.py` | A built artifact computes what the source computes |
| `test/no_caps.py` | No new hard-coded size limits (see below) |

`examples/run_verifier.sh ./lin` checks the example programs the same way.

### The limits lint

`test/no_caps.py` scans the C sources for fixed-size arrays and numeric guards.
A new one fails the suite unless it is derived from the data it bounds or is
declared in the script's table with a reason. If a table needs to hold more, make
it grow.

## Debugging

| Tool | Use |
|------|-----|
| `lin -b file.lin` | Steps, node counts and time for each result |
| `LIN_FN_DEBUG=1` | Why the function compiler compiled or declined each call; `2` prints the C |
| `LIN_FN_OFF=1` | Run without the function compiler, to compare answers |
| `LIN_NO_SHRINK=1`, `LIN_NO_EGRAPH=1` | Run without compile-time simplification |
| `LIN_TRACE=1` | Trace reduction |
| `LIN_DUMP_NET=<path>` with `LIN_DUMP_AT_STEP=<n>` | Write the net at a given step |
| `test/netdump.py` | Inspect a dumped net |

When a compiled function gives a different answer from the net, the net is right
by definition: reproduce with `LIN_FN_OFF=1`, then reduce the program until
`LIN_FN_DEBUG=2` shows the offending C.

## Conventions

- **The core stays pure.** No new node kinds, no payloads on nodes, no knowledge
  of particular programs or drivers in `src/`. A faster way of doing something is
  a driver.
- **Prefer the library.** If something can be written in Lin, it belongs in
  `std/`, not in C.
- **General over special.** An optimisation should apply to every datatype with
  the relevant shape, not to one named type.
- **A driver declines rather than guesses**, and every driver feature comes with
  a test that compares it against the net.
- **Benchmarks are written the natural way** in both languages; see
  [`bench/README.md`](../bench/README.md).

## Benchmarks

```bash
bench/run.sh ./lin       # or: nix run .#bench
```

The first run of each program fills the native-code cache and is not timed.
