# Lin

Lin is a functional programming language based on optimal interaction combinators. It executes lambda calculus terms directly as interaction nets using non-abelian scope gauges ($\langle 1, 2 \rangle^*$), eliminating the administrative bookkeeping nodes historically required by sharing graphs.

Lin includes a Hindley-Milner type system, Scott-encoded inductive datatypes, a C foreign function interface, and a built-in Geometry of Interaction (GoI) invariant tracker.

## Getting Started

### Building & Testing with Nix

Lin uses [Nix](https://nixos.org/) for reproducible, hermetic builds and testing:

```bash
# Build the lin compiler/runtime
nix build

# Run the full test suite (all suites, incl. .line containers and the Python oracles)
nix flake check

# Interactively run the test runner
nix run .#test

# Run the AOT E-Graph benchmark suite
nix run .#benchmarks

# Enter the development environment (gcc, gdb, valgrind, and `nix test` helper)
nix develop
```

### Classic Makefile Build

Lin is written in C99 and uses pthreads for lock-free parallel graph reduction:

```bash
# Build via Nix (default)
make build

# Run tests via Nix (committed tree only - see note below)
make nix-test

# Trusted working-tree build + full suite (all suites, incl. .line containers)
make test

# Or compile directly with gcc/clang
make lin
```

> **Note on nix & dirty trees.** `nix build` / `nix flake check` / `nix run
> .#test` evaluate from the **git-committed** content (flake `src = ./.` stages
> tracked, committed files), so uncommitted edits to `src/*.c` are NOT seen and
> results can be stale. For day-to-day development use `make test`, which builds
> `./lin` straight from the working tree and runs the full suite
> (`test/run_tests.sh`) against it. `nix-test` remains the reproducible CI path.

### Usage

```bash
# Interactive REPL
./result/bin/lin

# Run a source file (value-checked by examples/run_verifier.sh)
./result/bin/lin examples/pure-functional/scott_lists.lin

# Evaluate an expression directly
./result/bin/lin -e '(load "std/num.lin") (mul 6 7)'

# Multi-threaded parallel reduction (e.g. 8 threads)
./result/bin/lin -t 8 examples/logic-sat/tseitin.lin

# Benchmark mode (execution time, rewrite steps, GoI determinant)
./result/bin/lin -b examples/optimization/redundant_compute.lin
```

## Language Overview

Lin programs are written in S-expression syntax for curried lambda calculus.

### Functions and Definitions

```scheme
; Lambdas
(\x x)
(\x (\y (add x y)))

; Untyped definition (inferred via Hindley-Milner)
(define square (\x (mul x x)))

; Typed definition (checked at compile time)
(define! not (bool -> bool) (\b ((b false) true)))
(define! id (a -> a) (\x x))
```

### Data Types & Numerals

Integers are 64-bit two's complement and wrap on overflow, exactly like `int64_t`
(`x / 0` and `x % 0` are 0). They are plain net structure: a chain of bit cells, least
significant first, ended by a terminal carrying the sign. The pure-Lin arithmetic in
`std/num.lin` takes O(64) bit steps per operation; the fold drivers compute the same
function natively (`std/runtime/i64.h`).

```scheme
(sub 3 8)                     ; => -5
(add 9223372036854775807 1)   ; => -9223372036854775808
(div -7 2)                    ; => -3
(if (lt -1 0) 1 2)            ; => 1   (`if` is a core form: no library needed)
```

### User-Defined Algebraic Data Types & Pattern Matching

Lin generalizes algebraic datatypes beyond the built-in numerals, booleans, and
lists. Declare your own Scott-encoded ADTs and dispatch on them by shape:

```scheme
(datatype List (nil) (cons head tail))

(match (cons 1 (cons 2 nil))
  (nil 0)
  ((cons h t) (add h 10)))   ; => 11

(datatype Option (none) (some val) (err msg))
(match (some 5) (none 0) ((some v) v) ((err m) 9))  ; => 5
```

`(datatype Name (Ctor field...) ...)` introduces each constructor as a
Scott-encoded function (`C_i = \f1..\fk \d0..\d_{m-1} (d_i f1 ... fk)`), and
`(match scrut (pat body) ...)` compiles to positional Scott dispatch: the
scrutinee is applied to one value (nullary / `_`) or field-binding lambda per
case. Constructors type-check through ordinary Hindley-Milner let-generalization,
so no special type machinery is required.

Fields may state their types, and a datatype may take type parameters:

```scheme
(datatype (Tree a) (leaf) (node (v a) (l Tree a) (r Tree a)))
(define build (\n (if (eq n 0) leaf (node n (build (sub n 1)) leaf))))
(build 2)                    ; => (node 2 (node 1 leaf leaf) leaf)
```

A value is printed by its type: a datatype by its constructors' names, a list of
text as a string, any other list element by element (`[10 20 30]`, `[true false]`).
Declared field types make the printing exact; an undeclared field is read as its
constructor states, as a number, or as the enclosing datatype.

### Standard Library

The standard library (`std/`) is written in pure Lin. A module whose top-level forms
only define is read when a program first names something in it, so the library can grow
without costing a program that does not use it (`LIN_EAGER_STD=1` loads everything up front):

- `std/bool.lin`: Booleans and conditionals (`true`, `false`, `not`, `and`, `or`, `xor`, `if`, `ifl`).
- `std/pair.lin`: Pairs and projections (`pair`, `fst`, `snd`, `swap`, `pair_map`, `curry`, `uncurry`).
- `std/list.lin`: Inductive lists (`nil`, `cons`, `head`, `tail`, `list1`..`list5`, `first`..`eighth`).
- `std/seq.lin`: A list as a datatype, `(Seq a)` (`snil`, `scons`, `srange`, `smap`, `sfilter`, `sfoldl`, `sfoldr`, `ssum`, `slength`, `stake`, `sdrop`, `sreverse`, `sappend`, `sany`, `sall`, `snth`, `seq_of_list`, `seq_to_list`). Typed by `match`, and compiled by the function driver, higher-order calls included: `(ssum (smap (\x (mul x x)) (srange 0 1000000)))` runs as C.
- `std/maybe.lin`: Option monad (`nothing`, `just`, `is_nothing`, `is_just`, `from_maybe`, `maybe_map`, `maybe_bind`, `maybe_or`).
- `std/either.lin`: Sum / Result type (`left`, `right`, `is_left`, `is_right`, `either`, `either_map`, `either_bind`, `from_right`).
- `std/tree.lin`: Binary trees (`leaf`, `node`, `is_leaf`, `is_node`, `tree_val`, `tree_left`, `tree_right`, navigation helpers).
- `std/num.lin`: Arithmetic and comparisons (`add`, `sub`, `mul`, `div`, `mod`, `eq`, `lt`, `leq`, `gt`, `geq`).
- `std/loop.lin`: Runtime iteration (`loop n f x = f^n x` for a runtime Church count `n`, `count`).  Pure λ-calculus iteration — the loop bound is data, not a compile-time ladder.
- `std/sat.lin`: SAT combinators, quantifiers, and witness probes (`exists`, `forall`, `probe1`..`probe5`, `verify1`..`verify5`).
- `std/ffi.lin`: POSIX Foreign Function Interface (`ffi`, `ccall0`..`ccall3`, `dlopen`, `getenv`, `system`, `exit`).
- `std/io.lin`: I/O subsystem: stream/character printing (`puts`, `putchar`), file operations (`fopen`, `fclose`, `fgetc`, `fputc`), continuation-passing waiting (`io_wait`, `io_read`, `io_file`), and monadic output (`io_print`, `io_write_to`, `io_prompt`, `io_done`).

### General Result Waiting & Interactive I/O

Lin provides a general, continuation-passing mechanism to wait for results from arbitrary sources:
- **Terminal input / `stdin`**: `(io_wait 0 (\input ...))` or `(io_read cb)`
- **File descriptors / IPC**: `(io_wait fd (\chunk ...))`
- **External processes / commands**: `(io_wait "!echo 42" (\output ...))`
- **File contents**: `(io_wait "file:path" (\contents ...))`
- **Timers / delays**: `(io_wait "sleep:50" (\ms ...))`
- **FFI calls**: `(io_wait (add 40 2) (\res ...))`

Example:
```scheme
(load "std/io.lin")

; Prompt terminal user:
(io_prompt "Enter name: "
  (\name (io_print (cons "Hello, " name) (io_done 0))))

; Wait for an external process result:
(io_wait "!uname -s"
  (\kernel (io_print kernel (io_done 0))))
```

### Foreign Function Interface

Lin supports calling C library functions and dynamically loaded symbols:

```scheme
(load "std/ffi.lin")

(puts "Hello from Lin!")
(getenv "USER")
```

## Parallel Reduction & Architecture

Lin executes lambda calculus terms directly as interaction nets using non-abelian scope gauges ($\langle 1, 2 \rangle^*$), eliminating the administrative bookkeeping nodes historically required by sharing graphs.

- **Wavefront Parallelism**: Redexes whose 2-hop neighborhoods do not overlap form independent sets that are contracted simultaneously across CPU hardware threads without mutexes or global locks.
- **Lévy Optimality**: Shared subcomputations are evaluated at most once, reducing functional expressions in optimal steps.
- **No Garbage Collector**: memory is managed by the calculus itself. A rule frees the pair it consumes, and the
  compiler wires an eraser (`ERA`, one of the four node kinds) wherever a value goes unused; erasers consume what
  they reach (`ERA x LAM/APP/DUP`, a discarded application's inputs) with no tracing, no reachability walk and no
  pause. Freed slots are reused only at a safepoint, so no held index ever names a different node.
  `LIN_LEAKCHECK=1 lin -b f.lin` reports what the result still reaches (a diagnostic, never run otherwise).
- **Compiled functions (a driver, not the core)**: `std/drivers/fn.c` reads a recursive function from its own
  net and compiles it to C: arithmetic, conditionals, constructors and `match` (with in-place reuse of data
  nothing else holds), calls among functions, and higher-order calls -- a function argument is inlined into a
  copy of the callee specialised to it. Independent recursive calls run in parallel. Anything it cannot
  compile, it declines, and the net computes it; the net's answer is the authority (`test/fn_compile.sh`).
  `LIN_FN_OFF=1` turns it off, `LIN_FN_DEBUG=1` shows each decision and the C. See `bench/` for the numbers.
- **Non-Resolution Graph Normalization**: Formula normalization bypasses classical $2^{\Omega(n)}$ resolution lower bounds on parity problems like Tseitin expanders ($82|E| - 3$ linear steps).

## Examples

The `examples/` directory is a curated, self-verifying set demonstrating
Lin's interesting properties.  Each example is a self-contained program whose
top-level expressions print `=> <value>` lines, and those carrying `; expect`
annotations are machine-checked by `examples/run_verifier.sh` (14 PASS,
5 interactive):

- `optimization/` — optimization by construction: every program reduces to its
  optimal interaction-net form (Lévy/opportunistic sharing), with the native
  fold made observable (`sharing_folds.lin`), Church-encoded arithmetic sharing,
  and AOT `.line` parity.
- `pure-functional/` — the purely functional, sharing data model: Scott lists
  and ADTs, immutable collections (queue/stream/set/map).
- `logic-sat/` — constructive SAT + certificate check and Curry–Howard proofs.
- `numeric-float/` — floating-point and recursive numeric kernels.
- `systems-ffi/` — the C FFI / systems boundary and the pluggable reduction
  driver (`set_driver cpu/simd`).
- `interactive/` — runnable demos: a driver tour (`cpu->simd->gpu`), a pure
  calculator REPL, and a small turn-based game.

See `examples/README.md` for the full index, how to run each file, and how to
value-check the whole suite (`bash examples/run_verifier.sh ./lin`).

## Command-Line Options

```
Usage: lin [options] [file.lin]

Options:
  -e, --eval <expr>       Evaluate expression string directly and exit
  -b, --bench [file]      Benchmark mode: report steps, nodes, time, and GoI determinant
  -t, --threads <N>       Number of worker threads (or LIN_THREADS env)
  -v, --version           Display version information
  -h, --help              Display help and usage information
```

## License

MIT
