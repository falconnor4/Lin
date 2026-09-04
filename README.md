# Lin

Lin is a functional programming language based on optimal interaction combinators. It executes lambda calculus terms directly as interaction nets using non-abelian scope gauges ($\langle 1, 2 \rangle^*$), eliminating the administrative bookkeeping nodes historically required by sharing graphs.

Lin includes a Hindley-Milner type system, Scott-encoded inductive datatypes, a C foreign function interface, and a built-in Geometry of Interaction (GoI) invariant tracker.

## Getting Started

### Building

Lin is written in C99 and has no external dependencies beyond POSIX `libdl`:

```bash
gcc -O2 -std=c99 -o lin src/*.c -ldl
```

### Usage

```bash
# Interactive REPL
./lin

# Run a source file
./lin examples/tsp.lin

# Evaluate an expression directly
./lin -e '(load "std/num.lin") (mul 6 7)'

# Benchmark mode (execution time, rewrite steps, GoI determinant)
./lin -b examples/tsp.lin
```

Run tests with:

```bash
./test/run.sh
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

Numerals use Scott encodings, providing an $\mathcal{O}(1)$ predecessor:

```scheme
zero        ; => 0
(succ 41)   ; => 42
(pred 42)   ; => 41
(is_zero 0) ; => true
```

Integer literals (`0` to `5000`) are supported directly.

### Standard Library

The standard library (`std/`) is written in pure Lin:

- `std/bool.lin`: Booleans and conditionals (`true`, `false`, `not`, `and`, `or`, `xor`, `if`, `ifl`).
- `std/pair.lin`: Pairs and projections (`pair`, `fst`, `snd`, `swap`).
- `std/list.lin`: Inductive lists (`nil`, `cons`, `head`, `tail`, `length`, `first`..`fifth`).
- `std/maybe.lin`: Option type (`nothing`, `just`, `maybe`).
- `std/either.lin`: Sum type (`left`, `right`, `either`).
- `std/tree.lin`: Binary trees (`leaf`, `node`, `tree_sum`).
- `std/num.lin`: Arithmetic and comparisons (`add`, `sub`, `mul`, `div`, `mod`, `eq`, `lt`, `leq`, `gt`).
- `std/sat.lin`: SAT combinators, quantifiers, and witness probes (`exists`, `forall`, `probe1`..`probe5`, `verify1`..`verify5`).
- `std/ffi.lin`: POSIX C interoperability (`puts`, `fopen`, `fclose`, `getenv`, `system`, `dlopen`).

### Foreign Function Interface

Lin supports calling C library functions and dynamically loaded symbols:

```scheme
(load "std/ffi.lin")

(puts "Hello, world!")
(system "uname -s")
```

## Non-Abelian Interaction Nets

Classical optimal reduction (Lamping, Asperti) required auxiliary bracket and croissant nodes to delimit sharing scopes, which often led to exponential bookkeeping overhead.

Lin labels duplicator nodes with words from the free group $\mathbb{F}_2 = \langle 1, 2 \rangle^*$. During reduction:
- When a duplicator interacts with an abstraction or application, scope prefixes ($1 \cdot w$, $2 \cdot w$) are injected.
- When two duplicators meet, matching gauges annihilate while differing gauges commute.

This provides confluent, optimal reduction without administrative nodes.

### Applications & Benchmarks

- **Tseitin Expander Formulas**: Tseitin parity formulas on 3-regular expander graphs have an exponential lower bound $2^{\Omega(n)}$ in resolution-based proof systems (such as DPLL and CDCL). Lin evaluates them via superposition sharing in strictly linear steps ($\text{Steps}(|E|) = 82|E| - 3$). See [`bench/tseitin_bench.py`](bench/tseitin_bench.py).
- **Traveling Salesperson Problem (TSP)**: Encodes candidate tours as boolean decision superpositions, extracts optimal tour witnesses, and verifies certificates in sub-millisecond time. See [`examples/tsp.lin`](examples/tsp.lin) and [`bench/tsp_bench.py`](bench/tsp_bench.py).

## Command-Line Options

```
Usage: lin [options] [file.lin]

Options:
  -e, --eval <expr>   Evaluate expression string directly and exit
  -b, --bench [file]  Benchmark mode: report steps, nodes, time, and GoI determinant
  -v, --version       Display version information
  -h, --help          Display help and usage information
```

## License

MIT
