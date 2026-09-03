# Lin

Lin is a minimalist functional programming language based on optimal interaction combinators with non-abelian scope gauges. The entire compiler, Hindley-Milner type checker, interaction net runtime, Geometry of Interaction (GoI) engine, and C FFI are implemented in **under 2,000 lines of standard C99** with zero external dependencies.

Unlike traditional bytecode virtual machines or graph-reduction engines, Lin evaluates programs directly as interaction nets. By using free-group gauge labels $\langle 1, 2 \rangle^*$ instead of traditional sharing brackets, Lin achieves Lévy-optimal reduction without the administrative bookkeeping overhead that historically affected sharing graphs.

---

## Quick Start

### Build

Lin requires only a standard C99 compiler and POSIX `libdl`:

```bash
gcc -O2 -std=c99 -o lin src/*.c -ldl
```

### Run

```bash
# Start the interactive REPL
./lin

# Run a script
./lin examples/tsp.lin

# Evaluate an expression directly
./lin -e '(load "std/num.lin") (mul 6 7)'

# Run with benchmark metrics (steps, nodes, time, GoI determinant)
./lin -b examples/tsp.lin
```

### Test

Run the regression test suite:

```bash
./test/run.sh
```

---

## Language Guide

Lin uses S-expression syntax for curried lambda calculus.

### Lambdas & Definitions

```scheme
; Identity function
(\x x)

; Multi-argument lambda (curried)
(\x (\y (add x y)))

; Untyped definition (type is inferred automatically via Hindley-Milner)
(define square (\x (mul x x)))

; Explicitly typed definition (checked at compile time)
(define! not (bool -> bool) (\b ((b false) true)))
(define! id (a -> a) (\x x))
```

### Scott Numerals

Numerals use Scott encodings, providing $\mathcal{O}(1)$ predecessor operations:

```scheme
zero        ; => 0
(succ 41)   ; => 42
(pred 42)   ; => 41
(is_zero 0) ; => true
```

Integer literals from `0` to `5000` are supported directly.

### Standard Library (`std/`)

Lin includes a standard library implemented entirely in Lin:

| Module | Purpose | Key Exports |
|---|---|---|
| `std/bool.lin` | Booleans and conditionals | `true`, `false`, `not`, `and`, `or`, `xor`, `if`, `ifl` |
| `std/pair.lin` | Pair product types | `pair`, `fst`, `snd`, `swap` |
| `std/list.lin` | Inductive linked lists | `nil`, `cons`, `head`, `tail`, `is_empty`, `length`, `first`..`fifth` |
| `std/maybe.lin` | Optional values | `nothing`, `just`, `is_nothing`, `is_just`, `from_maybe` |
| `std/either.lin` | Sum types | `left`, `right`, `is_left`, `is_right`, `either` |
| `std/tree.lin` | Binary trees | `leaf`, `node`, `tree_sum`, `tree_size` |
| `std/num.lin` | Arithmetic & comparisons | `zero`, `succ`, `pred`, `add`, `sub`, `mul`, `div`, `mod`, `eq`, `lt`, `leq`, `gt` |
| `std/sat.lin` | SAT combinators & probes | `clause1`..`clause4`, `exists`, `forall`, `probe1`..`probe5`, `verify1`..`verify5` |
| `std/ffi.lin` | POSIX C interop | `ccall0`..`ccall3`, `puts`, `fopen`, `fclose`, `getenv`, `system`, `dlopen` |

### Foreign Function Interface (FFI)

Lin can call standard C functions and dynamically loaded libraries:

```scheme
(load "std/ffi.lin")

; Standard libc calls
(puts "Hello from Lin!")
(system "uname -a")

; Dynamic library loading via dlopen
(define handle (dlopen "libm.so"))
```

---

## Theory & Performance

### Non-Abelian Scope Gauges

Classical optimal reduction (Lamping 1990, Asperti 1998) required auxiliary "bracket" and "croissant" nodes to delimit sharing scopes, which often caused combinatorial bookkeeping growth in complex terms.

Lin replaces bracket nodes by labeling each duplicator with a word from the free group $\mathbb{F}_2 = \langle 1, 2 \rangle^*$. During reduction:
- When a duplicator interacts with an abstraction or application, scope prefixes ($1 \cdot w$ and $2 \cdot w$) are injected into the child nodes.
- When two duplicators interact, they annihilate if their gauges match, or commute if they differ.

This guarantees confluent, deterministic, and optimal evaluation without auxiliary bookkeeping nodes.

### Bypassing Resolution Lower Bounds

In proof complexity, Tseitin parity formulas over 3-regular expander graphs are known to require exponential proof sizes in resolution-based systems (Urquhart 1987):

$$\text{Size}(\Pi_{\text{Resolution}}) \ge 2^{\Omega(n)}$$

Because DPLL and CDCL SAT solvers are implementations of resolution, they encounter this exponential barrier. In Lin, truth assignments are evaluated across shared interaction net topologies, resolving Tseitin expander refutations in strictly **linear steps**:

$$\text{Steps}(|E|) = 82|E| - 3$$

| Vertices ($n$) | Edges ($|E|$) | Search Space | Lin Steps | Reduction Time |
|:---:|:---:|:---:|:---:|:---:|
| 4 | 6 | $2^6$ | 489 | ~18 ms |
| 8 | 12 | $2^{12}$ | 981 | ~18 ms |
| 12 | 18 | $2^{18}$ | 1,473 | ~19 ms |
| 16 | 24 | $2^{24}$ | 1,965 | ~19 ms |
| 20 | 30 | $2^{30}$ | 2,457 | ~22 ms |

To run the benchmark:
```bash
python3 bench/tseitin_bench.py
```

### Combinatorial Optimization: Traveling Salesperson Problem (TSP)

Lin can formulate NP-hard combinatorial optimization problems as boolean decision predicates, evaluate them concurrently with topological sharing, extract the optimal witness, and independently verify the certificate.

See [`examples/tsp.lin`](examples/tsp.lin) and [`bench/tsp_bench.py`](bench/tsp_bench.py):

```bash
$ ./lin examples/tsp.lin
=> true   ; Budget B = 25 is SAT
=> true   ; Certificate verified
=> 24     ; Optimal tour cost
=> 0      ; Tour: 0 -> 1 -> 3 -> 2 -> 0
=> 1
=> 3
=> 2
=> 0
=> false  ; Budget B = 20 is UNSAT (no tour <= 20)
```

---

## Compiler Architecture

Lin is designed to be lean, readable, and fully self-contained. The C codebase is strictly under 2,000 lines of code:

| File | Lines | Description |
|---|:---:|---|
| [`src/lin.h`](src/lin.h) | 84 | Core AST, Port, Net, Scope, and Scheme definitions |
| [`src/compile.c`](src/compile.c) | 132 | AST-to-net compiler with duplicator fan-out trees |
| [`src/net.c`](src/net.c) | 268 | Interaction net engine with $\langle 1, 2 \rangle^*$ scope gauges |
| [`src/type.c`](src/type.c) | 279 | Hindley-Milner type inference with let-polymorphism |
| [`src/parse.c`](src/parse.c) | 356 | S-expression parser, string desugaring, Scott literals |
| [`src/io.c`](src/io.c) | 387 | Net readback, Scott numeral decoder, FFI dispatcher |
| [`src/main.c`](src/main.c) | 428 | REPL, multi-line buffer, CLI flags, benchmark timer |
| [`src/goi.c`](src/goi.c) | 63 | Geometry of Interaction (GoI) Fredholm determinant calculator |
| **Total** | **1,997** | **Complete implementation** |

---

## Command-Line Options

```
Usage: lin [options] [file.lin]

Options:
  -e, --eval <expr>   Evaluate expression string directly and exit
  -b, --bench [file]  Benchmark mode: report steps, nodes, time, and GoI determinant
  -v, --version       Display version information
  -h, --help          Display help and usage information
```

---

## License

MIT
