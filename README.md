# Lin

Lin is a functional programming language based on optimal interaction combinators. It executes lambda calculus terms directly as interaction nets using non-abelian scope gauges ($\langle 1, 2 \rangle^*$), eliminating the administrative bookkeeping nodes historically required by sharing graphs.

Lin includes a Hindley-Milner type system, Scott-encoded inductive datatypes, a C foreign function interface, and a built-in Geometry of Interaction (GoI) invariant tracker.

## Getting Started

### Building

Lin is written in C99 and uses OpenMP for lock-free parallel graph reduction. Build with:

```bash
make
```

Or invoke the compiler directly:

```bash
gcc -O2 -std=c99 -fopenmp -o lin src/*.c -ldl
```

### Usage

```bash
# Interactive REPL
./lin

# Run a source file
./lin examples/adts.lin

# Evaluate an expression directly
./lin -e '(load "std/num.lin") (mul 6 7)'

# Multi-threaded parallel reduction (e.g. 8 threads)
./lin -t 8 examples/parallel_tree.lin

# Benchmark mode (execution time, rewrite steps, GoI determinant)
./lin -b examples/sat_verify.lin
```

Run test suite with:

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

Arbitrary-magnitude integer literals are supported directly.

### Standard Library

The standard library (`std/`) is written in pure Lin:

- `std/bool.lin`: Booleans and conditionals (`true`, `false`, `not`, `and`, `or`, `xor`, `if`, `ifl`).
- `std/pair.lin`: Pairs and projections (`pair`, `fst`, `snd`, `swap`, `pair_map`, `curry`, `uncurry`).
- `std/list.lin`: Inductive lists (`nil`, `cons`, `head`, `tail`, `list1`..`list5`, `first`..`eighth`).
- `std/maybe.lin`: Option monad (`nothing`, `just`, `is_nothing`, `is_just`, `from_maybe`, `maybe_map`, `maybe_bind`, `maybe_or`).
- `std/either.lin`: Sum / Result type (`left`, `right`, `is_left`, `is_right`, `either`, `either_map`, `either_bind`, `from_right`).
- `std/tree.lin`: Binary trees (`leaf`, `node`, `is_leaf`, `is_node`, `tree_val`, `tree_left`, `tree_right`, navigation helpers).
- `std/num.lin`: Arithmetic and comparisons (`add`, `sub`, `mul`, `div`, `mod`, `eq`, `lt`, `leq`, `gt`, `geq`).
- `std/sat.lin`: SAT combinators, quantifiers, and witness probes (`exists`, `forall`, `probe1`..`probe5`, `verify1`..`verify5`).
- `std/ffi.lin`: POSIX C interoperability (`puts`, `fopen`, `fclose`, `getenv`, `system`, `dlopen`).
- `std/io.lin`: General I/O and result waiting primitives (`io_wait`, `io_read`, `io_file`, `io_print`, `io_write_to`, `io_prompt`, `io_done`).

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
- **Zero Garbage Collection**: Node allocation and reclamation occur linearly as part of cut-elimination with no stop-the-world pauses.
- **Non-Resolution Graph Normalization**: Formula normalization bypasses classical $2^{\Omega(n)}$ resolution lower bounds on parity problems like Tseitin expanders ($82|E| - 3$ linear steps).

## Examples

The `examples/` directory contains self-contained programs demonstrating the language:

- `examples/tictactoe.lin`: Interactive 3x3 Tic-Tac-Toe game engine and AI opponent; evaluates moves in real time (`(play board move)`), detects winning threats, blocks opponent lines, and referees matches.
- `examples/sat_solver.lin`: Working propositional SAT solver with model extraction, certificate verification, and Tseitin graph expander refutations.
- `examples/logic_proofs.lin`: Constructive Curry-Howard proof terms, Modus Ponens, De Morgan's laws, and double negation.
- `examples/circuit_alu.lin`: Gate-level hardware simulation (Full Adder, 4-bit Ripple-Carry Adder, Multiplexer, ALU).
- `examples/cellular_automaton.lin`: Discrete dynamical systems (Rule 90 Sierpinski fractal & Rule 110 Turing-complete automaton).
- `examples/adts.lin`: Functional data structures (Maybe, Either, Binary Search Tree, Pairs) with monadic chaining.
- `examples/parallel_tree.lin`: Wavefront parallel reduction across OpenMP threads on balanced trees.
- `examples/tsp.lin`: Traveling Salesperson Problem (TSP) tour extraction and verification.
- `examples/ffi_sys.lin`: Interoperability with standard C library functions (`puts`, `getenv`, `putchar`).

## Command-Line Options

```
Usage: lin [options] [file.lin]

Options:
  -e, --eval <expr>       Evaluate expression string directly and exit
  -b, --bench [file]      Benchmark mode: report steps, nodes, time, and GoI determinant
  -t, --threads <N>       Number of OpenMP worker threads (or LIN_THREADS env)
  -v, --version           Display version information
  -h, --help              Display help and usage information
```

## License

MIT
