# Lin against C

`bench/run.sh` (or `nix run .#bench`) runs each program here twice: as Lin, with the std and
all of its drivers, and as the C a programmer would write for the same algorithm, built with
`cc -O3 -march=native -ffp-contract=off`. Times are wall clock, best of three, and include Lin's whole process
(startup, prelude, and loading the function compiler's cached build). Outputs must match.

The rules, so the numbers mean something:

- **Same algorithm, natural code.** No memoisation or algorithmic help on the Lin side, no
  hand-written parallelism on the C side. If Lin is faster, it is because of what Lin does
  automatically.
- **Lin's speed comes from its drivers, never from changing the program.** `std/drivers/fn.c`
  compiles a recursive integer function to C *from its own net* and folds the call. Tree
  recursion and independent calls run on every core, and a loop folding an associative operation
  (wrapping `add`/`mul`, the bitwise ops, `max`/`min`) is split across threads. All of it is
  checked against the net's own reduction (`test/fn_compile.sh`).
- **`Lin -t 1` is reported too**, so the single-threaded comparison is visible.
- **Floating point is strict IEEE on both sides.** Lin's float semantics are fixed (no fused multiply-add),
  so the C is built with `-ffp-contract=off`; with contraction, `-march=native` C computes a *different*
  mandelbrot count, and two programs that disagree cannot be timed against each other.

| benchmark | C -O3 | Lin | Lin -t 1 | C / Lin | what it exercises |
|-----------|-------|-----|----------|---------|-------------------|
| collatz | 261 ms | 71 ms | 232 ms | 3.68x | a loop calling a helper loop; a max-reduction |
| fib | 176 ms | 67 ms | 186 ms | 2.63x | tree recursion |
| loop | 115 ms | 46 ms | 115 ms | 2.50x | a tail-recursive sum-reduction |
| mandel | 139 ms | 50 ms | 150 ms | 2.78x | floats (numerals with soft-float meanings); three nested loops |
| nqueens | 224 ms | 193 ms | 254 ms | 1.16x | bitmask backtracking, unbalanced tree |
| tak | 105 ms | 52 ms | 111 ms | 2.02x | calls whose arguments are calls |
| bintree | ~1 ms | 2.6 s | | ~0.0004x | constructors + `match`: a depth-7 tree built and counted |
| bst | ~1 ms | 40 s | | ~0.00003x | a search tree: 20 inserts, a weighted walk |

Measured on a 4-core x86-64 container (gcc 15, nixpkgs). Re-run before quoting.

## Where Lin is not fast yet

The last two rows are the honest gap.  The function compiler compiles recursive *numeric* functions;
code over data structures (constructors and `match`) runs on the interaction-net oracle, and there the
recursion itself is the problem: the oracle copies a recursive function's body lazily, so an arithmetic
operator inside it sees its operands *superposed* (one per copy, until the copy has moved through), no
single number is the answer, and the fold declines to the operator's bitwise pure meaning -- thousands of
interactions per `add`.  Two fixes are planned, both general:

- **an operator meeting a superposition duplicates itself** (each copy then waits for its own operand,
  and folds) -- the interaction-level rule, which keeps the reduction optimal;
- **the function compiler compiles data structures**: constructors to C objects, `match` to a switch,
  with memory reclaimed by ownership derived from the net's own sharing (DUP) and erasure (ERA).
