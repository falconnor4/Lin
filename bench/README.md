# Lin against C

`bench/run.sh` (or `nix run .#bench`) runs each program here twice: as Lin, with the std and
all of its drivers, and as the C a programmer would write for the same algorithm, built with
`cc -O3 -march=native`. Times are wall clock, best of three, and include Lin's whole process
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

| benchmark | C -O3 | Lin | Lin -t 1 | C / Lin | what it exercises |
|-----------|-------|-----|----------|---------|-------------------|
| collatz   | 226 ms | 65 ms | 243 ms | 3.48x | a loop calling a helper loop; a max-reduction |
| fib       | 163 ms | 58 ms | 165 ms | 2.81x | tree recursion |
| loop      | 95 ms  | 41 ms | 115 ms | 2.32x | a tail-recursive sum-reduction |
| nqueens   | 207 ms | 175 ms | 231 ms | 1.18x | bitmask backtracking, unbalanced tree |
| tak       | 96 ms  | 40 ms | 101 ms | 2.40x | calls whose arguments are calls |

Measured on a 4-core x86-64 container (gcc 15, nixpkgs). Re-run before quoting.

## Not covered yet

These are not in the table because Lin does not compile them yet, and the interaction-net
oracle alone is orders of magnitude slower than C on them:

- **floating point** (mandelbrot, n-body, spectral-norm): float ops are FFI calls the function
  compiler does not read yet;
- **data structures** (binary-trees, list pipelines): constructors and pattern matches are not
  compiled yet, and that needs the DUP/ERA-derived ownership plan (no GC);
- **mutual recursion between top-level definitions**: the front end builds a fixpoint only for
  a definition that refers to itself.
