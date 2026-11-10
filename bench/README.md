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
| bintree | 34 ms | 6 ms | 7 ms | 5.67x | constructors + `match`: a depth-20 tree (2M nodes) built and counted |
| bst | 28 ms | 31 ms | 30 ms | 0.90x | a search tree: 200,000 inserts (updated in place), a weighted walk |
| collatz | 201 ms | 51 ms | 150 ms | 3.94x | a loop calling a helper loop; a max-reduction |
| fib | 132 ms | 46 ms | 124 ms | 2.87x | tree recursion |
| loop | 79 ms | 28 ms | 76 ms | 2.82x | a tail-recursive sum-reduction |
| mandel | 114 ms | 31 ms | 92 ms | 3.68x | floats (numerals with soft-float meanings); three nested loops |
| nqueens | 158 ms | 127 ms | 162 ms | 1.24x | bitmask backtracking, unbalanced tree |
| tak | 58 ms | 32 ms | 74 ms | 1.81x | calls whose arguments are calls |

Measured on a 4-core x86-64 container (gcc 15, nixpkgs). Re-run before quoting.

## Data structures

`bintree` and `bst` are compiled by the same driver: a datatype's constructors and matches state which
constructor they are in the net (the constructor registry, src/lin.h), so the function compiler reads a
constructor as a C block and a match as a switch.  Memory comes from an arena freed when the call returns, and
OWNERSHIP decides reuse: the unit's DAG shows sharing exactly, so a match on a value nothing else holds rebuilds
the branch's constructor in the block it took apart -- the insert updates the path in place, as C does.  A
datatype with one boxed constructor (trees, lists) carries no tag at all.  Lin is lazy and the C strict: a unit
whose structure outgrows memory or the stack (an infinite one, of which the program reads a part) is abandoned
and the net computes the call -- the answer is always the net's.

Without the function compiler (the oracle alone) these two are still far behind C: the oracle copies a
recursive body per call.  `LIN_FN_OFF=1` shows it.
