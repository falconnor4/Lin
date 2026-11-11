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
| array | 7 ms | 61 ms | 59 ms | 0.11x | `std/array.lin` (a 32-way trie, updated in place): 1M strided writes, 1M reads -- against a flat C array |
| bintree | 45 ms | 7 ms | 8 ms | 6.43x | constructors + `match`: a depth-20 tree (2M nodes) built and counted |
| bst | 51 ms | 32 ms | 32 ms | 1.59x | a search tree: 200,000 inserts (updated in place), a weighted walk |
| collatz | 259 ms | 68 ms | 237 ms | 3.81x | a loop calling a helper loop; a max-reduction |
| fib | 183 ms | 69 ms | 188 ms | 2.65x | tree recursion |
| loop | 103 ms | 32 ms | 110 ms | 3.22x | a tail-recursive sum-reduction |
| mandel | 138 ms | 46 ms | 145 ms | 3.00x | floats (numerals with soft-float meanings); three nested loops |
| nqueens | 230 ms | 194 ms | 257 ms | 1.19x | bitmask backtracking, unbalanced tree |
| omap | 129 ms | 111 ms | 147 ms | 1.16x | `std/omap.lin` (a red-black tree): 200,000 inserts, 200,000 lookups (the lookups split across threads) |
| seqs | 77 ms | 16 ms | 15 ms | 4.81x | `std/seq.lin`: map, filter, fold over a million-element list (higher-order, specialised; each a loop, in place) |
| tak | 102 ms | 42 ms | 114 ms | 2.43x | calls whose arguments are calls |
| words | 4 ms | 14 ms | 18 ms | 0.29x | text: a 1M-character string built, its words counted -- against a C scan of a char buffer |

Measured on a 4-core x86-64 container (gcc 15, nixpkgs). Re-run before quoting.

## Where Lin is behind, and why

`array` and `words` compare a persistent, pure structure with C's mutable flat memory, and that gap is real:
an array element is four pointer hops down a trie where C does one indexed load, and a string is a linked list of
16-byte cells where C scans bytes.  Both run as compiled C with in-place update and no garbage -- the remaining
cost is the representation, and for `array` also the front end: a program that uses the trie spends about 20 ms
being parsed, expanded and compiled before it runs (C's figure has no compiler in it).

Three things the compiled code does that these two lean on:

- **Destination passing.**  A recursion that builds a cell around its own call (`map`, `filter`, `append`,
  splitting text) is written as a loop: the cell is built first with a hole, and the call is a tail call given
  the hole's address.  A list of any length is processed in constant stack.
- **A field is stored only if it changed.**  An update in place hands back the block it was given; storing that
  pointer again would make the next operation's load wait on the store, putting a loop's steps in series.
- **Huge pages.**  The arena grows by doubling chunks and asks for 2 MB pages for the large ones; fresh 4 KB
  pages were most of what building a million-cell list cost.

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
