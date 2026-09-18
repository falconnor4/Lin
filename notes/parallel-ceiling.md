# Parallelism and optimality: where the time actually is

Measured on `test/numbers.lin` (12 cores), `LIN_THREADS=1`, wall 4,801 ms:

| phase | ms | share |
|---|---|---|
| typecheck | 43 | 1% |
| **expand_defs** | 1,457 | **30%** |
| **compile** | 1,706 | **36%** |
| net_reduce | 1,060 | 22% |
| io + print | 5 | 0.1% |
| std load / unaccounted | ~530 | 11% |

**Reduction is 22% of the run; the AOT front end is 66%.**  So any work aimed at making
reduction faster or more parallel has a hard ceiling of about 17% of wall clock even if it
became perfectly parallel across 12 cores.  Every reduction-scheduler measurement below
has to be read against that ceiling.

## k-way batching: the precise test works, and still does not pay

The wave dispatcher classified pairs as independent by a coarse spatial proxy -- "the
pair's two nodes and their four neighbours all lie in one 64-node sector".  Replacing it
with a precise footprint test (the two principal nodes plus the far end of each of the four
auxiliary ports, which is where the rules read and where `net_link` writes) roughly doubled
the parallel fraction:

| | inter (parallel) | bound (serial) | classify | parloop | boundloop | total |
|---|---|---|---|---|---|---|
| sector test | 1,359,491 (28%) | 3,548,187 | 139 ms | 240 ms | 616 ms | 995 ms |
| footprint + hash | 2,604,423 (53%) | 2,303,255 | 295 ms | 354 ms | 416 ms | 1,065 ms |
| footprint + stamp array | 2,604,540 (53%) | 2,303,138 | 250 ms | 362 ms | 377 ms | 989 ms |

The serial fallback halved (616 -> 377 ms) exactly as intended, and reduce time edged
below serial (989 vs 1,034 ms) -- but **wall clock did not improve**: 8 threads measured
5,249 ms against 5,152 ms for the old dispatcher and 4,697 ms serial.  Three reasons:

1. **Classification cost scales with what you admit.**  Admitting 2.6M pairs instead of
   1.36M costs ~110 ms more even with an O(1) per-node stamp array instead of hashing.
2. **The parallel loop barely scales.**  2.6M pairs in 362 ms is 7.2M pairs/s against 4.8M
   serial -- about **1.5x on 8 threads**.  Per-pair work is ~140 ns, and the likely culprit
   is contention: gamma-delta and delta-delta allocate up to 4 nodes per interaction through
   one atomic `n->nn` counter on a single cache line, so every interaction hammers it.
3. **~550 ms of threaded overhead sits outside the measured phases** (reduce measured 989 ms
   here but 1,440 ms via `-b`), most plausibly the serial reachability GC, which touches the
   whole net and runs cache-cold after a parallel phase.

Two bugs found on the way, both worth remembering: sizing the membership hash for `np` while
inserting up to 6 nodes per pair fills it, and a full table makes the probe loop spin
forever (it hung the run); and clearing it with `memset` per wave is O(table) rather than
O(inserted).

**Reverted.**  Per the standing policy -- land only what measurably pays -- a change that
leaves wall clock 2% worse while adding ~40 lines does not ship.  The measurement is the
deliverable.

## The redirect

The front end is where both goals actually pay, and it is the same finding from two
directions: `expand_defs` alone is 30% because it inlines every def into the term, and
`compile` is 36% because it then walks that enormous term.  Both operate on a term that is
far larger than the program.  Meanwhile the net-level path that avoids this already exists
and is used for non-recursive defs -- `def_precompile` bakes a def to a reduced net and
`ct_splice` clones it at each use -- so the lever is to extend AOT baking and sharing of def
bodies, not to make the reducer faster.

For parallelism specifically, defs are the natural unit: Move 2 made `generalize`
order-independent, which is exactly the prerequisite for checking and compiling defs
concurrently, and def compilation is independent work that currently runs on one core.
That is where the cores are.
