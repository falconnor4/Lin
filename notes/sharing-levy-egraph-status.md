# Status: sharing, Levy-optimality, and the e-graph AOT pass

Three questions, answered by measurement rather than by DESIGN.md's claims.

## 1. Sharing: VERIFIED optimal for acyclic values

Probe: share one expensive computation (`(mul 6 7)`, ~21.7k steps) and vary only the
number of uses, with the uses themselves structurally cheap (`pair`/`fst`) so the
arithmetic cannot confound the result.  Pure beta, no arithmetic driver.

| uses of the shared value | steps | marginal per extra use |
|---|---|---|
| 1 (no sharing) | 21,667 | -- |
| 2 | 21,839 | +172 |
| 3 | 22,016 | +177 |
| 4 | 22,193 | +177 |

The marginal cost of another use is **constant at ~177 steps, 0.8% of the computation**.
So the shared computation runs ONCE and each additional use costs only fan + projection
overhead.  That is the property Levy-optimality is about -- no re-execution -- and it is
verified here at the value level.

Also measured and ruled out as causes of cost variation: the fan tree's construction
(identical to the step when only `dup_tree` varies) and the wave schedule order (identical
to the step under LIFO vs FIFO).  Earlier numbers that looked like a 2.5x sharing defect
were `num.add` recursing on its FIRST argument.

## 2. Levy-optimality: optimal for ACYCLIC, absent for CYCLIC. Recursion is the hole.

What exists: fans (DUP) with a gauge/level discipline, delta-delta annihilation when levels
match and commutation when they do not, gamma-delta commutation with `scope_meet`
modulation.  This is a real sharing discipline and it is oracle-green.

What does NOT exist: brackets or abstractors.  Consequences, in order of how much they cost:

- **Recursion is bounded self-unravelling, not shared reduction.**  `build_bound_rec`
  emits `f (f (... (f base)))` with k = 24 copies of the def body, doubled by
  `widen_recursion` when the depth is exceeded.  That is k copies of the work at COMPILE
  time, and it is why `expand_defs` is **30% of real runtime** -- the single largest
  compiler cost measured (see notes/parallel-ceiling.md).  A Levy-optimal engine would
  share the body once and reduce it cyclically.
- **A fan wrapped around a cyclic body is divergent by construction**, which is why the
  knot was abandoned and the unrolling bound kept.  DESIGN.md already records this.

So the honest answer is: sharing is optimal where sharing is possible today, and the entire
Levy gap is concentrated in **cyclic sharing, i.e. recursion**.  That is also Move 4's
stated goal ("share what the levels have in common, k^2 -> k"), for the same reason: it is
where the cost is.

## 3. The e-graph AOT pass: currently a measured no-op

State of the code (`egraph_optimize` in src/compile.c):

- runs ONLY in `do_build`, i.e. only on the AOT path; `eval_form` never calls it;
- implements only BETA and ETA (`eg_saturate` inlines a lambda whose class is applied, and
  eta-collapses `(\x (f x))`), despite the file's comment listing projections, booleans and
  Scott collapses;
- finds equal sub-terms and then throws the sharing away: `eg_extract` rebuilds a TREE, so
  a class with two parents is emitted twice;
- dedup in `eg_add` is a LINEAR SCAN over all nodes, so insertion is O(n^2) -- a scaling
  time bomb, capped only by the `g->nn < 32768` saturation guard;
- has NO test of its own output: `test/egraph.lin` is named for it but only checks
  reduction results (42, 99, 10, 20, projections), which pass by plain beta because the
  interpreter never runs the pass.

Measured contribution (`LIN_NO_EGRAPH=1` A/B on the two `.line` programs):

| program | with e-graph | without | effect |
|---|---|---|---|
| line_binary | 8,238 compiled nodes, 106,243 B | 8,238 nodes, 106,243 B | ZERO, byte-identical |
| line_ffi | 63,890 nodes, 92,853 B | 66,990 nodes, 92,853 B | 4.6% fewer nodes, artifact identical |
| build time | 129 / 264 ms | 120 / 273 ms | within noise |

So on the only programs that exercise it, "e-graphs used for AOT" is not doing anything
measurable -- and where it does fire it does not change the shipped artifact.

## The synthesis

The two concerns are the same concern.  Sharing-as-a-language-feature (a let-bound value
used many times) is already optimal, so the remaining optimality work is RECURSION, and
recursion is also the largest measured compiler cost.  The e-graph is the layer that is
supposed to make those decisions AOT -- sharing (CSE -> fans), precompile-vs-textual, and
the unrolling strategy -- and today it makes none of them, measurably.

So the order that pays:

1. **Recursion AOT (Move 4).**  Share what the k unrolled levels have in common, so a
   recursive def costs O(k) to compile instead of k copies -- attacking the measured 30%.
   This is the real Levy gap and it needs no new core agent if the sharing can be done at
   the net level the way `ct_splice` already shares a precompiled def body.
2. **Then make the e-graph the place those decisions live**, with the standing rule that a
   pass ships only if an A/B on real programs shows it pays -- CSE is the cautionary tale:
   it shrank the compiled net 27x and made the artifact 30x larger.
