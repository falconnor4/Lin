# Recursion: measured baseline, and the first win

## Sharing is verified Levy-optimal for acyclic values (rigorous)

Earlier I claimed this from a test that used `pair`/`fst` as the uses -- and
`fst (pair v v)` NEVER FORCES the second `v`, so those "extra uses" were discarded and
the test was confounded.  Redone with uses that are genuinely forced (`(add v ...)` nested),
measuring the cost attributable to the shared computation against literal baselines:

    baselines (no computation to share)   2 uses: 17225   3 uses: 38185
    duplicated (M written out)             2 uses: 133505  3 uses: 212605
    shared (let-bound M)                   2 uses: 75537   3 uses: 96668

    per-mul cost in context, derived from the DUPLICATED pair:  58140  (and 58140 again)
    cost attributable to M when shared:  2 uses: 58312   3 uses: 58483

So the shared computation costs exactly ONE mul (58,140) no matter how many times it is
used, with ~171 steps of marginal overhead per extra forced use.  Sharing is genuinely
Lévy-optimal for acyclic reused values, now on sound evidence.

## Recursion is the whole remaining gap, and it is expensive at BUILD time

Referencing one recursive def, at depth 0 -- i.e. hitting the base case immediately, never
recursing -- against the identical program with no recursive def:

| | compiled nodes | artifact |
|---|---|---|
| no recursive def | 333 | 14,254 B |
| one recursive def, depth 0 | **1,280** | **423,502 B** |

4x the compiled nodes and 30x the artifact, for a recursion that never happens.  The reason
is `build_bound_rec`: a recursive def is emitted as k=24 copies of its body, producing
`f (f (... (f base)))`, and that entire chain exists in the net whether or not the depth
ever needs it.  Both programs compacted to the SAME 3 live nodes / 66 bytes, so the extra
was pure baggage.

## First win: trim the gauge table before serialising (landed)

Parsing the header of the 423,502-byte artifact showed where it actually went:

    version=2  nn=3  scn=52920  nnamed=2
    node arrays = 66 B     scope table = 423,360 B

**99.98% of the artifact was the gauge table** -- 52,920 entries against a 3-node net.
Those gauges belong to the k-unrolled levels: reduction erased the nodes, `net_gc` drops
the nodes, and nothing ever dropped their gauges.

`net_trim_scopes` marks the entries live nodes reference, copies them in order (so a
referenced range stays contiguous and remapping its start suffices), remaps every node's
offset, and sets any node holding a stale offset to `scope_nil()` so nothing can point past
the trimmed table.  Called at the top of `net_save_line`, so every artifact benefits.

| artifact | before | after |
|---|---|---|
| no recursive def | 14,254 B | **142 B** |
| one recursive def, depth 0 | 423,502 B | **142 B** |
| line_binary.line | 106,243 B | 104,731 B |
| line_ffi.line | 92,853 B | 92,853 B |

All outputs unchanged; gate green (53 suites / 978 assertions, both container tests, and
the independent oracle).

## What remains for Levy-optimal recursion (both AOT and runtime)

Trimming fixed the *symptom*.  The disease is that recursion is UNROLLED rather than
SHARED: k body copies at compile time, and a runtime whose work is bounded by k rather than
by the depth actually needed.  A Lévy-optimal recursion shares one body and reduces it
cyclically -- the knot -- which DESIGN.md records as diverging ("a fan wrapped around a
cyclic body is divergent by construction") and as needing either active erasure or a level
discipline in which the cycle's fans annihilate.

Two things changed since that was written, and they are why a retry is worth it:

1. The `_op`/`_ffi` fold is no longer in the core.  It is a pre-emptor driver that claims a
   redex only when it can actually fold it, and parks (with a core drain point) otherwise.
   The recorded knot failures were dominated by fold-stranding -- `(add 8 5)` reducing to
   `((\_add 13) <spine>)` because the fold never ran -- and that machinery is gone.
2. Sharing is now verified optimal for the acyclic case, so the baseline the knot has to
   beat is known, and the gauge discipline's behaviour on fans is measured rather than
   assumed.

Checkpoints for the knot, in the order that makes failure cheap to localise:

  a. compile ONE body and wire the self-reference through a fan, for the SINGLE,
     linear-self-recursion case only (the case DESIGN records as having worked: peel 3->0,
     fact 4->24, sumto 5->15, pow2 4->16);
  b. require the net to become inert (no redex firings at a stable node count) -- DESIGN's
     recorded divergence was exactly a failure of this;
  c. require compile nodes to stop scaling with k (the quantifiable AOT goal);
  d. require runtime steps to scale with the DEPTH needed, not with k;
  e. only then widen to multi-reference recursion, and only if the oracle stays green.
