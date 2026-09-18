# Knot work-in-progress: verified patch set

Not landed. Everything here is verified to build and to behave as described.
See `DESIGN.md` sections "A2/A3: the knot…", "The `_op` fold path…" and the round notes
for the measurements and the failures that were ruled out.

## What works (verified)

- Self-recursion through the knot: `(peel 1/2/3)` -> 0, `(fact 0)` -> 1,
  `(pair (peel 1) (peel 2))` -> `(0, 0)`, all fast; no 24-fold unrolling, no `_rec`
  sentinel, no widening retry.
- Knot nets are structurally correct (dumped): body = a LAM's principal, `occ` -> `F.1`.
- `enqueue = 1` in `ct_splice` alone is harmless (behaves exactly like HEAD).

## What still breaks

`_op`-wrapper programs under a knot: `(add 1 2)` prints `((\_add 3) <spine>)` (the value is
computed but the closure is left applied), `(mul 2 3)` stuck, g3 stuck.  Folds are guarded
off in this configuration, so the mis-threading is in the **base beta rule** interacting
with knot-shared nodes (`n->dead[n1] = n->dead[n2] = 1` kills a copy the sibling needs).

`LIN_TRACE=1` on `(add 1 2)` shows what that costs: **22,584,025 steps** and nodes up to
18,443,735 for a program HEAD finishes in about thirty — the tail is an unbroken run of
`1.* x 2.*` (APP x DUP) commutations, i.e. the knot inflates the spine-building
applications without ever converging, then the wave loop gives up and prints the partial
structure.  So the symptom to chase is two-sided: runaway fan/app commutation *and* the
result landing in the wrong slot.

**Probe 1 (done, negative but informative).** Dead-flagging the cloned ROOT node makes no
difference at all (same ~7.7 s, same output), so the stray ROOT agent is not the growth.

**Why the growth is expected, and where it must be fixed.** The knot's fan `F` feeds the
define's own references, and those references live *inside the body that `F` duplicates*.
So every γ⋈δ commutation around the cycle produces another copy of the body, and with it
another `F` feeding the same references — the fan meets itself inside a cycle. The engine
already has machinery aimed exactly at that case: the scope word is a non-abelian prefix
injection on commutation (`src/net.c`, top comment) so that two fans meeting inside a cycle
*converge* instead of growing a word — and the commutation rule allocates its copies at
`scope_ext(sm, 1/2)`, i.e. as an extension of the meet. The knot's fan is instead allocated
with a bare `fan_lvl()`, which is fine for tree-shaped sharing (every compiler fan) but is
the suspicious part for a fan in a cycle. Getting the knot fan's gauge right — so a
commutation around the cycle is recognised as the same sharing point rather than a new one
— is one candidate.  But the gauge machinery is in better shape than that suggests:
`fan_lvl()` builds each level as a *path* of bits (`scope_ext` per bit of a counter), the
γ⋈δ rule allocates its copies at `scope_ext(meet, 1/2)` and gives the two new fans the
commuted fan's own gauge, and equal gauges annihilate (`δ⋈δ`) — so fan identity does
propagate and copies of one sharing point do collapse.  What no gauge can fix is this:

**A sharing fan wrapped around a *cyclic* body is divergent by construction.**  `F`'s
principal sits on the body's root agent, and the body contains the reference sites that
`F` feeds.  Every γ⋈δ commutation therefore copies the body — and the copy contains `F`
again, feeding the same sites — so the number of agents grows once per commutation around
the cycle, whatever the gauges say.  That is precisely the 22.5M-step trace: unbroken
`APP × DUP` with nodes climbing to 18M.

The fix is a different knot, not a different gauge: recursion must share the body's
*reduct* through the cycle, i.e. the reference sites should be fed from what the body
*produces* (its result wire), rather than the body being wrapped in a fan and copied per
demand.  Lamping-style systems handle this with brackets/abstractors, which this engine
does not have; the alternative within the current design is to place the sharing point on
the body's output (the value) so a commutation meets an already-copied value rather than
the term that contains the fan.  That is the next construction to try.  Note also that `ct_splice` copies node 0 (ROOT) like
any other node, so a spliced net carries a second ROOT-tagged node whose wires are
deliberately not linked — worth checking when hunting the growth.

## The patch set

1. `src/compile.c` — knot constructor (also change `ct_splice`'s link call to `enqueue = 1`;

   a precompiled body is a normal form so it costs nothing, but a spliced knot body is
   deliberately unreduced and its redexes must enter the active queue or they never run):

```c
int compile_knot(Term *body, const char *name, Net *n, char *err, int errsz) {
  Term *wrap = term_new(TLAM, name, term_copy(body), 0);
  int ok = compile(wrap, n, err, errsz);
  term_free(wrap);
  if (!ok) return 0;
  Port lv = n->wire[0];
  if (lv.node <= 0 || lv.node >= n->nn || lv.port != 0 || n->tag[lv.node] != LAM) {
    snprintf(err, errsz, "knot: body is not a lambda"); return 0;
  }
  Port b = n->wire[lv.node * 3 + 2], occ = n->wire[lv.node * 3 + 1];
  if (b.node < 0 || b.node >= n->nn) { snprintf(err, errsz, "knot: empty body"); return 0; }
  Port f = net_alloc(n, DUP, fan_lvl(), "");
  net_link(n, (Port){f.node, 0}, b, 1);
  if (occ.node >= 0) net_link(n, (Port){f.node, 1}, occ, 1);
  net_link(n, (Port){f.node, 2}, (Port){0, 0}, 0);
  return 1;
}
```

2. `src/lin.h` — `int compile_knot(Term *body, const char *name, Net *n, char *err, int errsz);`
   and `extern int lin_has_knot;`

3. `src/main.c` — `int lin_has_knot = 0;` plus, in `def_precompile`, replace `if (d->rec) return;`
   with `if (d->rec) { def_knot(d, d->rec_body); return; }`, and define:

```c
static void def_knot(Def *d, Term *body) {
  if (!body) return;
  const char *dot = strrchr(d->name, '.');
  const char *bare = dot ? dot + 1 : d->name;
  Guard g; memset(&g, 0, sizeof g);
  guard_push(&g, d->name);
  if (strcmp(bare, d->name)) guard_push(&g, bare);
  Term *ex = expand(term_copy(body), &g);
  free(g.names);
  char err[512]; Net src; net_init(&src, 1 << 14);
  if (compile_knot(ex, bare, &src, err, sizeof err)) { d->compiled = net_copy(&src); lin_has_knot = 1; }
  net_free(&src); term_free(ex);
}
```

4. `src/net.c` — guard the fold edges while a knot is present (head folds in the LAM×APP
   branch of `net_interact`, and `fold_arg`), i.e. `!lin_has_knot &&` on the `lin_fold_ffi`
   / `lin_fold_op` calls and `if (lin_has_knot) return 0;` at the top of `fold_arg`.

5. `src/io.c` — **required by 4** (ASan-proven crash otherwise): these read wires through the
   TU's static `N` and must never leave it stale:

```c
  N = n;   /* at the entry of lin_op_needs_operand, lin_ffi_needs_operand, ffi_ops_concrete */
```

## Acceptance matrix

| program | want |
|---|---|
| `(peel 1)`, `(peel 2)`, `(peel 3)` | `0` |
| `(pair (peel 1) (peel 2))` | `(0, 0)` = `(\f ((f 0) 0))` |
| `(add 1 2)` | `3` |
| `(mul 2 3)` | `6` |
| `(let ((g (mul 2))) (g 3))` | `6` |
| `(let ((g (mul 2))) (pair (g 3) (g 4)))` | `(6, 8)` (hangs on HEAD too) |
| `(let ((g (\x (\y (mul x y))))) (pair (g 2 3) (g 4 5)))` | `(6, 20)` (hangs on HEAD too) |
| `test/selfrecursion.lin`, `test/scott_arith.lin`, full suite + oracle | green |

The programs above are one-liners to type at the prompt (with the repo root as cwd), or
paste into a scratch file *outside* the repo — this note deliberately carries no repro
files, and none belong in the tree.

## Conclusion after round 7: redirect A3 away from the knot

`(peel 1..3)` and `(fact 0)` do reduce correctly through the knot — recursion of depth 1-3
finishes before the copy-around-the-cycle dominates.  Anything deeper (`(fact 1)`, `(mul 2 3)`,
`(add 1 2)`) runs away, for the structural reason above: **any fan placed on a recursive
term sits on a cycle, and every commutation around that cycle copies the body that contains
the fan.**  In Lamping-style systems that is exactly what brackets/abstractors exist to
control; this engine has fans with a gauge discipline but no brackets, so a lazy recursion
knot is not expressible in it.  That is a property of the sharing model, not a bug to hunt.

The redirect that keeps the engine pure and stays inside its model: keep the bounded
unrolling (it is sound and already landed), and attack its *cost* by sharing what the
unrolled levels have in common instead of duplicating whole bodies.  Today
`build_bound_rec` emits `k` textual copies, so a define that recurses through another
recursive define (`_pmul` through `_padd`) carries a 24-fold `_padd` inside *each* of its
own 24 levels — the 30,773 -> 111,933 node oscillation.  Fan-sharing the levels' common
sub-nets (no cycle: each level stays a distinct tree level, but their shared parts become
one node) removes the nesting blow-up without touching the reduction rules, which is
exactly the "fan-share a normalised body rather than copy it" goal the session opened
with — applied to the unrolled net rather than to the recursive name.

## Round 8: precompiling the recursive define — real win, one runaway left

Two changes, tried together as the redirect predicts:

1. `def_precompile`: let self-recursive defines be baked too (`d->rec && !d->term` instead of
   `d->rec`).  Their term is the bounded unravelling — a finite tree, no cycle — and once the
   other recursive defines are baked, references to them inside it become value markers
   instead of copies.
2. `op_value_from_lam`: drop the open-body bail (the lever from round 2).

Measured (core 2,842 lines):

| program | HEAD | with both changes |
|---|---|---|
| `(add 1 2)` | 3, 414 ms | 3, **400 ms** |
| `(mul 2 3)` | stuck | **6, 606 ms** |
| `(let ((g (mul 2))) (g 3))` | stuck | **6, 550 ms** |
| `(peel 1)` | 0, 419 ms | 0, 450 ms |
| `(pair (peel 1) (peel 2))` | `(0, 0)` | `(0, 0)`, 428 ms |
| std load | 433-440 ms | 459-464 ms |
| `test/scott_arith.lin` | green | prints `20`, `3`, then **hangs** |
| `test/selfrecursion.lin` | green | prints `6`, `24`, then **hangs** |

So the nesting-blow-up fix is real — the `_op`-wrapper cases that were stuck on HEAD now
return correct values in half a second — but some *later* case in each suite runs away, which
is why this is reverted rather than landed.  Note the suites print several correct values
first, so it is a specific shape, not a general collapse: the next iteration should find which
expression in `scott_arith.lin` / `selfrecursion.lin` follows the last printed value and trace
it, and it should also consider a size bound on what may be baked (a baked recursive net that
is large is exactly the thing that can run away at run time).

## Round 9: the runaway is `eq`, and it is exactly what the decline guard was for

Bisecting `test/scott_arith.lin` form by form under the round-8 build: every form up to
`(mod 23 5)` -> 3 is correct and fast (388-1155 ms), including `(div 100 5)` -> 20 and
`(mul 6 7)` -> 42.  The runaway is `(eq 42 42)` and `(eq 42 43)`, both of which hang, while
`(lt 5 10)`, `(lt 10 5)`, `(leq 5 5)` and `(gt 10 5)` — same family — are correct in ~400 ms.

That closes the loop on the lever: `def_precompile`'s `lin_stuck_ffi_count` test exists
precisely to refuse caching a define whose open-body precompile β-consumed a closure it
could not fold ("the baked net is broken for composed use").  Removing the *detection* (the
`_op` bail) without replacing it lets such a net be cached, and `eq`'s cached net runs away —
`eq` is the define whose body applies an `_op` closure to free variables in a way that β then
eats.  So the lever must be replaced, not removed: the useful half of round 8 is change (1)
(baking the recursive define, which is what made `(mul 2 3)` and `(let ((g (mul 2))) (g 3))`
correct in ~0.5 s), and the half that must be re-thought is (2), because "free-variable operand"
and "closure that β will destroy" are not the same condition — the fix has to detect the
latter (what β actually consumed) rather than the former (an operand that merely is not
concrete yet).

## Round 10: HEAD's shared-mul hang is a measured deferral livelock (correction to round 8)

Instrumented on unmodified HEAD, `(let ((g (mul 2))) (pair (g 3) (g 4)))`:

```
[NQ 1]   _mul argc=0 sk=0 declines=0     nn=30733  steps=2978
[DEFER 1] lam=45 app=44                  nn=30733
[NQ 2]   _mul argc=1 sk=1 declines=1     nn=111933 steps=41477
[DEFER 20000] lam=45 app=44              nn=111933 declines=20000
[DEFER 60000] lam=45 app=44              nn=111933 declines=27232
```

The net reaches 111,933 nodes once and then **freezes**; the `_mul` redex is re-examined and
re-deferred at ~2400/s for ever, with `argc=1 sk=1` — one operand decodes, one slot is
"present, not concrete" and never becomes concrete because nothing else in the net can run.
`declines` never reaches the `1 << 15` cap because folds elsewhere keep resetting it.  So the
shared case is a **livelock**, not a blow-up (the growth happens once, earlier).

**Correction to round 8's table.**  `(add 1 2)`, `(mul 2 3)` and `(let ((g (mul 2))) (g 3))`
already produce 3/6/6 on unmodified HEAD in 440-530 ms; the "stuck" column there was measured
on knot builds, not on HEAD.  Change 1 alone (precompile the self-recursive define)
is therefore **safe but neutral** — `(eq 42 42)` still works, `(scott_arith)` prints its
correct values, and timings are unchanged (408-709 ms) — so it is not worth landing by itself.
`let_mul_shared` and `let_mul_lambda` hang on HEAD and in every variant tried.

**The quiescence rule (tried, did not fire).**  Spending the deferral budget when the drain
sees `changed == 0 && n->atop == 0` never triggers: the re-queued blocked pair *is* the thing
in the queue, so `atop` is never 0 there.  The right signal is **progress**, not emptiness —
capture `n->steps` when the wave starts and spend the budget when a wave leaves it unchanged
(deferring is not an interaction, so a wave that only re-examined deferred pairs leaves
`steps` exactly as it was).  That is the next thing to try; the monotonic-`declines` variant
is separately known to be unsound at a small cap (`modules.lin` 225 -> 1).

## Round 11: why `steps` cannot be the progress signal

The progress-based expiry was implemented as "if a wave leaves `n->steps` unchanged while
redexes are still deferred, spend the deferral budget" (with a two-wave debounce).  It does
not fire: **a deferral is itself an interaction attempt and increments `n->steps`**, so a
livelocked wave always looks like progress (the instrumented trace shows exactly that —
`steps` creeping 41,477 -> 41,478 -> ... between deferrals).  `changed` is no better: the
deferral path returns 1 from `net_interact`, so it counts as handled there too.

So the measure has to be *completed rewrites*, not attempts: one counter incremented where a
rule actually rewrites (next to the `return 1`s that follow real work, not the deferral
return), and the drain spends the budget when a wave finishes with that counter unchanged and
blocked pairs present.

Two shortcuts are ruled out for the record, both because β of a deferred pair can *destroy*
shared operand structure, which is why the wait exists at all:

- a small per-pair or net-lifetime cap (round 2: `modules.lin` 225 -> 1);
- "queue empty ⇒ beta" — the drain always runs with `atop == 0`, so that degenerates into
  "defer once, then beta", the same over-eager rule.

The sound discriminator is genuinely "nothing else can ever run", which is why it must be
based on real rewrites rather than on attempts, queue state, or step counts.
