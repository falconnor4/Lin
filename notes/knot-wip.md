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
result landing in the wrong slot.  Note also that `ct_splice` copies node 0 (ROOT) like
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
