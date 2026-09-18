# Move 2 (TYPES AOT): measurements and design

## Measured baseline

Startup cost of `./lin -e '1'`: **425 ms**, of which **421 ms is the std load**
(`LIN_STD=scratch/empty.lin` → 4 ms).

Instrumented `type.c` (temporary counters, since reverted) over a std load:

```
[types] calls=512 typecheck_ms=371.9 gen_calls=519 env_scans=160024 fv_visits=11928065
```

So type checking is **371.9 ms of the 421 ms** — the user's "~370 of ~410 ms" is exact.
319 defs, 512 `type_check*` calls.

The cost is not the number of defs: it is `generalize`'s env loop.  519 `generalize`
calls perform **160,024 env-entry scans** — ~308 entries each — and each scan walks
the whole scheme type (11.9M `fv` visits ÷ 160,024 ≈ **74 nodes per entry**).  That
is the O(envn × |scheme|) blow-up:

```c
static Scheme generalize(Type *t) {
  int f[256], fn = 0; fv(t, f, &fn);
  for (int i = 0; i < envn; i++) {
    int g[256], gn = 0; fv(env[i].s.t, g, &gn);   /* recomputed on EVERY generalize */
    ...pairwise filter...
  }
```

Three further avoidable costs in the same path:

- `type_check*` calls `env_load_defs()`, which re-`push`es all 319 defs every time
  (512 × 319 ≈ 163k pushes, each a 256-byte `snprintf` ≈ 42 MB of copying).
- `env_find` is a linear `strcmp` scan over the env for **every** variable
  occurrence, and falls back to `def_find`, another linear scan.
- `generalize` is called even when the inferred type has no free vars at all.

## Design

### 1. Order-independent `generalize` + O(1) lambda-bound fast path

Replace the pairwise filter with a **maintained env free-variable multiset**: a
refcount array indexed by type-var id (ids are dense — `next_id++` per `tvar()`), so
membership is `rc[id] != 0` in O(1).  `generalize` then costs O(|t|) regardless of how
many defs are loaded, and the answer is a function of the env as a *set* rather than of
its iteration order — which is what "order-independent" buys, and what makes the
parallel/any-order def checking below sound.

The subtlety that makes a naive fast path wrong: a λ-bound entry is pushed as
`(Scheme){.nq = 0, .t = a}` where `a` is a **fresh var that is unified later**, so its
free-var set is not knowable at push time.  Contributing only `a`'s own id over-generalises.
Counter-example:

```
(\x (x 5))     ;  x : a, then unify(a, num -> c) makes a = (num -> c)
```
the body type is `c`, and `c` must **not** be quantified, because it is free in the env
through `x`.  So the fast path must follow links: when a var that is currently an env root
is linked to a type, add that type's free vars to the set.  Attribute the additions to the
*root var* (not to the entry) so removal on pop stays exact and O(1) amortised:
`rc[v]` counts direct membership, and a per-var list records what was added because `v`
got linked, released when `rc[v]` returns to 0.

Def entries never mutate (instantiation copies), so they are registered once and only
the handful of λ-bound roots need the link hook — the recomputation is therefore rare,
not per-`generalize`.

### 2. Type cache

- Fix `env_load_defs` to rebuild only when a def was added/typed since last time
  (a `ndefs` generation counter): turns 163k pushes into 319.
- Memoise `instantiate`/`generalize` per (scheme, generation) so repeated occurrences of
  the same def in a body do not re-walk its type.
- Replace `env_find`/`def_find` linear scans with a name→index hash.

### 3. Parallel def checking

Order-independent `generalize` is the prerequisite: today def *n*'s scheme depends on the
push order of defs 0..n-1, so checking cannot be reordered.  With the env as a set, defs
that do not reference each other are independent and can be checked concurrently, with a
worklist for those that do (a def whose dependency is not yet typed is deferred, not
failed).  `process_def`'s `qualify_free`/`build_bound_rec` work is per-def and already
independent.

Gate: `test/types.lin`, `test/datatype.lin`, `test/adt_types.lin` plus the whole suite
must stay green, and the inferred schemes must be **byte-identical** to before — this is a
pure performance/AOT change, and any scheme difference means the refcount set is not
exactly equivalent to the pairwise filter.

## Result (step 1 landed)

| | before | after |
|---|---|---|
| startup with std | 425 ms | **102 ms** |
| std load | 421 ms | **98 ms** |
| full suite | 58.9 s | **38.6 s** |

The env-entry scans (160,024) and their 11.9M `fv` visits are gone: `generalize`
is now O(|t|), its answer is a set lookup against `envrc`, and each def scheme's
free variables are registered **once per def** instead of once per check.

Equivalence was checked independently against a HEAD build: 26 expressions
spanning polymorphism, let-generalization, recursion, ADTs and higher-order use
produce byte-identical `:type` output — including identical type-variable ids,
which is the strong form of "quantifies exactly the same set in the same order".

### Still to do for this move

Step 1 removed the algorithmic blow-up; the remaining 98 ms is per-def inference
work.  The planned **type cache** (share inference of a repeated sub-term /
avoid re-walking a scheme per occurrence) and **parallel def checking** (now
sound to reorder, which is what order-independent `generalize` bought) are the
next increments, together with replacing the linear `env_find`/`def_find`
`strcmp` scans over 319 defs with a name hash.  None of these is needed for
correctness; they are what is left of the 98 ms.
