# Lin Examples

Fresh, self-verifying example programs demonstrating what makes Lin interesting.
Each `.lin` is a self-contained Lin **program**: run it and every top-level
expression prints one `=> <value>` line.  Examples that carry `; expect`
annotations are value-checked automatically by `examples/run_verifier.sh`.

```bash
# Run a single example
./lin examples/pure-functional/scott_lists.lin

# Value-check every non-interactive example (14 PASS / 5 interactive)
./lin                  # from the repo root, then:
bash examples/run_verifier.sh ./lin
```

## Clusters

### optimization/ — why Lin programs are already optimal
Lin executes λ-terms directly as interaction nets (Lévy-/*opportunistic* beta
sharing), so the *reduction strategy* is the language: a program reduces to its
optimal interaction-net form by construction, with no separate optimizer pass.

- `redundant_compute.lin` — the same repeated subterm written twice folds to one
  shared net node; exact values.
- `sharing_folds.lin` — **makes the fold observable**: after a shared redex,
  `(folded)` is true and the native-fold counter advanced.
- `church_numerals.lin` — Church-encoded arithmetic (`c_add`/`c_mul`/`c_pow`)
  sharing `f` and `x` across iterations.
- `aot_vs_interpret.lin` *(interactive)* — the same source interpreted and
  AOT-compiled to a `.line` container run the identical optimal net
  (`./lin build <f> -o out.line && ./lin out.line`); `-b` is a measurement flag,
  not an optimizer.

### pure-functional/ — the purely functional, sharing data model
No mutation; collections are values. Scott-encoded lists/pairs/trees and
Church-encoded self-iterating folds; `queue_peek` twice doesn't consume,
inserting into a map leaves the original intact.

- `scott_lists.lin` — Scott lists, `nth`, `list_eq`, Church `c_map`/`c_length`/
  `c_reverse`.
- `immutable_adt.lin` — a user `(datatype ...)` + `match`, and the std tree
  module, immutably.
- `functional_collections.lin` — queue / stream (`nats_from`, `stream_nth_c` /
  `stream_take`) / set / map, all pure.

### logic-sat/ — SAT and constructive proofs
- `sat_solve.lin` — constructive SAT witness + O(1) certificate check.
- `curry_howard.lin` — Curry–Howard proof terms (Modus Ponens, De Morgan) as
  pure λ-terms that normalize to `true`.
- `tseitin.lin` — a Tseitin 3-CNF with a full truth table and certificate check.

### numeric-float/ — numeric and float kernels
- `float_math.lin` — `fsqrt`/`ffloor`/`fadd`/`fmul`, `lerp`, `clamp`,
  `deg2rad`/`rad2deg`.
- `recurse_arith.lin` — recursive arithmetic over Scott numerals.
- `tiny_kernel.lin` — sum-of-squares and a short geometric series: one pure
  expression, one normal form.

### systems-ffi/ — the FFI / systems boundary
- `ffi_basics.lin` — `puts`, `getenv`, `ccall1`, `dlopen`, `system`
  (non-deterministic values prefix-matched).
- `driver_folds.lin` — the pluggable reduction driver: `set_driver cpu/simd`,
  `get_driver`, and `folds` accounting, values identical across drivers.
- `interactive_repl.lin` *(interactive)* — a continuation-passing REPL built
  from `io_prompt`/`io_read`/`io_print`.

### interactive/ — runnable demos
- `driver_tour.lin` *(interactive)* — switch `set_driver cpu → simd → gpu`
  live and watch `get_driver`/`folds`; the canonical cross-driver selftest
  story. GPU self-degrades to CPU when no Vulkan device is present.
- `repl_calc.lin` *(interactive)* — a pure calculator REPL loop (no mutable
  state).
- `game_demo.lin` *(interactive)* — a small turn-based prompt/response demo.

Interactive examples are intended to be run through a terminal (`./lin <file>`
with piped stdin, or via `./lin -e '...'`) and are reported by the verifier as
*interactive* rather than value-checked.