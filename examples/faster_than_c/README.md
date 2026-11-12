# Early comparisons with C

These three programs were Lin's first comparisons with C. They are kept for
reference and are **not** the project's benchmarks: the maintained, like-for-like
suite is in [`bench/`](../../bench/README.md).

Each pair here compares programs that do different amounts of work, so the
timings do not measure the languages against each other:

| Pair | What differs |
|------|--------------|
| `bench_branch.c` / `bench_branch.lin` | The C calls `branch(d - 1)` twice; the Lin binds it once with `let`. The Lin program does exponentially less work by construction |
| `bench_stream.c` / `bench_stream.lin` | The C fills a 10-million-element buffer; the Lin reads a prefix of a lazy stream |
| `bench_linden.c` / `bench_linden.lin` | The Lin side calls a C plugin, so both sides are C |

What the pairs do illustrate is real: a shared subcomputation is evaluated once,
and a lazy structure costs only what is read from it.

`run_benchmarks.sh` builds and runs all three.
