# Pending benchmarks

Programs written but not yet run by `bench/run.sh`, because Lin cannot yet run
them in a time worth measuring. Each has its C counterpart beside it.

| Program | What is missing |
|---------|-----------------|
| `regexredux` | The function compiler declines `std/regex.lin`'s matcher, so matching runs by net reduction: it did not finish on 300 characters in two minutes, against a 200,000-character input. The library itself is checked against Python's `re` in `test/regex.lin`. |
