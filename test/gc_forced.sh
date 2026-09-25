#!/usr/bin/env bash
# ================================================================================
# Reclamation must not change the answer.
# --------------------------------------------------------------------------------
# The collector is dormant in a normal run: it needs a million live nodes, and the
# suite peaks an order of magnitude below that.  Which is exactly why it rotted --
# it had two independent defects (a ROOT-only root set, and a renumbering pass that
# invalidated every node index held across a reduction) and NOTHING was exercising it.
#
# So this suite runs the same programs twice, once with the threshold forced down to
# a value that makes every wave a collection opportunity, and requires the output to be
# byte-identical.  It hard-codes no expectations: the un-forced run IS the expectation,
# which is what makes it a differential for the collector rather than a second copy of
# the value suite.
#
# usage: test/gc_forced.sh [LIN_BIN] [LIN_STD_DIR]
# ================================================================================
set -e
. "$(dirname "$0")/common.sh"
lin_test_env "${1:-}" "${2:-}" || exit 1

# Programs chosen for shape rather than size: arithmetic, sharing, recursion depth, containers,
# and the two (vector, numbers) that a wrong anchor set once truncated.
PROGRAMS="test/numbers.lin test/levels.lin test/let.lin test/recursion.lin test/selfrecursion.lin
          test/vector.lin test/map.lin test/set.lin test/trees.lin test/pairs.lin"
GC=200

pass=0; fail=0
for f in $PROGRAMS; do
  [ -f "$f" ] || continue
  a=$(timeout 120 "$LIN_BIN" "$f" 2>/dev/null || true)
  b=$(LIN_GC=$GC timeout 300 "$LIN_BIN" "$f" 2>/dev/null || true)
  if [ -n "$a" ] && [ "$a" = "$b" ]; then
    pass=$((pass+1))
  else
    fail=$((fail+1))
    echo "FAIL $f: reclamation changed the answer (LIN_GC=$GC)"
    diff <(printf '%s\n' "$a") <(printf '%s\n' "$b") | head -10
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "gc_forced: OK ($pass programs identical with reclamation forced on every wave)"
else
  echo "gc_forced: $fail of $((pass + fail)) programs changed under forced reclamation"
fi
exit $fail
