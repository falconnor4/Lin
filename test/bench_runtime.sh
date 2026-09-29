#!/usr/bin/env bash
# ============================================================================
# RUNTIME WORK: a container must do the work the build could not do.
# ----------------------------------------------------------------------------
# test/bench_runtime.lin reads N from the environment, so the build CANNOT decide
# it.  That makes it the one workload here where a driver's run-time recognition
# actually runs at run time: the rest of the corpus is closed, `lin build`
# evaluates it all, and the artifact ships at ~1 reduce step (this harness
# measures the contrast -- see `numbers` below).
#
# WHAT THIS PINS
#   1. DATA SIZE -- the interpreter's answer is (sumto N) = N(N+1)/2, computed
#      HERE, not copied from the engine, for several N.  A benchmark whose answer
#      is not checked measures nothing.
#   2. THE ARTIFACT TRACKS ITS OWN ENVIRONMENT -- the artifact is built with
#      BENCH_N ABSENT and run once per N: it must answer for each run's own
#      environment.  An artifact that had baked the build's answer would print
#      ONE number for every N, which is exactly the failure this catches (it is
#      the shape of the bug test/build_observe.lin documents).  This is also the
#      attestation: a suite where the build really did everything would pass a
#      value differential vacuously.
#   3. AGGRESSIVE SLOT RECYCLING -- the same artifact answers the same way under
#      LIN_GC=200, where freed node indices are handed straight back out.  Any
#      driver state keyed by node index (a match cache, a recognition table, a
#      carried section) is wrong the moment a slot it named is reused, so this is
#      the guard that a derived entry never becomes an ANSWER: a stale entry may
#      cost a missed optimisation, never a different number.
#   4. THE CORPUS CONTRAST -- test/numbers.lin, whose work IS closed, is reported
#      folded-by-the-build next to the benchmark.  That contrast is the reason
#      the benchmark exists.
# ============================================================================
set -u
BIN=${1:-./lin}
STD=${2:-std}
STD_DIR=$(cd "$STD" && pwd)
PASS=0
FAIL=0
fail() { echo "  FAIL: $*"; FAIL=$((FAIL+1)); }
ok() { PASS=$((PASS+1)); }

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

BENCH="$PWD/test/bench_runtime.lin"
[ -f "$BENCH" ] || BENCH="test/bench_runtime.lin"

# `N` is ABSENT while building, so nothing the build does can answer the program.
ART="$TMP/bench_runtime.line"
if env -u BENCH_N LIN_STD_DIR="$STD_DIR" LIN_STD="$STD_DIR/std.lin" \
       timeout 300 "$BIN" build "$BENCH" -o "$ART" >"$TMP/build.log" 2>&1; then
  ok
else
  fail "the build refused test/bench_runtime.lin"; cat "$TMP/build.log"
fi

run_art() { env "$@" LIN_STD_DIR="$STD_DIR" timeout 300 "$BIN" "$ART" 2>/dev/null; }
run_int() { env "$@" LIN_STD_DIR="$STD_DIR" LIN_STD="$STD_DIR/std.lin" timeout 300 "$BIN" "$BENCH" 2>/dev/null; }

# ---- 1+2: the answer is N(N+1)/2, from the harness, on both paths, per N ----
for n in 0 1 6 10 14 20; do
  want=$(( n * (n + 1) / 2 ))
  got=$(run_int BENCH_N=$n)
  [ "$got" = "=> $want" ] && ok || fail "interpreter: N=$n got '$got' want '=> $want'"
  got=$(run_art BENCH_N=$n)
  [ "$got" = "=> $want" ] && ok || fail "artifact: N=$n got '$got' want '=> $want'"
done

# ---- the artifact must be RUN-TIME dependent, not baked -------------------
a=$(run_art BENCH_N=6); b=$(run_art BENCH_N=10)
[ "$a" != "$b" ] && ok || fail "artifact answered '$a' for both N=6 and N=10: its work was baked"

# ---- 3: the same answers with slots recycled aggressively -----------------
gc_fail=0
for n in 1 6 10 14 20; do
  want=$(( n * (n + 1) / 2 ))
  got=$(run_art LIN_GC=200 BENCH_N=$n)
  [ "$got" = "=> $want" ] || { fail "LIN_GC=200 N=$n got '$got' want '=> $want'"; gc_fail=1; }
done
[ "$gc_fail" = 0 ] && ok
got=$(env -u BENCH_N LIN_GC=200 LIN_STD_DIR="$STD_DIR" timeout 300 "$BIN" "$ART" 2>/dev/null)
[ "$got" = "=> 0" ] && ok || fail "LIN_GC=200 with BENCH_N unset got '$got' want '=> 0'"

# ---- 4: the corpus contrast, reported and pinned --------------------------
CLOSED="$PWD/test/numbers.lin"
[ -f "$CLOSED" ] || CLOSED="test/numbers.lin"
closed_steps=$(env LIN_STD_DIR="$STD_DIR" LIN_STD="$STD_DIR/std.lin" LIN_PASSES=1 \
                 timeout 300 "$BIN" build "$CLOSED" -o "$TMP/numbers.line" 2>&1 |
               sed -n 's/.*runtime=\([0-9]*\) reduce steps.*/\1/p' | tail -1)
open_steps=$(env -u BENCH_N LIN_STD_DIR="$STD_DIR" LIN_STD="$STD_DIR/std.lin" LIN_PASSES=1 \
               timeout 300 "$BIN" build "$BENCH" -o "$TMP/bench_runtime2.line" 2>&1 |
             sed -n 's/.*runtime=\([0-9]*\) reduce steps.*/\1/p' | tail -1)
echo "  closed suite (test/numbers.lin)      artifact runtime: ${closed_steps:--} reduce step(s)"
echo "  open benchmark (test/bench_runtime)  artifact runtime: ${open_steps:--} reduce step(s) before the observation"
# The closed suite is the point of comparison: the build folds it away.  The open one reports the same
# number for the same reason in reverse -- needed order stops at the observation, so the *reported*
# figure counts only what happens before it.  What the artifact then does is measured by (2) above,
# which no bake can fake.
if [ "${closed_steps:-x}" = "1" ]; then ok; else fail "numbers.lin artifact ran ${closed_steps:-?} steps; the contrast this harness reports is gone"; fi

if [ "$FAIL" -eq 0 ]; then
  echo "bench_runtime: OK ($PASS checks: interpreter and artifact agree on N(N+1)/2 for 6 sizes," 
  echo "               artifact proven run-time dependent, identical under LIN_GC=200)"
  exit 0
fi
echo "bench_runtime: $FAIL check(s) failed"
exit 1
