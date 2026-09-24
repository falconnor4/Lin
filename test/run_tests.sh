#!/usr/bin/env bash
# ================================================================================
# Lin test runner (working-tree aware)
# --------------------------------------------------------------------------------
# Runs the full Lin Confluence & Stability suite against a binary + std of your
# choice, rooted at the repository checkout.  Defaults to `./lin` (built from
# the current working tree, so uncommitted changes ARE tested - unlike `nix run
# .#test`, which only sees git-committed content because flakes stage `src = ./`).
#
# Usage:
#   test/run_tests.sh [LIN_BIN] [LIN_STD_DIR]        # run everything
#   LIN_BIN=./lin test/run_tests.sh
#   LIN_BIN=./lin LIN_STD_DIR=./std make test
#
# Mirror of flake.nix's `lin-test` runner (Tiers 1-5); keep both in sync.
# ================================================================================

set -e
. "$(dirname "$0")/common.sh"     # ROOT / LIN_BIN / STD_DIR resolution, shared (see test/common.sh)
lin_test_env "${1:-}" "${2:-}" || exit 1

pass=0; fail=0; total_checks=0
t_start=$(date +%s%3N 2>/dev/null || date +%s)

. "$ROOT/test/expect.sh"          # the shared `; expect` matcher (see test/expect.sh)

run_test() {
  f="$1"
  t0=$(date +%s%3N 2>/dev/null || date +%s)
  lin_expect_check "$LIN_BIN" "$f"
  t1=$(date +%s%3N 2>/dev/null || date +%s)
  dur=$((t1 - t0)); total_checks=$((total_checks + EXP_N))
  if [ "$EXP_OK" = 1 ]; then pass=$((pass+1)); printf "PASS %-32s (%2d checks, %3dms)\n" "$f" "$EXP_N" "$dur"
  else fail=$((fail+1)); printf "FAIL %-32s (got %d want %d)\n" "$f" "$(printf '%s\n' "$EXP_GOT" | grep -c . || true)" "$EXP_N"
    echo "--- want ---"; printf '%s\n' "$EXP_WANT"
    echo "--- got  ---"; printf '%s\n' "$EXP_GOT"
  fi
}

printf "Running Lin Confluence & Stability Test Suite against %s\n" "$LIN_BIN"

printf "[Tier 1: Core Interaction Calculus & Primitives]\n"
for f in test/levels.lin test/basics.lin test/booleans.lin test/combinators.lin test/pairs.lin test/scott.lin test/scott_arith.lin test/float.lin test/vector.lin test/math.lin test/strings.lin test/string.lin test/adts.lin test/multi_file.lin test/modules.lin test/numbers.lin test/higher_order.lin test/let.lin test/test_escapes_utf8.lin test/types.lin test/datatype.lin test/adt_types.lin test/loop.lin; do
  run_test "$f"
done

printf "[Tier 2: Foreign Function Interface & System Drivers]\n"
for f in test/float_share.lin test/ffi.lin test/ffi_advanced.lin test/ffi_systems.lin test/driver_gpu.lin test/gpu_dispatch.lin test/unison.lin test/simd_fold.lin; do
  run_test "$f"
done

# Operands that only exist at RUN time (via getenv), so the folds they feed cannot be resolved at
# compile time.  N is what the program reads; it is fixed so the assertions can state values.
N=6 run_test test/runtime_ffi.lin

# ----------------------------------------------------------------------------
# Tier 2.5: Canonical cross-driver selftest
#   Runs std/selftest.lin under the base CPU engine (golden) and under every
#   registered driver, requiring value-for-value equality (test/driver_selftest.sh).
#   This is the CONTRACT any current or future driver must satisfy.
# ----------------------------------------------------------------------------
DS_LOG=$(mktemp)
if bash test/driver_selftest.sh "$LIN_BIN" "$STD_DIR" >"$DS_LOG" 2>&1; then
  pass=$((pass+1)); total_checks=$((total_checks + 46)); echo "PASS test/driver_selftest.sh (2 drivers x 23 probes)"
  rm -f "$DS_LOG"
else
  fail=$((fail+1)); echo "FAIL test/driver_selftest.sh"; cat "$DS_LOG"; rm -f "$DS_LOG"
fi

# The driver ABI's other half: what happens when a hook misbehaves.  A parallel wave cannot grow the
# net, so an arg_fold that allocates past the wave's reservation used to write past the arrays
# (measured: SIGSEGV, ASan heap-buffer-overflow, `free(): invalid pointer`).  It is now diagnosed.
PG_LOG=$(mktemp)
if ! command -v python3 >/dev/null 2>&1; then
  fail=$((fail+1)); echo "FAIL test/parallel_guard.py (python3 not found)"
elif python3 test/parallel_guard.py "$LIN_BIN" "$STD_DIR" >"$PG_LOG" 2>&1; then
  pass=$((pass+1)); total_checks=$((total_checks + 2)); echo "PASS test/parallel_guard.py ($(tail -1 "$PG_LOG"))"
else
  fail=$((fail+1)); echo "FAIL test/parallel_guard.py"; cat "$PG_LOG"
fi
rm -f "$PG_LOG"

# ----------------------------------------------------------------------------
# Tier 2.6: Independent soundness oracle
#   The sharing-sensitive files (sat / sat_verify / tseitin) are checked against
#   an independent evaluation of their boolean formulas rather than against their
#   own `; expect` comments: the suite previously ASSERTED the wrong values the
#   unsound fan sharing produced (sat_verify.lin documented its own answer as a
#   "superposition collapse false negative").  Editing an expectation can no
#   longer make an unsound engine pass.
# ----------------------------------------------------------------------------
SO_LOG=$(mktemp)
if ! command -v python3 >/dev/null 2>&1; then
  fail=$((fail+1)); echo "FAIL test/soundness_enum.py (python3 not found)"
elif python3 test/soundness_enum.py "$LIN_BIN" "$STD_DIR" \
     test/sat.lin test/sat_verify.lin test/tseitin.lin >"$SO_LOG" 2>&1; then
  pass=$((pass+1)); total_checks=$((total_checks + 35)); echo "PASS test/soundness_enum.py (35 independent evaluations)"
  rm -f "$SO_LOG"
else
  fail=$((fail+1)); echo "FAIL test/soundness_enum.py"; cat "$SO_LOG"; rm -f "$SO_LOG"
fi

# ----------------------------------------------------------------------------
# Tier 2.75: Lévy optimality -- the engine's actual headline claim.
#   A value-based test cannot see a re-reduced shared redex: the answer is still right, only the
#   work is wrong.  test/optimality.py measures the work instead (see its docstring).
# ----------------------------------------------------------------------------
OPT_LOG=$(mktemp)
if ! command -v python3 >/dev/null 2>&1; then
  fail=$((fail+1)); echo "FAIL test/optimality.py (python3 not found)"
elif python3 test/optimality.py "$LIN_BIN" "$STD_DIR" >"$OPT_LOG" 2>&1; then
  pass=$((pass+1)); total_checks=$((total_checks + 12)); echo "PASS test/optimality.py ($(tail -1 "$OPT_LOG"))"
else
  fail=$((fail+1)); echo "FAIL test/optimality.py"; cat "$OPT_LOG"
fi
rm -f "$OPT_LOG"

printf "[Tier 3: Constraint Satisfaction & Term Rewriting]\n"
for f in test/sat.lin test/sat_verify.lin test/tseitin.lin test/tsp.lin test/egraph.lin; do
  run_test "$f"
done

printf "[Tier 4: Non-Trivial Workloads & Confluence Invariants]\n"
for f in test/graph.lin test/map.lin test/set.lin test/queue.lin test/stream.lin test/stress_wavefront.lin test/nqueens.lin test/sudoku.lin test/trees.lin test/lists.lin test/algorithms.lin test/recursion.lin test/recursion_share.lin test/selfrecursion.lin test/maybe_either.lin; do
  run_test "$f"
done

# ----------------------------------------------------------------------------
# Tier 5: Container (.line) build & execution invariants
#   Each "src.lin:EXPECTED" program is compiled to a .line container, verified
#   executable + shebang'd, run through the engine and (if /usr/bin/env exists)
#   executed directly, and both outputs must equal EXPECTED.
# ----------------------------------------------------------------------------
t0=$(date +%s%3N 2>/dev/null || date +%s)
TMP_DIR=$(mktemp -d)
trap 'rm -rf "$TMP_DIR"' EXIT

# The loop below asserts one hard-coded string for two programs, which left the whole AOT
# pipeline (e-graph saturation, precompile/splice, net_gc, the serializer) nearly unchecked.
# test/aot_equiv.py asks the general form of the same question -- does the artifact print what
# the interpreter prints -- over a curated case set; its docstring records the miscompile that
# motivated it.  It belongs to this tier because it is a container invariant, not a language one.
AE_LOG="$TMP_DIR/aot_equiv.log"
if ! command -v python3 >/dev/null 2>&1; then
  fail=$((fail+1)); echo "FAIL test/aot_equiv.py (python3 not found)"
elif python3 test/aot_equiv.py "$LIN_BIN" "$STD_DIR" >"$AE_LOG" 2>&1; then
  pass=$((pass+1)); total_checks=$((total_checks + 28)); echo "PASS test/aot_equiv.py ($(tail -1 "$AE_LOG"))"
else
  fail=$((fail+1)); echo "FAIL test/aot_equiv.py"; cat "$AE_LOG"
fi

line_total=0; line_fail=0
for spec in "test/line_binary.lin:LINE_BINARY_OK: 43" "test/line_ffi.lin:FFI_LINE_OK: 144"; do
  src="${spec%%:*}"; want="${spec#*:}"; name="$(basename "$src" .lin)"
  line=$((line_total + 1))
  "$LIN_BIN" build "$src" -o "$TMP_DIR/$name.line"
  lok=1
  # An artifact is a deliverable: its size is a first-class invariant.  Gauge representation
  # once inflated these files 27x (a level bit-word spilling to a per-net table) and no value
  # test noticed, so the container tier asserts a bound as well.
  sz=$(wc -c < "$TMP_DIR/$name.line")
  [ "$sz" -le 300000 ] || { echo "FAIL: $name.line is $sz bytes (bound 300000)"; lok=0; }
  [ -x "$TMP_DIR/$name.line" ] || { echo "FAIL: $name.line not executable"; lok=0; }
  head -n 1 "$TMP_DIR/$name.line" | grep -q '^#!' || { echo "FAIL: $name.line missing shebang"; lok=0; }
  out1=$("$LIN_BIN" "$TMP_DIR/$name.line")
  [ "$out1" = "$want" ] || { echo "FAIL: $name engine output '$out1' (want '$want')"; lok=0; }
  # The container's shebang is `#!<realpath argv[0]>`, i.e. absolute, so executing it directly does
  # not depend on PATH; `env` is only a proxy for "this sandbox can exec a script at all", and the
  # check is skipped where it cannot.  Testing `-x /usr/bin/env` rather than `command -v env` made
  # the check silently vanish under Nix, where there is no /usr/bin -- so the one environment that
  # needed it most was the one that skipped it.
  if command -v env >/dev/null 2>&1; then
    PATH="$(dirname "$LIN_BIN"):$PATH" "$TMP_DIR/$name.line" > "$TMP_DIR/out2"
    out2=$(cat "$TMP_DIR/out2")
    [ "$out2" = "$want" ] || { echo "FAIL: $name direct output '$out2' (want '$want')"; lok=0; }
  fi
  if [ "$lok" = 1 ]; then pass=$((pass+1)); echo "PASS $src (build+run, 4 checks)"; else fail=$((fail+1)); line_fail=$((line_fail+1)); fi
done
line_total=$((line_total + 2 * 4))
total_checks=$((total_checks + line_total))

t1=$(date +%s%3N 2>/dev/null || date +%s)

# ----------------------------------------------------------------------------
# Tier 6: Budget, Command Line Interface & Flag Invariants
# ----------------------------------------------------------------------------
if bash test/test_cli_flags.sh "$LIN_BIN" >/dev/null 2>&1; then
  pass=$((pass+1)); total_checks=$((total_checks + 7)); echo "PASS test/test_cli_flags.sh (7 checks)"
else
  fail=$((fail+1)); echo "FAIL test/test_cli_flags.sh"; bash test/test_cli_flags.sh "$LIN_BIN"
fi

# The core is deliberately small enough to read in one sitting, and that budget is the only
# thing keeping the engine from accreting passes.  It has to be a test: the claim in the
# Makefile ("<= 3000 lines") had silently drifted past 3500, and a number in a comment
# cannot fail a build.
LOC=$(cat src/*.c src/*.h | wc -l)
if [ "$LOC" -le 3500 ]; then
  pass=$((pass+1)); total_checks=$((total_checks + 1)); echo "PASS src/ line budget ($LOC / 3500)"
else
  fail=$((fail+1)); echo "FAIL src/ line budget: $LOC lines, budget 3500 (move a pass into a .inc, or delete code)"
fi

t_end=$(date +%s%3N 2>/dev/null || date +%s)
total_dur=$((t_end - t_start))
echo "========================================================================"
if [ "$fail" -eq 0 ]; then
  echo "SUCCESS: All $pass test suites passed ($total_checks assertions in $total_dur ms)"
else
  echo "FAILURE: $fail failed, $pass passed ($total_checks total assertions)"
fi
echo "========================================================================"
exit $fail