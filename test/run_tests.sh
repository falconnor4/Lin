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
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

LIN_BIN="${LIN_BIN:-$1}"
LIN_BIN="${LIN_BIN:-./lin}"
STD_DIR="${STD_DIR:-$2}"
STD_DIR="${STD_DIR:-$ROOT/std}"
export LIN_STD="${LIN_STD:-$STD_DIR/std.lin}"
export LIN_STD_DIR="$STD_DIR"

if [ ! -x "$LIN_BIN" ]; then
  echo "Error: Lin binary '$LIN_BIN' not executable (run 'make lin' first)" >&2
  exit 1
fi

pass=0; fail=0; total_checks=0
t_start=$(date +%s%3N 2>/dev/null || date +%s)

run_test() {
  f="$1"
  t0=$(date +%s%3N 2>/dev/null || date +%s)
  got=$("$LIN_BIN" "$f" 2>&1 | grep -v '^warning' || true)
  want=$(grep '^; expect ' "$f" | sed 's/^; expect //')
  gn=$(printf '%s\n' "$got"  | grep -c . || true)
  wn=$(printf '%s\n' "$want" | grep -c . || true)
  ok=1; [ "$gn" = "$wn" ] || ok=0
  if [ "$ok" = 1 ] && [ "$wn" -gt 0 ]; then
    i=1
    while [ "$i" -le "$wn" ]; do
      w=$(printf '%s\n' "$want" | sed -n "${i}p")
      g=$(printf '%s\n' "$got"  | sed -n "${i}p")
      case "$w" in
        *...) pfx="${w%...}"; case "$g" in "$pfx"*) ;; *) ok=0 ;; esac ;;
        *)    [ "$w" = "$g" ] || ok=0 ;;
      esac
      i=$((i + 1))
    done
  fi
  t1=$(date +%s%3N 2>/dev/null || date +%s)
  dur=$((t1 - t0)); total_checks=$((total_checks + wn))
  if [ "$ok" = 1 ]; then pass=$((pass+1)); printf "PASS %-32s (%2d checks, %3dms)\n" "$f" "$wn" "$dur"
  else fail=$((fail+1)); printf "FAIL %-32s (got %d want %d)\n" "$f" "$gn" "$wn"
    echo "--- want ---"; printf '%s\n' "$want"
    echo "--- got  ---"; printf '%s\n' "$got"
  fi
}

printf "Running Lin Confluence & Stability Test Suite against %s\n" "$LIN_BIN"

printf "[Tier 1: Core Interaction Calculus & Primitives]\n"
for f in test/basics.lin test/booleans.lin test/combinators.lin test/pairs.lin test/scott.lin test/scott_arith.lin test/math.lin test/strings.lin test/string.lin test/adts.lin test/multi_file.lin test/modules.lin test/numbers.lin test/higher_order.lin test/let.lin test/test_escapes_utf8.lin test/types.lin; do
  run_test "$f"
done

printf "[Tier 2: Foreign Function Interface & System Drivers]\n"
for f in test/ffi.lin test/ffi_advanced.lin test/ffi_systems.lin test/driver_gpu.lin; do
  run_test "$f"
done

printf "[Tier 3: Constraint Satisfaction & Term Rewriting]\n"
for f in test/sat.lin test/sat_verify.lin test/tseitin.lin test/tsp.lin test/egraph.lin; do
  run_test "$f"
done

printf "[Tier 4: Non-Trivial Workloads & Confluence Invariants]\n"
for f in test/graph.lin test/map.lin test/set.lin test/queue.lin test/stream.lin test/stress_wavefront.lin test/nqueens.lin test/sudoku.lin test/trees.lin test/lists.lin test/algorithms.lin test/recursion.lin test/maybe_either.lin; do
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
line_total=0; line_fail=0
for spec in "test/line_binary.lin:LINE_BINARY_OK: 43" "test/line_ffi.lin:FFI_LINE_OK: 144"; do
  src="${spec%%:*}"; want="${spec#*:}"; name="$(basename "$src" .lin)"
  line=$((line_total + 1))
  "$LIN_BIN" build "$src" -o "$TMP_DIR/$name.line"
  lok=1
  [ -x "$TMP_DIR/$name.line" ] || { echo "FAIL: $name.line not executable"; lok=0; }
  head -n 1 "$TMP_DIR/$name.line" | grep -q '^#!/usr/bin/env lin' || { echo "FAIL: $name.line missing lin shebang"; lok=0; }
  out1=$("$LIN_BIN" "$TMP_DIR/$name.line")
  [ "$out1" = "$want" ] || { echo "FAIL: $name engine output '$out1' (want '$want')"; lok=0; }
  if [ -x /usr/bin/env ]; then
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
# Tier 6: Command Line Interface & Flag Invariants
# ----------------------------------------------------------------------------
if bash test/test_cli_flags.sh "$LIN_BIN" >/dev/null 2>&1; then
  pass=$((pass+1)); total_checks=$((total_checks + 7)); echo "PASS test/test_cli_flags.sh (7 checks)"
else
  fail=$((fail+1)); echo "FAIL test/test_cli_flags.sh"; bash test/test_cli_flags.sh "$LIN_BIN"
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