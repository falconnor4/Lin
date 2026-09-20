#!/usr/bin/env bash
# ================================================================================
# Examples verifier.
# --------------------------------------------------------------------------------
# Runs every examples/*.lin that carries `; expect` annotations and diffs the
# engine output line-for-line against them (same matcher test/run_tests.sh uses,
# including `...` prefix matching).  Interactive examples (those with `;interactive`
# or no `; expect`) are reported but not value-checked.
#
# Usage: examples/run_verifier.sh [LIN_BIN] [LIN_STD_DIR]
# ================================================================================
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [ "$#" -gt 0 ]; then LIN_BIN="${LIN_BIN:-$1}"; else LIN_BIN="${LIN_BIN:-}"; fi
LIN_BIN="${LIN_BIN:-$ROOT/lin}"
if [ "$#" -gt 1 ]; then STD_DIR="${STD_DIR:-$2}"; else STD_DIR="${STD_DIR:-}"; fi
STD_DIR="${STD_DIR:-$ROOT/std}"
export LIN_STD="${LIN_STD:-$STD_DIR/std.lin}"
export LIN_STD_DIR="$STD_DIR"

pass=0; fail=0; int=0
. "$ROOT/test/expect.sh"          # the shared `; expect` matcher (see test/expect.sh)
# Scan every *.lin under examples/ recursively (examples live in per-topic
# subdirectories such as examples/interactive/, examples/pure-functional/, ...).
while IFS= read -r -d '' f; do
  case "$(basename "$f")" in README*|index*|run_verifier*) continue;; esac
  if ! lin_has_expects "$f"; then
    int=$((int + 1)); printf "INT   %-40s\n" "$(basename "$f")"
    continue
  fi
  lin_expect_check "$LIN_BIN" "$f"
  if [ "$EXP_OK" = 1 ]; then pass=$((pass + 1)); printf "PASS  %-40s (%2d checks)\n" "$(basename "$f")" "$EXP_N"
  else fail=$((fail + 1)); printf "FAIL  %-40s (got %d want %d)\n" "$(basename "$f")" "$(printf '%s\n' "$EXP_GOT" | grep -c . || true)" "$EXP_N"
    echo "--- want ---"; printf '%s\n' "$EXP_WANT"
    echo "--- got  ---"; printf '%s\n' "$EXP_GOT"
  fi
done < <(find "$ROOT"/examples -name '*.lin' -type f -print0 | sort -z)
echo "========================================================================"
printf "examples: %d pass, %d fail, %d interactive\n" "$pass" "$fail" "$int"
[ "$fail" -eq 0 ]