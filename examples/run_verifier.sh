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
# Scan every *.lin under examples/ recursively (examples live in per-topic
# subdirectories such as examples/interactive/, examples/pure-functional/, ...).
while IFS= read -r -d '' f; do
  case "$(basename "$f")" in README*|index*|run_verifier*) continue;; esac
  if ! grep -q '^; expect' "$f"; then
    int=$((int + 1)); printf "INT   %-40s\n" "$(basename "$f")"
    continue
  fi
  got=$("$LIN_BIN" "$f" 2>&1 | grep -v '^warning' || true)
  want=$(grep '^; expect ' "$f" | sed 's/^; expect //')
  gn=$(printf '%s\n' "$got" | grep -c . || true); wn=$(printf '%s\n' "$want" | grep -c . || true)
  ok=1; [ "$gn" = "$wn" ] || ok=0
  if [ "$ok" = 1 ] && [ "$wn" -gt 0 ]; then
    i=1
    while [ "$i" -le "$wn" ]; do
      w=$(printf '%s\n' "$want" | sed -n "${i}p")
      g=$(printf '%s\n' "$got" | sed -n "${i}p")
      case "$w" in
        *...) pfx="${w%...}"; case "$g" in "$pfx"*) ;; *) ok=0 ;; esac ;;
        *) [ "$w" = "$g" ] || ok=0 ;;
      esac
      i=$((i + 1))
    done
  fi
  if [ "$ok" = 1 ]; then pass=$((pass + 1)); printf "PASS  %-40s (%2d checks)\n" "$(basename "$f")" "$wn"
  else fail=$((fail + 1)); printf "FAIL  %-40s (got %d want %d)\n" "$(basename "$f")" "$gn" "$wn"
    echo "--- want ---"; printf '%s\n' "$want"
    echo "--- got  ---"; printf '%s\n' "$got"
  fi
done < <(find "$ROOT"/examples -name '*.lin' -type f -print0 | sort -z)
echo "========================================================================"
printf "examples: %d pass, %d fail, %d interactive\n" "$pass" "$fail" "$int"
[ "$fail" -eq 0 ]