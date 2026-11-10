#!/usr/bin/env bash
# ================================================================================
# Erasure reclaims what a program discards -- there is no collector.
# --------------------------------------------------------------------------------
# Memory is the calculus's own business: a rule frees the pair it consumes, and an
# ERASER (the calculus's ERA node, wired wherever a value goes unused) consumes what it
# reaches.  This suite pins both halves on programs whose discarded part is known:
#   * the answer is right (erasure never destroys a value something still needs), and
#   * the structure the program DISCARDS is gone afterwards: LIN_LEAKCHECK (a diagnostic
#     walk, never run otherwise) counts live nodes the result no longer reaches, and the
#     live count must sit far below the peak the discarded subterm needed.
# usage: test/erasure.sh [LIN_BIN] [LIN_STD_DIR]
# ================================================================================
. "$(dirname "$0")/common.sh"
lin_test_env "${1:-}" "${2:-}" || exit 1
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
pass=0; fail=0
# expr | expected value | max live nodes unreachable from the result
check() {
  printf '%s\n' "$1" > "$TMP/e.lin"
  out=$(LIN_LEAKCHECK=1 timeout 60 "$LIN_BIN" -b "$TMP/e.lin" 2>&1)
  val=$(printf '%s\n' "$out" | grep -o '^=> [^[]*' | head -1 | sed 's/ *$//')
  unr=$(printf '%s\n' "$out" | sed -n 's/.*reachable, \([0-9]*\) live unreachable.*/\1/p')
  if [ "$val" = "=> $2" ] && [ -n "$unr" ] && [ "$unr" -le "$3" ]; then pass=$((pass+1))
  else fail=$((fail+1)); echo "FAIL $1: got '$val' (want '=> $2'), $unr unreachable (max $3)"; fi
}
check '(let ((g (cons 1 (cons 2 (cons 3 nil))))) 7)' 7 2
check '(fst (pair 1 (list3 4 5 6)))' 1 0
check '(snd (pair (list3 4 5 6) 9))' 9 0
check '(head (tail (list3 1 2 3)))' 2 0
check '((\x 5) (list5 1 2 3 4 5))' 5 0
check '(if true 1 (head (list3 7 8 9)))' 1 2
# a discarded ARITHMETIC thunk: the fold's leftovers are erased too, so live stays far below peak
printf '%s\n' '((\x 5) (mul 300 (add 7 9)))' > "$TMP/e.lin"
line=$(LIN_NO_SHRINK=1 "$LIN_BIN" -b "$TMP/e.lin" 2>&1 | grep -o '[0-9]* nodes ([0-9]* live)')   # the eraser itself (shrinking drops it before)
peak=${line%% *}; live=$(printf '%s' "$line" | sed 's/.*(\([0-9]*\) live)/\1/')
if [ -n "$live" ] && [ "$live" -lt $((peak / 4)) ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL discarded arithmetic: $live live of $peak peak"; fi
# ...and the compiler's shrinking reductions remove an argument nobody uses before any of it is built
sline=$("$LIN_BIN" -b "$TMP/e.lin" 2>&1 | grep -o '[0-9]* nodes ([0-9]* live)'); speak=${sline%% *}
if [ -n "$speak" ] && [ "$speak" -lt $((peak / 4)) ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL shrinking left the dead argument: $speak nodes against $peak"; fi
if [ "$fail" -eq 0 ]; then echo "erasure: OK ($pass checks: discarded structure reclaimed, values intact)"; else echo "erasure: $fail of $((pass+fail)) failed"; fi
exit $fail
