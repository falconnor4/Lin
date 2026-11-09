#!/usr/bin/env bash
# ================================================================================
# The language runs without its standard library.
# --------------------------------------------------------------------------------
# Everything the CORE language offers compiles to plain net structure: lambdas,
# application, numerals (64-bit, signed), strings (cell chains), `if`, `lazy`/`force`,
# `let` (recursion included) and `match`.  With an EMPTY prelude, each of these must
# still reduce and print.  (Arithmetic and the rest are library functions -- std/.)
# usage: test/no_std.sh [LIN_BIN] [LIN_STD_DIR]
# ================================================================================
. "$(dirname "$0")/common.sh"
lin_test_env "${1:-}" "${2:-}" || exit 1
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
: > "$TMP/empty.lin"
pass=0; fail=0
check() {
  got=$(LIN_STD="$TMP/empty.lin" timeout 60 "$LIN_BIN" -e "$1" 2>&1)
  if [ "$got" = "=> $2" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $1: got '$got' want '=> $2'"; fi
}
check '((\x x) (\y y))' '(\a a)'
check '42' '42'
check '-9223372036854775808' '-9223372036854775808'
check '(if (\t (\f f)) 1 2)' '2'
check '"no library needed"' '"no library needed"'
check '(force (lazy 7))' '7'
check '(let ((k (\a (\b a)))) (k 3 4))' '3'
check '(let ((const (\x (\y x)))) (let ((twice (\f (\x (f (f x)))))) (twice (const 9) 1)))' '9'
check '(datatype Opt (none) (some v)) (match (some 5) (none 0) ((some v) v))' '5'
check '(datatype Opt (none) (some v)) (match none (none 0) ((some v) v))' '0'
if [ "$fail" -eq 0 ]; then echo "no_std: OK ($pass forms run with an empty prelude)"; else echo "no_std: $fail of $((pass+fail)) failed"; fi
exit $fail
