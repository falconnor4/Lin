#!/usr/bin/env bash
# ================================================================================
# Lin's integers are 64-bit two's complement, wrapping -- in the NET and in every driver.
# --------------------------------------------------------------------------------
# The net's own arithmetic (std/num.lin: pure Lin over bit chains) and the fold drivers'
# (std/runtime/i64.h) must be ONE function.  Each pair below runs the pure body directly
# (num._p<op>, which nothing pre-empts) beside the folded op, and both must equal the
# int64_t answer, including overflow and the division edge cases.
# usage: test/int64.sh [LIN_BIN] [LIN_STD_DIR]
# ================================================================================
. "$(dirname "$0")/common.sh"
lin_test_env "${1:-}" "${2:-}" || exit 1
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
MAX=9223372036854775807; MIN=-9223372036854775808
# op a b expected
cases="add 5 3 8
add $MAX 1 $MIN
sub 3 8 -5
sub $MIN 1 $MAX
mul -3 4 -12
mul $MAX 2 -2
div -7 2 -3
div 7 -2 -3
div 13 0 0
div $MIN -1 $MIN
mod -7 2 -1
mod 7 -2 1
mod 13 0 0
lt -1 0 true
lt 0 -1 false
lt $MIN $MAX true
eq -5 -5 true
pow 2 10 1024
pow -2 3 -8"
: > "$TMP/p.lin"; : > "$TMP/want"
while read -r op a b want; do
  printf '(num._p%s %s %s)\n(%s %s %s)\n' "$op" "$a" "$b" "$op" "$a" "$b" >> "$TMP/p.lin"
  printf '=> %s\n=> %s\n' "$want" "$want" >> "$TMP/want"
done <<< "$cases"
got=$(timeout 600 "$LIN_BIN" "$TMP/p.lin" 2>/dev/null)
if [ "$got" = "$(cat "$TMP/want")" ]; then
  echo "int64: OK ($(wc -l < "$TMP/want") checks: the net's arithmetic and the fold agree with int64_t)"; exit 0
fi
echo "int64: FAILED"; diff <(cat "$TMP/want") <(printf '%s\n' "$got") | head -20; exit 1
