#!/usr/bin/env bash
# A datatype's constructor type must describe ALL of its fields, and the count is taken from the
# PROGRAM, not from a number in this test: the property is "as many arrows as the constructor has
# fields", which stays true whatever the field list is.  A fixed scope in the compiler silently
# dropped the fields past it, and a dropped field is a different type -- measured: a 20-field
# constructor came out `t1 -> ... -> t16 -> Big` before the scope was sized from the fields.
set -u
LIN=${1:-./lin}
W=$(mktemp -d); trap 'rm -rf "$W"' EXIT

NF=24                                         # deliberately past any fixed scope the compiler has had
fields=$(python3 -c "print(' '.join('f%d' % i for i in range($NF)))")
printf '(datatype Wide (mk %s))\n:type mk\n' "$fields" > "$W/wide.lin"

ty=$("$LIN" < "$W/wide.lin" 2>&1 | grep -- '->' | head -1)
arrows=$(printf '%s' "$ty" | grep -o -- '->' | wc -l | tr -d ' ')

if [ "$arrows" -ne "$NF" ]; then
  echo "datatype_arity: FAIL ($arrows of $NF fields typed)"
  echo "  $ty"
  exit 1
fi
echo "datatype_arity: OK ($NF fields, $arrows arrows, both counted from the program)"
