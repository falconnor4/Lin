#!/bin/sh
# test runner: compares program output against "; expect " annotations
cd "$(dirname "$0")/.." || exit 1

pass=0
fail=0

TESTS="$@"
if [ -z "$TESTS" ]; then
  TESTS="test/basics.lin test/booleans.lin test/combinators.lin test/pairs.lin test/scott.lin test/scott_arith.lin test/adts.lin test/multi_file.lin test/sat.lin test/sat_verify.lin test/tseitin.lin test/ffi.lin test/ffi_advanced.lin test/ffi_systems.lin"
fi

for f in $TESTS; do
  got=$(./lin "$f" 2>&1 | grep -v '^warning')
  want=$(grep '^; expect ' "$f" | sed 's/^; expect //')
  gn=$(printf '%s\n' "$got" | grep -c .)
  wn=$(printf '%s\n' "$want" | grep -c .)
  ok=1
  [ "$gn" = "$wn" ] || ok=0
  if [ "$ok" = 1 ] && [ "$wn" -gt 0 ]; then
    i=1
    while [ "$i" -le "$wn" ]; do
      w=$(printf '%s\n' "$want" | sed -n "${i}p")
      g=$(printf '%s\n' "$got" | sed -n "${i}p")
      case "$w" in
        *...)
          pfx="${w%...}"
          case "$g" in "$pfx"*) ;; *) ok=0 ;; esac
          ;;
        *)
          [ "$w" = "$g" ] || ok=0
          ;;
      esac
      i=$((i + 1))
    done
  fi
  if [ "$ok" = 1 ]; then
    pass=$((pass + 1))
    printf "PASS %s\n" "$f"
  else
    fail=$((fail + 1))
    echo "FAIL $f"
    echo "--- want ---"
    printf '%s\n' "$want"
    echo "--- got ---"
    printf '%s\n' "$got"
  fi
done

echo ""
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
