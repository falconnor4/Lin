#!/bin/sh
# test runner: compares program output against "; expect " annotations
cd "$(dirname "$0")/.." || exit 1

pass=0
fail=0

for f in test/*.lin; do
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
  else
    fail=$((fail + 1))
    echo "FAIL $f"
    echo "--- want ---"
    printf '%s\n' "$want"
    echo "--- got ---"
    printf '%s\n' "$got"
  fi
done

echo "$pass passed, $fail failed"
[ "$fail" = 0 ]
