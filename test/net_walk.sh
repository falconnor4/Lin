#!/usr/bin/env bash
# The net's demand walk stays proportional to the work.
#   A force walks from its own root (net.c, net_mark_demand).  That root used to be an index into the root
#   array, which a freed node closes up, so a stale index fell back to walking every root: each wave of a
#   force cost the depth of the forces nested around it.  A lazy left fold nests forces as deep as its list,
#   so its walk grew with the square of the list (a 1000-cell fold walked ~800 steps per interaction, a
#   2000-cell one twice that).  This holds the walk per interaction fired (LIN_WAVE_STATS) under a bound
#   the old code exceeded forty-fold.
set -u
LIN_BIN="${1:-./lin}"
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
cat > "$TMP/fold.lin" <<'LIN'
(define hb (\k (if (eq k 0) snil (scons k (hb (sub k 1))))))
(sfoldl (\a (\x (add a x))) 0 (hb 1000))
LIN
out=$(LIN_FN_OFF=1 LIN_WAVE_STATS=1 "$LIN_BIN" -t 1 "$TMP/fold.lin" 2>&1)
case "$out" in *"=> 500500"*) ;; *) echo "net_walk: wrong answer: $out"; exit 1 ;; esac
fired=$(printf '%s\n' "$out" | grep -o 'fired=[0-9]*' | cut -d= -f2)
walked=$(printf '%s\n' "$out" | grep -o 'walked=[0-9]*' | cut -d= -f2)
[ -n "$fired" ] && [ -n "$walked" ] && [ "$fired" -gt 0 ] || { echo "net_walk: no wave stats: $out"; exit 1; }
per=$((walked / fired))
if [ "$per" -ge 20 ]; then
  echo "net_walk: a 1000-cell lazy fold walked $per steps per interaction ($walked for $fired): the demand walk is not starting from its force's root"
  exit 1
fi
echo "net_walk: OK (a 1000-cell lazy fold on the net walks $per steps per interaction fired, bound 20)"
