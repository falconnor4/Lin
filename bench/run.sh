#!/usr/bin/env bash
# ================================================================================
# Lin against C, honestly.
# --------------------------------------------------------------------------------
# Every benchmark is one program written the natural way in each language: no hand
# parallelism in the C, no algorithmic help in the Lin.  The C is built with
# `cc -O3 -march=native`; Lin runs with its std (all of its drivers).  Times are wall
# clock, best of three, and include Lin's whole process: startup, prelude, and the
# function compiler's cached build.  The first Lin run of each benchmark fills that
# cache and is not timed.  Outputs must be identical or the row says MISMATCH.
#
# usage: bench/run.sh [LIN_BIN]       (or: nix run .#bench)
# ================================================================================
set -u
DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$DIR/.." && pwd)"
LIN="${1:-${LIN_BIN:-$ROOT/lin}}"
CC="${CC:-cc}"
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
best() {   # best wall-clock ms of three runs of "$@"
  local b=-1
  for _ in 1 2 3; do
    local s=$(date +%s%N); "$@" >/dev/null 2>&1; local e=$(date +%s%N)
    local ms=$(( (e - s) / 1000000 )); if [ $b -lt 0 ] || [ $ms -lt $b ]; then b=$ms; fi
  done
  echo $b
}
printf '| %-11s | %10s | %10s | %10s | %8s | %s\n' benchmark "C -O3" "Lin" "Lin -t 1" "C / Lin" result
printf '|%s|%s|%s|%s|%s|%s\n' ------------- ------------ ------------ ------------ ---------- --------
for f in "$DIR"/*.lin; do
  name=$(basename "$f" .lin)
  "$CC" -O3 -march=native -ffp-contract=off -o "$TMP/$name" "$DIR/$name.c" -lm 2>/dev/null || { echo "| $name | (C build failed)"; continue; }
  want=$("$TMP/$name")
  got=$("$LIN" "$f" 2>/dev/null | sed 's/^=> //')         # also warms the compile cache
  if [ "$got" != "$want" ]; then printf '| %-11s | MISMATCH: C %s, Lin %s\n' "$name" "$want" "$got"; continue; fi
  c=$(best "$TMP/$name"); l=$(best "$LIN" "$f"); l1=$(best "$LIN" -t 1 "$f")
  ratio=$(awk -v c="$c" -v l="$l" 'BEGIN { printf "%.2fx", (l > 0 ? c / l : 0) }')
  printf '| %-11s | %7d ms | %7d ms | %7d ms | %8s | %s\n' "$name" "$c" "$l" "$l1" "$ratio" "$want"
done
