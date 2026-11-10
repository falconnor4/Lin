#!/usr/bin/env bash
# ============================================================================
# A float is net structure, so an artifact carries it with nothing beside it.
#
# A float is the numeral of its 64-bit IEEE-754 pattern; its TYPE says float.  So a
# built artifact holds its floats in the net itself -- no value table, no section,
# no driver that has to be loaded to give them back:
#
#   1. an artifact prints its own floats;
#   2. it does so with NO prelude at all (nothing outside the net is needed);
#   3. two artifacts in one process each keep their own value (there is no shared
#      table to collide in).
# ============================================================================
set -u
BIN=${1:-./lin}
STD=${2:-std}
STD_DIR=$(cd "$STD" && pwd)
FAIL=0
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
export LIN_STD_DIR="$STD_DIR"

prog() {  # prog <file> <float>
  { printf '(load "std/std.lin")\n\n(define! main float\n  (let ((v %s))\n    v))\n\n(main)\n' "$2"; } > "$1"
}
prog "$TMP/a.lin" 2.5
prog "$TMP/b.lin" 144.0
for p in a b; do
  LIN_STD="$STD_DIR/std.lin" timeout 120 "$BIN" build "$TMP/$p.lin" -o "$TMP/$p.line" >/dev/null 2>&1 \
    || { echo "  FAIL: could not build $p.line"; FAIL=$((FAIL+1)); }
done
want_a='=> 2.5'; want_b='=> 144'
got_a=$(LIN_STD="$STD_DIR/std.lin" timeout 120 "$BIN" "$TMP/a.line" 2>/dev/null | tail -1)
got_b=$(LIN_STD="$STD_DIR/std.lin" timeout 120 "$BIN" "$TMP/b.line" 2>/dev/null | tail -1)
[ "$got_a" = "$want_a" ] || { echo "  FAIL: a.line printed '$got_a', wanted '$want_a'"; FAIL=$((FAIL+1)); }
[ "$got_b" = "$want_b" ] || { echo "  FAIL: b.line printed '$got_b', wanted '$want_b'"; FAIL=$((FAIL+1)); }

bare="$TMP/empty.lin"; printf '; no prelude\n' > "$bare"
got_bare=$(LIN_STD="$bare" timeout 120 "$BIN" "$TMP/b.line" 2>/dev/null | tail -1)
[ "$got_bare" = "$want_b" ] || { echo "  FAIL: without a prelude the artifact printed '$got_bare'"; FAIL=$((FAIL+1)); }

both=$(LIN_STD="$STD_DIR/std.lin" timeout 120 "$BIN" "$TMP/a.line" "$TMP/b.line" 2>/dev/null)
printf '%s\n' "$both" | grep -q "=> 2.5" || { echo "  FAIL: a.line lost its value when run beside b.line"; FAIL=$((FAIL+1)); }
printf '%s\n' "$both" | grep -q "=> 144" || { echo "  FAIL: b.line lost its value when run beside a.line"; FAIL=$((FAIL+1)); }

if [ "$FAIL" -eq 0 ]; then
  echo "floats_carry: OK (an artifact's floats are its own net: printed with no prelude, no table to share or collide)"
  exit 0
fi
echo "floats_carry: $FAIL check(s) failed"
exit 1
