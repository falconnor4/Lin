#!/usr/bin/env bash
# ============================================================================
# Value storage is a DRIVER's, so an artifact has to carry it and say who owns it.
#
# The float box table used to be core state: the container hardcoded a section
# for it and `net_load_line` restored it directly.  It is now a driver's table
# (std/drivers/values.c) carried as an OPAQUE section tagged with the driver's
# name, which buys three properties this test pins:
#
#   1. an artifact still prints its own floats;
#   2. the artifact is SELF-DESCRIBING -- run it with no prelude at all and the
#      section's name is enough for the core to load whoever wrote it, so the
#      core can stay ignorant of every value domain;
#   3. entries come back at their ORIGINAL indices, because a box's index is
#      baked into its spine.  Two artifacts built in separate processes collide
#      (both number from zero) and that is reported rather than silently
#      resolved -- the old design clobbered and printed the wrong number.
# ============================================================================
set -u
BIN=${1:-./lin}
STD=${2:-std}
STD_DIR=$(cd "$STD" && pwd)
FAIL=0
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
export LIN_STD_DIR="$STD_DIR"

# The shape a container build accepts: a `main` def whose value is the float (Tier 5's pattern).
prog() {  # prog <file> <float>
  { printf '(load "std/std.lin")\n\n(define! main a\n  (let ((v %s))\n    v))\n\n(main)\n' "$2"; } > "$1"
}

prog "$TMP/a.lin" 2.5
prog "$TMP/b.lin" 144.0
for p in a b; do
  LIN_STD="$STD_DIR/std.lin" timeout 120 "$BIN" build "$TMP/$p.lin" -o "$TMP/$p.line" >/dev/null 2>&1 \
    || { echo "  FAIL: could not build $p.line"; FAIL=$((FAIL+1)); }
done

want_a='=> 2.5'
want_b='=> 144'
got_a=$(LIN_STD="$STD_DIR/std.lin" timeout 120 "$BIN" "$TMP/a.line" 2>/dev/null | tail -1)
got_b=$(LIN_STD="$STD_DIR/std.lin" timeout 120 "$BIN" "$TMP/b.line" 2>/dev/null | tail -1)
[ "$got_a" = "$want_a" ] || { echo "  FAIL: a.line printed '$got_a', wanted '$want_a'"; FAIL=$((FAIL+1)); }
[ "$got_b" = "$want_b" ] || { echo "  FAIL: b.line printed '$got_b', wanted '$want_b'"; FAIL=$((FAIL+1)); }

# (2) self-describing: no prelude loaded, so only the section's driver name can supply the table
bare="$TMP/empty.lin"; printf '; no prelude\n' > "$bare"
got_bare=$(LIN_STD="$bare" timeout 120 "$BIN" "$TMP/b.line" 2>/dev/null | tail -1)
[ "$got_bare" = "$want_b" ] || { echo "  FAIL: without a prelude the artifact printed '$got_bare' (the section did not load its own driver)"; FAIL=$((FAIL+1)); }

# (3) both in one process: each keeps its own value, and a genuine table collision is reported
both=$(LIN_STD="$STD_DIR/std.lin" timeout 120 "$BIN" "$TMP/a.line" "$TMP/b.line" 2>"$TMP/err")
printf '%s\n' "$both" | grep -q "=> 2.5"   || { echo "  FAIL: a.line lost its value when run beside b.line"; FAIL=$((FAIL+1)); }
printf '%s\n' "$both" | grep -q "=> 144"   || { echo "  FAIL: b.line lost its value when run beside a.line"; FAIL=$((FAIL+1)); }
grep -q "value table conflict" "$TMP/err" || { echo "  FAIL: two conflicting tables were not reported"; FAIL=$((FAIL+1)); }

if [ "$FAIL" -eq 0 ]; then
  echo "values_carry: OK (artifact carries its own table, loads its own driver from the section name, indices restored, collisions reported)"
  exit 0
fi
echo "values_carry: $FAIL check(s) failed"
exit 1
