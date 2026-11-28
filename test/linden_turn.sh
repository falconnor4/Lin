#!/usr/bin/env bash
# ================================================================================
# A game's frame, compiled whole (std/drivers/fn.c, A LOOP'S STEP): leaves.lin's turn -- draw the world, wait for
# the frame's keys, step the world -- is a turn that waits, compiled once as its parts and run each frame around
# the frame's own call.  The picture after many frames must be IDENTICAL, bit for bit, to the one the net draws
# with that compile switched off (LIN_STEP_WAIT_OFF), and the compiled run must really be the compiled turn.
# usage: test/linden_turn.sh [LIN_BIN] [LIN_STD_DIR]
# ================================================================================
. "$(dirname "$0")/common.sh"
lin_test_env "${1:-}" "${2:-}" || exit 1
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
FRAMES=90
if [ ! -f examples/linden/linden.so ]; then
  make -s examples/linden/linden.so >/dev/null 2>&1 || { echo "linden_turn: SKIP (examples/linden/linden.so cannot be built)"; exit 0; }
fi
render() {   # tag, env... -> $TMP/<tag>.ppm, the debug log in $TMP/<tag>.log
  local tag=$1; shift
  env "$@" LINDEN_HEADLESS=1 LINDEN_FRAMES=$FRAMES LINDEN_PPM="$TMP/$tag.ppm" LIN_NATIVE_CACHE="$TMP/cache-$tag" \
    LIN_FN_DEBUG=1 timeout 600 "$LIN_BIN" examples/linden/leaves.lin >"$TMP/$tag.log" 2>&1
}
fail=0
render turn X=1
render net LIN_STEP_WAIT_OFF=1
for t in turn net; do
  [ -s "$TMP/$t.ppm" ] || { echo "FAIL: the $t run drew no picture"; tail -5 "$TMP/$t.log"; fail=1; }
done
[ $fail = 0 ] && { cmp -s "$TMP/turn.ppm" "$TMP/net.ppm" || { echo "FAIL: the compiled turn's picture differs from the net's"; fail=1; }; }
grep -q "step: compiled as its parts" "$TMP/turn.log" || { echo "FAIL: the frame's turn was not compiled"; grep "step:" "$TMP/turn.log"; fail=1; }
grep -q "step: compiled as its parts" "$TMP/net.log" && { echo "FAIL: LIN_STEP_WAIT_OFF still compiled the turn"; fail=1; }
[ $fail = 0 ] || exit 1
echo "linden_turn: OK ($FRAMES frames of leaves.lin: the compiled turn draws what the net draws)"
