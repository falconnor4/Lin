#!/usr/bin/env bash
# ============================================================================
# The driver ABI must FAIL CLOSED: what a plugin can do is decided by what it
# DECLARES, and a declaration the core cannot reach must be refused out loud --
# never quietly ignored.
#
#   1. REFUSAL -- a plugin that does not declare a `size` reaching its own hooks
#      is refused, the message names the field, and the core never consults it.
#      This was a live silent failure: std/drivers/gpu.c set no `.size`, so
#      every hook read back ABSENT (DRV_HAS is `size >= offsetof+sizeof`), the
#      driver registered, `(get_driver)` reported it as the ACTIVE strategy and
#      the base engine did all the work.
#   2. ADMISSION -- the SAME plugin with `.size` is consulted (its claim hook
#      runs) and the values are still the base engine's: a driver that declines
#      every redex changes nothing, which is what makes the count meaningful.
#   3. DIAGNOSIS -- `(set_driver "<absent>")` says the plugin is not available
#      instead of silently running the base engine.
#
# The probe is built and loaded from a COPY of the std, so nothing is written
# into the checkout.
# ============================================================================
set -u
BIN=${1:-./lin}
STD=${2:-std}
STD_DIR=$(cd "$STD" && pwd)
ROOT=$(cd "$(dirname "$0")/.." && pwd)
PASS=0
FAIL=0
fail() { echo "  FAIL: $*"; FAIL=$((FAIL+1)); }
ok() { PASS=$((PASS+1)); }

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
cp -r "$STD_DIR" "$TMP/std"

# A probe that DECLINES every redex (so an accepted probe cannot change a value) and counts the
# redexes the core offers it -- the only way to observe whether the core consults it at all.
cat > "$TMP/probe.c" <<'PROBE'
#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
static int claims;
static int probe_claim(const Net *n, Port p1, Port p2) { (void)n; (void)p1; (void)p2; claims++; return 0; }
static int probe_reduce(Net *n, Port *rx, int nred, long limit, int *changed) {
  (void)n; (void)rx; (void)nred; (void)limit; (void)changed; return 0;
}
LinDriver lin_probe_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
/*SIZEFIELD*/
  .name = "probe", .description = "ABI probe: counts offers, declines every one",
  .caps = LIN_CAP_FIXED, .priority = 30,
  .claim = probe_claim, .reduce = probe_reduce,
};
static void probe_report(void) { fprintf(stderr, "[probe] claims=%d\n", claims); }
static void __attribute__((constructor)) probe_load(void) {
  atexit(probe_report);
  lin_driver_add(&lin_probe_driver);
}
PROBE

# `$1` = the .size line to use ("" for the plugin that never set it).
build_probe() {
  awk -v s="$1" '{ if ($0 == "/*SIZEFIELD*/") { if (s != "") print s } else print }' \
    "$TMP/probe.c" > "$TMP/probe_built.c"
  cc -O2 -std=c99 -fopenmp -fPIC -shared -I "$ROOT/src" -o "$TMP/std/drivers/probe.so" \
     "$TMP/probe_built.c" -ldl -lm 2>"$TMP/cc.err"
}

if ! command -v cc >/dev/null 2>&1; then
  echo "driver_abi: SKIPPED (no cc to build the probe plugin)"
  exit 0
fi

printf '(load "std/drivers/driver.lin")\n(set_driver "probe")\n(mul 6 7)\n' > "$TMP/with_probe.lin"
printf '(load "std/drivers/driver.lin")\n(set_driver "cpu")\n(mul 6 7)\n'    > "$TMP/base.lin"
printf '(load "std/drivers/driver.lin")\n(set_driver "no_such_plugin")\n(mul 6 7)\n' > "$TMP/absent.lin"
run() { LIN_STD="$TMP/std/std.lin" LIN_STD_DIR="$TMP/std" timeout 60 "$BIN" "$1" >"$TMP/out" 2>"$TMP/err"; }
value() { grep '^=> ' "$TMP/out" | tail -1; }

run "$TMP/base.lin"
base=$(value)
[ -n "$base" ] || fail "the base run produced no value: the probe's expectations are meaningless"
echo "  base value: $base"

# ---- 1. refusal -----------------------------------------------------------
if build_probe ""; then
  run "$TMP/with_probe.lin"
  if grep -q "rejected" "$TMP/err"; then ok; else fail "a plugin without .size was NOT refused"; fi
  if grep -q "'probe'" "$TMP/err"; then ok; else fail "the refusal does not name the plugin"; fi
  if grep -q "\[probe\] claims=0$" "$TMP/err"; then ok; else
    fail "the core CONSULTED a plugin whose hooks it cannot reach ($(grep '\[probe\]' "$TMP/err" || echo 'no report'))"
  fi
  if [ "$(value)" = "$base" ]; then ok; else fail "the refused plugin changed the value ($(value))"; fi
  echo "  refused: $(grep rejected "$TMP/err" | head -1)"
else
  fail "the probe plugin did not compile: $(tail -3 "$TMP/cc.err" | tr '\n' ' ')"
fi

# ---- 2. admission ---------------------------------------------------------
if build_probe "  .size = (uint32_t)sizeof(LinDriver),"; then
  run "$TMP/with_probe.lin"
  if grep -q "rejected" "$TMP/err"; then fail "a plugin WITH .size was refused: $(grep rejected "$TMP/err")"; else ok; fi
  claims=$(sed -n 's/^\[probe\] claims=\([0-9]*\)$/\1/p' "$TMP/err" | tail -1)
  if [ -n "$claims" ] && [ "$claims" -gt 0 ]; then ok; else fail "an admitted plugin was never consulted (claims=${claims:-none})"; fi
  echo "  redexes offered to the admitted probe: ${claims:-none}"
  if [ "$(value)" = "$base" ]; then ok; else fail "a plugin that declines every redex changed the value ($(value))"; fi
else
  fail "the probe plugin did not compile with .size: $(tail -3 "$TMP/cc.err" | tr '\n' ' ')"
fi

# ---- 3. diagnosis ---------------------------------------------------------
run "$TMP/absent.lin"
if grep -q "no_such_plugin" "$TMP/err"; then ok; else
  fail "(set_driver) for an absent plugin said nothing about it"
fi
if [ "$(value)" = "$base" ]; then ok; else fail "an absent driver changed the value ($(value))"; fi
echo "  absent plugin: $(grep 'not available' "$TMP/err" | head -1)"

if [ "$FAIL" -eq 0 ]; then
  echo "driver_abi: OK ($PASS checks: refusal named and never consulted, admission consulted, absent plugin diagnosed)"
  exit 0
fi
echo "driver_abi: FAIL ($FAIL of $((PASS + FAIL)) checks: refusal named and never consulted, admission consulted, absent plugin diagnosed)"
exit 1
