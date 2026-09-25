#!/usr/bin/env bash
# ============================================================================
# The C-emitting native driver (std/drivers/native.c) must be the interpreted
# path, only sooner.
#
#   1. DIFFERENTIAL -- with the driver loaded, every deterministic suite is
#      byte-identical to the run without it.  The net stays the source of
#      truth; compiling a cone only decides WHEN a value is computed.  A suite
#      the BASELINE is not deterministic on (it prints an address) cannot be a
#      differential input at all, so it is detected and skipped rather than
#      special-cased by name.
#   2. ATTESTATION -- a fresh cache must actually receive compiled objects.
#      Without this the differential would pass vacuously against a driver that
#      never fires, which is exactly how a broken driver hides.
#   3. SEMANTICS -- the whitelist is the shared table's own expressions, so the
#      cases a name-only emitter gets wrong are pinned by hand: `lin_sub`
#      SATURATES at zero (`sub 1 2` is 0, not -1), `div`/`mod` guard their
#      divisor, `pow` is the table's own loop, and the saturating form is
#      order-sensitive (`sub 5 3` is 2).
#   4. NO COMPILER -- when cc cannot be run the driver must not fail, strand a
#      redex or change an answer: it takes the interpreted fallback.
# ============================================================================
set -u
BIN=${1:-./lin}
STD=${2:-std}
STD_DIR=$(cd "$STD" && pwd)
PASS=0
FAIL=0
fail() { echo "  FAIL: $*"; FAIL=$((FAIL+1)); }
ok() { PASS=$((PASS+1)); }

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
CACHE="$TMP/cache"
mkdir -p "$CACHE"

# A prelude that loads the real one and then activates the driver: this is how a
# program enables it (`(set_driver "native")`), applied to whole suites.
BASE_STD="$STD_DIR/std.lin"
NATIVE_STD="$TMP/std_native.lin"
printf '(load "%s")\n(set_driver "native")\n' "$BASE_STD" > "$NATIVE_STD"

run_base() { LIN_STD="$BASE_STD" LIN_STD_DIR="$STD_DIR" timeout 120 "$BIN" "$1" 2>/dev/null; }
run_native() { LIN_STD="$NATIVE_STD" LIN_STD_DIR="$STD_DIR" LIN_NATIVE_CACHE="$CACHE" timeout 120 "$BIN" "$1" 2>/dev/null; }

# ---- 1. differential ------------------------------------------------------
suites=0
skipped=0
for f in test/*.lin; do
  grep -q '^; expect ' "$f" || continue
  a=$(run_base "$f"); b=$(run_base "$f")
  if [ "$a" != "$b" ]; then skipped=$((skipped+1)); continue; fi      # baseline itself is not deterministic
  suites=$((suites+1))
  n=$(run_native "$f")
  if [ "$a" = "$n" ]; then ok; else fail "native differs from the interpreted path on $f"; fi
done
echo "  suites compared: $suites (skipped as nondeterministic: $skipped)"

# ---- 2. attestation -------------------------------------------------------
compiles=0
if command -v cc >/dev/null 2>&1 && echo 'int lin_probe(void){return 0;}' | cc -x c - -shared -fPIC -o "$TMP/probe.so" 2>/dev/null; then
  compiles=$(ls "$CACHE"/*.so 2>/dev/null | wc -l)
  if [ "$compiles" -ge 3 ]; then ok; else fail "only $compiles cone(s) compiled: the driver is not firing"; fi
  echo "  cones compiled during the differential: $compiles"
else
  echo "  no usable cc: cone compilation not exercised here (the fallback is still checked below)"
fi

# ---- 3. semantics, pinned by hand -----------------------------------------
cat > "$TMP/sem.lin" <<'LIN'
(sub 1 2)
(div 5 0)
(mod 7 0)
(pow 2 10)
(sub 5 3)
(mul (add 1 2) (sub 5 3))
(add (mul 6 7) (div 100 4))
LIN
cat > "$TMP/sem_expect" <<'LIN'
=> 0
=> 0
=> 0
=> 1024
=> 2
=> 6
=> 67
LIN
got=$(LIN_STD="$NATIVE_STD" LIN_STD_DIR="$STD_DIR" LIN_NATIVE_CACHE="$CACHE" timeout 60 "$BIN" "$TMP/sem.lin" 2>/dev/null)
if [ "$got" = "$(cat "$TMP/sem_expect")" ]; then ok; else fail "compiled semantics differ from the table"; printf '%s\n' "$got" | sed 's/^/    got: /'; fi
base_got=$(LIN_STD="$BASE_STD" LIN_STD_DIR="$STD_DIR" timeout 60 "$BIN" "$TMP/sem.lin" 2>/dev/null)
if [ "$got" = "$base_got" ]; then ok; else fail "compiled semantics differ from the interpreted path"; fi

# ---- 4. no compiler: degrade to the interpreted path, same answers --------
nocc=$(LIN_STD="$NATIVE_STD" LIN_STD_DIR="$STD_DIR" LIN_NATIVE_CC=/nonexistent/cc timeout 60 "$BIN" "$TMP/sem.lin" 2>/dev/null)
if [ "$nocc" = "$base_got" ]; then ok; else fail "without a compiler the run changed"; fi

if [ "$FAIL" -eq 0 ]; then
  echo "native_cone: OK ($suites suites identical, $compiles cones compiled, saturating/zero-guard semantics pinned, degraded path identical)"
  exit 0
fi
echo "native_cone: $FAIL check(s) failed"
exit 1
