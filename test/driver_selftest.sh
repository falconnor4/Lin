#!/usr/bin/env bash
# ================================================================================
# Canonical Cross-Driver Selftest Runner
# --------------------------------------------------------------------------------
# Verifies every Lin reduction driver against the base CPU engine (the golden
# oracle) using the canonical corpus in std/selftest.lin.  This is the driver
# correctness CONTRACT: ANY driver - existing or future - is validated solely
# by loading its std module, running the SAME corpus, and requiring that its
# readback values match the base engine's exactly, value-for-value.
#
#   - Value equality: the driver's probe lines must equal the CPU golden's.
#   - Fold reporting: the trailing (folds) line is reported per driver but is
#     NOT part of the equality contract - folding is each driver's own
#     optimization decision (folded need not be true).
#   - Driver coverage is assertable but not enforced here: a driver that makes
#     no claim simply reproduces the base output unchanged (base does the work).
#
# Register a driver by adding its module name to DRIVERS below; the script is
# otherwise driver-agnostic, so a new driver needs no bespoke test file.
#
# Usage:
#   test/driver_selftest.sh [LIN_BIN] [LIN_STD_DIR]
# ================================================================================

set -e
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

LIN_BIN="${LIN_BIN:-$1}"
LIN_BIN="${LIN_BIN:-./lin}"
STD_DIR="${STD_DIR:-$2}"
STD_DIR="${STD_DIR:-$ROOT/std}"
export LIN_STD="${LIN_STD:-$STD_DIR/std.lin}"
export LIN_STD_DIR="$STD_DIR"

if [ ! -x "$LIN_BIN" ]; then
  echo "Error: Lin binary '$LIN_BIN' not executable (run 'make lin' first)" >&2
  exit 1
fi

# ----------------------------------------------------------------------------
# Registry of drivers to validate against the CPU golden.  Each entry is the
# std module (relative to LIN_STD_DIR) that activates the driver; the runner
# loads it before the canonical corpus.  A future driver only needs a row here.
# ----------------------------------------------------------------------------
DRIVERS=(simd gpu)

TMP_DIR=$(mktemp -d)
trap 'rm -rf "$TMP_DIR"' EXIT

CORPUS="$STD_DIR/selftest.lin"
for d in "${DRIVERS[@]}"; do
  [ -f "$STD_DIR/drivers/$d.lin" ] || { echo "SKIP  $d (no std/drivers/$d.lin)"; continue; }
done

# ----------------------------------------------------------------------------
# Run the corpus under a given driver and emit the probe lines (dropping the
# runner's leading '=> 1' activation line).  Returns full output via stdout.
#   run_corpus <driver-name-cpu|simd|gpu>
# ----------------------------------------------------------------------------
run_corpus() {
  local drv="$1" wrap="$TMP_DIR/wrap.lin"
  if [ "$drv" = cpu ]; then
    # Golden: base engine, no accelerator driver active.
    printf '(load "std/drivers/driver.lin")\n(set_driver "cpu")\n(load "std/selftest.lin")\n' > "$wrap"
  else
    # Driver under test: activate its module, then the shared corpus.
    printf '(load "std/drivers/%s.lin")\n(load "std/selftest.lin")\n' "$drv" > "$wrap"
  fi
  "$LIN_BIN" "$wrap" 2>/dev/null | grep '^=> ' | tail -n +2 || true
}

printf "Canonical Driver Selftest against %s\n" "$LIN_BIN"
printf "corpus: %s\n" "$CORPUS"

golden="$(run_corpus cpu)"
nprobe=$(printf '%s\n' "$golden" | grep -c '^=> ' || true)
gfolds=$(printf '%s\n' "$golden" | tail -n 1 | sed 's/^=> *//')

pass=0; fail=0
for d in "${DRIVERS[@]}"; do
  [ -f "$STD_DIR/drivers/$d.lin" ] || continue
  got="$(run_corpus "$d")"
  n=$(printf '%s\n' "$got" | grep -c '^=> ' || true)
  folds=$(printf '%s\n' "$got" | tail -n 1 | sed 's/^=> *//')
  # Compare all but the trailing fold-count line.
  ok=1; [ "$n" -eq "$nprobe" ] || ok=0
  if [ "$ok" = 1 ] && [ "$n" -gt 0 ]; then
    cmp -s <(printf '%s\n' "$golden" | head -n -1) \
           <(printf '%s\n' "$got" | head -n -1) || ok=0
  fi
  if [ "$ok" = 1 ]; then pass=$((pass+1)); printf "PASS  %-6s (%2d probes equal; %s native folds)\n" "$d" "$((n-1))" "$folds"
  else fail=$((fail+1)); printf "FAIL  %-6s (golden %d probes vs %s %d probes)\n" "$d" "$nprobe" "$d" "$n"
    echo "--- golden ---"; printf '%s\n' "$golden"
    echo "--- $d ---";    printf '%s\n' "$got"
  fi
done

echo "========================================================================"
if [ "$fail" -eq 0 ]; then
  echo "SELFTEST OK: $pass drivers match the CPU golden ($nprobe probes; golden $gfolds folds)"
else
  echo "SELFTEST FAILURE: $fail failed, $pass passed"
fi
echo "========================================================================"
exit $fail