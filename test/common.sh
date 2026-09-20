#!/usr/bin/env bash
# Shared prologue for every Lin test entry point.
# --------------------------------------------------------------------------------
# Locates the checkout, resolves the engine binary and the std directory, exports them,
# and refuses to run against a non-executable engine.
#
# This was copy-pasted into test/run_tests.sh and test/driver_selftest.sh, and both copies
# carried the same bug: `STD_DIR="${STD_DIR:-$2}"; STD_DIR="${STD_DIR:-$ROOT/std}"` ignores an
# inherited LIN_STD_DIR, so a caller that hands over the *packaged* std -- where the driver
# plugins live -- is silently reset to the checkout's own `std/`, which under Nix contains
# `arith.c` but no `arith.so`.  The symptom was not a missing-plugin warning but
# `error: unbound variable 'num._padd'` and `error: no candidate produced an artifact`: the
# pure-Lin fallback cannot supply what the driver registers.  One implementation is what stops
# the next entry point from re-introducing it.
#
# Resolution order, most explicit first: LIN_BIN / STD_DIR from the environment, then argv[1] /
# argv[2], then LIN_STD_DIR from the environment, then the checkout's own std/.
#
# usage:
#   . "$(dirname "$0")/common.sh"
#   lin_test_env "${1:-}" "${2:-}" || exit 1
#   # now ROOT, LIN_BIN, STD_DIR, LIN_STD and LIN_STD_DIR are set, and cwd is ROOT

lin_test_env() {
  ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
  cd "$ROOT" || return 1
  LIN_BIN="${LIN_BIN:-$1}"
  LIN_BIN="${LIN_BIN:-./lin}"
  STD_DIR="${STD_DIR:-${2:-${LIN_STD_DIR:-$ROOT/std}}}"
  export LIN_STD="${LIN_STD:-$STD_DIR/std.lin}"
  export LIN_STD_DIR="$STD_DIR"
  if [ ! -x "$LIN_BIN" ]; then
    echo "Error: Lin binary '$LIN_BIN' not executable (run 'make lin' first)" >&2
    return 1
  fi
  return 0
}
