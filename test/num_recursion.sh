#!/usr/bin/env bash
# ================================================================================
# A recursion whose argument is built by a recursion: the numerals' one open defect.
# --------------------------------------------------------------------------------
# This is the executable form of the goals.md defect: `_padd` over a chain whose cells
# were produced by `pred`'s BORROW branch (a chain whose tail is itself a recursive
# call) never reaches WHNF -- the fan-fan copy rule unrolls instead of converging.
# Everything here is a one-line program whose expected value is a LITERAL, so the
# assertion does not depend on how the printer renders a shared normal form:
#
#   the projection's RESULT is consumed by `ifl` and the branch returns a fresh literal,
#   so a value that is a shared/unprintable net still has to answer TRUE or FALSE.
#   (Printing the projection itself does NOT work as a test: the readback reports `?`
#   for shared normal forms by design, and a decoded-looking closure tree can be either
#   a correct value it declined to decode or a wrong one -- measured both ways, see
#   goals.md.  A test that cannot tell those two apart is not a test.)
#
# A failing case can fail THREE ways, and all three count as the defect: a stall (no value in
# 20s), a WRONG value (`(num.is_zero (num.pred (num.pred 2)))` answers with a chain, not a bool,
# measured -- read every "stall" in the log below as "stall OR wrong value"), and a type
# mismatch (`(num.is_zero (num.pred (_padd 2 0)))` is refused before it can run at all).
#
# Each case is bounded by its own `timeout`, because a stall is the failure mode: the
# suite's own runner has no per-case timeout, so these cannot live in test/run_tests.sh
# until they pass -- a stalling case there would hang the whole run.
#
# Usage: test/num_recursion.sh [LIN_BIN] [LIN_STD_DIR]     (defaults as test/common.sh)
# ================================================================================
set -u
. "$(dirname "$0")/common.sh"
lin_test_env "${1:-}" "${2:-}" || exit 1

C1='(num.cons_ bool.true (num.nil_))'
C2='(num.cons_ bool.false (num.cons_ bool.true (num.nil_)))'

pass=0; fail=0
run () { # run <label> <want> <cond>
  local label=$1 want=$2 cond=$3
  local src; src=$(mktemp)
  printf '(io_print (ifl %s (\\_ 1) (\\_ 0)) io_done)\n' "$cond" > "$src"
  local got; got=$(LIN_STD_DIR="$STD_DIR" timeout 20 "$LIN_BIN" "$src" 2>/dev/null); local rc=$?
  rm -f "$src"
  if [ "$rc" = 124 ]; then printf 'STALL %-44s %s\n' "$label" "(no value in 20s -- the defect)"
  elif [ "$got" = "$want" ]; then pass=$((pass+1)); printf 'PASS  %-44s %s\n' "$label" "$got"
  else fail=$((fail+1)); printf 'FAIL  %-44s got %s want %s\n' "$label" "$got" "$want"; fi
}

# `_padd x 0` over a 1-cell chain works today; over a 2-cell chain it is the defect.
run 'empty? tl (_padd 1 0)'        1 "(num.empty? (num.tl (num._padd $C1 0)))"
run 'hd (_padd 1 0)'               1 "(num.hd (num._padd $C1 0))"
run 'empty? tl tl (_padd 2 0)'     1 "(num.empty? (num.tl (num.tl (num._padd $C2 0))))"
run 'hd tl (_padd 2 0)'            1 "(num.hd (num.tl (num._padd $C2 0)))"
run 'empty? (_padd 2 0)'           0 "(num.empty? (num._padd $C2 0))"
run 'is_zero (pred (_padd 2 0))'   0 "(num.is_zero (num.pred (num._padd $C2 0)))"
# the same shape with no list, no projection and no literal: a counter decremented by pred
run 'is_zero (pred (pred 2))'      1 "(num.is_zero (num.pred (num.pred 2)))"
run 'is_zero (pred (pred (pred 2)))' 0 "(num.is_zero (num.pred (num.pred (num.pred 2))))"

printf -- '------------------------------------------------------------------------\n'
printf 'num_recursion: %d passed, %d failed\n' "$pass" "$fail"
[ "$fail" = 0 ]
