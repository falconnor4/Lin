#!/usr/bin/env bash
# The one implementation of Lin's `; expect` value check.
# --------------------------------------------------------------------------------
# Both suites and the examples sweep need the same thing: run a `.lin` file, take its
# stdout, and compare it line for line against the file's own `; expect` comments.
#
# That logic used to exist THREE times -- here in test/run_tests.sh, again in
# examples/run_verifier.sh, and a third time embedded in flake.nix's testRunner -- and the
# copies had already diverged in ways that mattered: the flake's copy asserted a stricter
# container shebang than run_tests.sh (`^#!/usr/bin/env lin` where the engine writes
# `#!<realpath argv[0]>`), and it ran 46 suites where run_tests.sh ran 57, so a test added to
# run_tests.sh alone never reached CI. A shared implementation is what makes that class of
# drift impossible rather than merely noticed.
#
# This function only decides pass/fail and exposes the strings; callers own their formatting,
# because the suites want timings and the examples sweep wants interaction counts.
#
# A trailing `...` in an expectation is a prefix match.
#
# usage:
#   . "$(dirname "$0")/../test/expect.sh"
#   lin_expect_check "$LIN_BIN" path/to/file.lin
#   [ "$EXP_OK" = 1 ] || echo "got $EXP_GOT want $EXP_WANT ($EXP_N checks)"

lin_expect_check() {
  local bin="$1" f="$2"
  # Capture stdout only.  Diagnostics (driver fallback warnings, etc.) go to stderr and must
  # not be merged into the readback stream: `2>&1` interleaves them onto stdout *data* lines at
  # the pipe level, which breaks line-for-line equality when a warning fires mid-expression.
  EXP_GOT=$("$bin" "$f" 2>/dev/null || true)
  EXP_WANT=$(grep '^; expect ' "$f" | sed 's/^; expect //')
  local gn wn
  gn=$(printf '%s\n' "$EXP_GOT"  | grep -c . || true)
  wn=$(printf '%s\n' "$EXP_WANT" | grep -c . || true)
  EXP_N="$wn"
  EXP_OK=1
  [ "$gn" = "$wn" ] || EXP_OK=0
  if [ "$EXP_OK" = 1 ] && [ "$wn" -gt 0 ]; then
    local i=1 w g pfx
    while [ "$i" -le "$wn" ]; do
      w=$(printf '%s\n' "$EXP_WANT" | sed -n "${i}p")
      g=$(printf '%s\n' "$EXP_GOT"  | sed -n "${i}p")
      case "$w" in
        *...) pfx="${w%...}"; case "$g" in "$pfx"*) ;; *) EXP_OK=0 ;; esac ;;
        *)    [ "$w" = "$g" ] || EXP_OK=0 ;;
      esac
      i=$((i + 1))
    done
  fi
  return 0
}

# Does this file carry expectations at all?  The examples sweep reports the rest as interactive.
lin_has_expects() { grep -q '^; expect' "$1"; }
