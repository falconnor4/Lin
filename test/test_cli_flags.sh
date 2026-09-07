#!/usr/bin/env bash
set -e

LIN_BIN="${1:-./result/bin/lin}"

if [ ! -x "$LIN_BIN" ]; then
  echo "Error: Lin binary '$LIN_BIN' not executable" >&2
  exit 1
fi

echo "Testing Lin CLI flags..."

# 1. Version flag
v_out=$("$LIN_BIN" -v)
if [ "$v_out" != "lin 0.1" ]; then
  echo "FAIL: expected 'lin 0.1', got '$v_out'" >&2
  exit 1
fi
echo "  PASS: -v flag"

# 2. Help flag
h_out=$("$LIN_BIN" -h 2>&1)
if ! printf '%s\n' "$h_out" | grep -q "usage:"; then
  echo "FAIL: expected usage output for -h" >&2
  exit 1
fi
echo "  PASS: -h flag"

# 3. Eval flag (-e)
e_out=$("$LIN_BIN" -e '(add 2 3)')
if [ "$e_out" != "=> 5" ]; then
  echo "FAIL: expected '=> 5', got '$e_out'" >&2
  exit 1
fi
echo "  PASS: -e flag"

# 4. Bench flag (-b)
b_out=$("$LIN_BIN" -b -e '(add 1 1)' 2>&1)
if ! printf '%s\n' "$b_out" | grep -q '\[bench\]'; then
  echo "FAIL: expected [bench] output with -b" >&2
  exit 1
fi
echo "  PASS: -b flag"

# 5. Threads flag (-t)
t_out=$("$LIN_BIN" -t 2 -e '(mul 3 3)')
if [ "$t_out" != "=> 9" ]; then
  echo "FAIL: expected '=> 9', got '$t_out'" >&2
  exit 1
fi
echo "  PASS: -t flag"

# 6. Unknown flag exit code
set +e
"$LIN_BIN" --invalid-flag >/dev/null 2>&1
code=$?
set -e
if [ "$code" -ne 1 ]; then
  echo "FAIL: expected exit code 1 for invalid flag, got $code" >&2
  exit 1
fi
echo "  PASS: invalid flag error handling"

# 7. Build container (-o)
TMP_DIR=$(mktemp -d)
trap 'rm -rf "$TMP_DIR"' EXIT
"$LIN_BIN" build test/line_binary.lin -o "$TMP_DIR/test.line"
if [ ! -x "$TMP_DIR/test.line" ]; then
  echo "FAIL: built container is not executable" >&2
  exit 1
fi
line_out=$("$LIN_BIN" "$TMP_DIR/test.line")
if [ "$line_out" != "LINE_BINARY_OK: 43" ]; then
  echo "FAIL: unexpected container output '$line_out'" >&2
  exit 1
fi
echo "  PASS: build -o line container"

echo "All CLI flag tests passed successfully!"
