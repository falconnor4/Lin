#!/bin/sh
set -e
cd "$(dirname "$0")/.."

# 1. Build .line binary
./lin build test/line_binary.lin -o test/line_binary.line

# 2. Check file exists and is executable
if [ ! -x test/line_binary.line ]; then
  echo "FAIL: test/line_binary.line is not executable"
  exit 1
fi

# 3. Verify shebang header
if ! head -n 1 test/line_binary.line | grep -q '^#!/usr/bin/env lin'; then
  echo "FAIL: test/line_binary.line missing lin shebang"
  exit 1
fi

# 4. Run via engine
out1=$(./lin test/line_binary.line)
if [ "$out1" != "LINE_BINARY_OK: 43" ]; then
  echo "FAIL: unexpected engine output: $out1"
  exit 1
fi

# 5. Run directly as standalone binary
export PATH="$PWD:$PATH"
out2=$(./test/line_binary.line)
if [ "$out2" != "LINE_BINARY_OK: 43" ]; then
  echo "FAIL: unexpected direct binary output: $out2"
  exit 1
fi

# 6. Clean up
rm -f test/line_binary.line

echo "PASS test/line_binary (.line container build & execute)"
