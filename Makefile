CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra -std=c99 -fopenmp
SRCS    := $(wildcard src/*.c) $(wildcard std/drivers/*.c)

build:
	nix build

lin: $(SRCS) src/lin.h
	$(CC) $(CFLAGS) -o $@ $(SRCS) -ldl

# Build ./lin from the WORKING TREE and run the full suite against it.
# This is the trusted dev path: unlike `nix flake check`/`nix run .#test`
# (which only see git-committed content because flakes stage `src = ./.`),
# it observes uncommitted edits - no dirty-tree staleness.
test: lin
	LIN_BIN=./lin test/run_tests.sh

# Nix repro/CI path (committed tree only).
nix-test:
	nix flake check

bench:
	nix run .#benchmarks

clean:
	rm -rf lin result test/line_binary.line

.PHONY: build test nix-test bench clean
