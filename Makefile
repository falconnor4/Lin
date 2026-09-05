CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra -std=c99 -fopenmp
SRCS    := $(wildcard src/*.c) $(wildcard std/drivers/*.c)

build:
	nix build

lin: $(SRCS) src/lin.h
	$(CC) $(CFLAGS) -o $@ $(SRCS) -ldl

test:
	nix flake check

bench:
	nix run .#benchmarks

clean:
	rm -rf lin result test/line_binary.line

.PHONY: build test bench clean
