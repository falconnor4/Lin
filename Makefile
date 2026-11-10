CC      ?= cc
# No -fopenmp: the parallel engine is pthreads, and the dispatch width comes from -t or
# OMP_NUM_THREADS when the compiler supplies OpenMP.  Any C99 compiler can build it.
CFLAGS  ?= -O2 -Wall -Wextra -std=c99
SRCS    := $(wildcard src/*.c)
DRIVERS := $(wildcard std/drivers/*.c)

build:
	nix build

# Core engine only: the language/runtime is src/*.c + src/lin.h (test/run_tests.sh
# reports its size on every run).
# -rdynamic exports the core's symbols so dlopen'd driver
# plugins (simd.so) can resolve net_alloc_scott / net_read_int / net_link &c.
lin: $(SRCS) src/lin.h
	$(CC) $(CFLAGS) -rdynamic -o $@ $(SRCS) -ldl -lm -lpthread -lffi

# Accelerator drivers (e.g. SIMD native arithmetic) are optional loaded plugins,
# compiled to std/drivers/*.so and dlopen'd at runtime by (set_driver "simd").
plugins: $(DRIVERS)
	@for d in $(DRIVERS); do \
	  n=$${d%.c}.so; \
	  $(CC) -O2 -Wall -Wextra -std=c99 -fPIC -shared -o $$n $$d -ldl -lm -lpthread -lffi; \
	done

# Build core + plugins (trusted working-tree path).
all: lin plugins

# Build ./lin from the WORKING TREE and run the full suite against it.
# This is the trusted dev path: unlike `nix flake check`/`nix run .#test`
# (which only see git-committed content - see note below), it observes
# uncommitted edits - no dirty-tree staleness.
test: all
	LIN_BIN=./lin test/run_tests.sh
	python3 test/parity.py

test-boot: all
	LIN_BIN=./bin/lin-boot test/run_tests.sh

parity: all
	python3 test/parity.py

# Nix repro/CI path (committed tree only).
nix-test:
	nix flake check

bench:
	nix run .#benchmarks

clean:
	rm -rf lin result test/line_binary.line std/drivers/*.so

.PHONY: build test test-boot parity nix-test bench clean all plugins
