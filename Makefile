CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra -std=c99 -fopenmp
SRCS    := $(wildcard src/*.c)
DRIVERS := $(wildcard std/drivers/*.c)

build:
	nix build

# Core engine only: the language/runtime is src/*.c + src/lin.h (compact,
# <= 2500 lines).  -rdynamic exports the core's symbols so dlopen'd driver
# plugins (simd.so) can resolve net_alloc_scott / net_read_int / net_link &c.
lin: $(SRCS) src/lin.h
	$(CC) $(CFLAGS) -rdynamic -o $@ $(SRCS) -ldl -lm

# Accelerator drivers (e.g. SIMD native arithmetic) are optional loaded plugins,
# compiled to std/drivers/*.so and dlopen'd at runtime by (set_driver "simd").
plugins: $(DRIVERS)
	@for d in $(DRIVERS); do \
	  n=$${d%.c}.so; \
	  $(CC) -O2 -Wall -Wextra -std=c99 -fopenmp -fPIC -shared -o $$n $$d -ldl -lm; \
	done

# Build core + plugins (trusted working-tree path).
all: lin plugins

# Build ./lin from the WORKING TREE and run the full suite against it.
# This is the trusted dev path: unlike `nix flake check`/`nix run .#test`
# (which only see git-committed content - see note below), it observes
# uncommitted edits - no dirty-tree staleness.
test: all
	LIN_BIN=./lin test/run_tests.sh

# Nix repro/CI path (committed tree only).
nix-test:
	nix flake check

bench:
	nix run .#benchmarks

# One-command window render: build the interpreter + the render helper, then
# run the wireframe demo.  Needs SDL2 on the compile/link path (see
# examples/render/Makefile for Nix SDL2_INC/SDL2_LIB overrides).
render: lin
	$(MAKE) -C examples/render all
	LD_LIBRARY_PATH="$$PWD/examples/render:$${LD_LIBRARY_PATH}" \
		./lin examples/render/render.lin

clean:
	rm -rf lin result test/line_binary.line std/drivers/*.so

.PHONY: build test nix-test bench clean all plugins render
