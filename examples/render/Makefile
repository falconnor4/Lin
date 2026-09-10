# Build the Lin window-render helper (renderer-specific C, NOT part of the Lin
# engine).  Produces liblinrender.so which render.lin loads via generic FFI.
# SDL2 paths default to pkg-config; override with SDL2_INC / SDL2_LIB for Nix.

SDL2_INC ?= $(shell sdl2-config --cflags 2>/dev/null || echo)
SDL2_LIB ?= $(shell sdl2-config --libs 2>/dev/null || echo -lSDL2)

.PHONY: all clean run
all: liblinrender.so

liblinrender.so: render.c
	cc -O2 -Wall -Wextra -std=c99 -fPIC -shared $(SDL2_INC) -o $@ render.c $(SDL2_LIB)

# Run the wireframe demo against the built interpreter.
#   LIN = path to the lin binary (default: ./lin at repo root)
#   Also needs SDL2 (and any libs liblinrender.so links against) on LD_LIBRARY_PATH.
run: liblinrender.so
	LD_LIBRARY_PATH=$$PWD:$${LD_LIBRARY_PATH} \
		$${LIN:?set LIN=path/to/lin} render.lin

clean:
	rm -f liblinrender.so