# Linden

Linden is a small game engine for Lin. A game is a value and two pure functions of
it: one says what the value looks like, the other what it becomes given the input
of that moment. Linden draws the picture, hands back the input, and keeps none of
the game's state. The same program runs in an X11 window, headless, or in a web
page.

```scheme
(load "std/std.lin")
(load "linden.lin")

(define draw   (\s <a frame>))
(define update (\s (\keys <the next state>)))
(game draw update start)
```

`examples/linden/leaves.lin` is a complete game in about 80 lines: move a basket
to catch falling leaves.

## Files

| File | Contents |
|------|----------|
| `linden.lin` | The Lin side: `game`, `run`, the drawing commands, keys and mouse |
| `linden.c` | The plugin: a rasteriser into a `0xRRGGBB` buffer, shown in a window, a PPM file or a canvas |
| `leaves.lin` | The example game |

## Running

From the repository root:

```bash
make linden
```

```bash
./lin examples/linden/leaves.lin
```

`make linden` builds the plugin with X11 when its headers are present, and a
headless-only plugin otherwise. The plugin is loaded by its path from the
repository root.

Headless runs are how a game is tested and timed. There is no pacing, and the
input can be scripted:

```bash
LINDEN_HEADLESS=1 LINDEN_FRAMES=600 LINDEN_PPM=leaves.ppm ./lin examples/linden/leaves.lin
```

| Variable | Meaning |
|----------|---------|
| `LINDEN_HEADLESS=1` | No window (also the default when there is no display) |
| `LINDEN_FRAMES=n` | Quit after `n` frames |
| `LINDEN_KEYS=m0,m1,...` | The keys of frame 0, 1, ...; the last one repeats |
| `LINDEN_PPM=path` | Write the last frame (`%d` in the path writes every frame) |
| `LINDEN_FPS=n` | The window's frame rate (default 60) |
| `LINDEN_SCALE=n` | Window pixels per frame pixel |

## In the browser

```bash
make all
```

```bash
nix shell nixpkgs#emscripten -c web/build.sh examples/linden/leaves.lin
```

Then serve `web/` with any static file server and open `linden.html`. The build
runs the game headless first to compile its functions ahead (WebAssembly cannot
load native code at run time), links Linden in, and copies the game into
`web/dist/games/`. The page runs one frame of the game per animation frame, with
the keyboard, touch buttons and the mouse as input.

## A frame

A frame is a list of drawing commands, and every command takes the rest of the
frame as its last argument, so a scene is commands nested in drawing order and
ended by `nil`:

```scheme
(frame W H (clear sky (rect x y 24 6 orange (number 4 4 score 1 white nil))))
```

| Command | Draws |
|---------|-------|
| `(clear c r)` | The whole frame in one colour |
| `(rect x y w h c r)`, `(box x y w h c r)` | A filled or outlined rectangle |
| `(line x0 y0 x1 y1 c r)` | A line |
| `(disc x y rad c r)` | A filled circle |
| `(tri x0 y0 x1 y1 x2 y2 c r)` | A filled triangle |
| `(number x y n s c r)`, `(text x y "str" s c r)`, `(glyph x y ch s c r)` | Digits and text, `s` pixels per dot |

Coordinates are integers and colours are `0xRRGGBB` numbers (`rgb r g b` builds
one). A part of a scene is a function that takes the rest too, which keeps a
frame a chain of calls the compiler turns into code.

## Input

`keys` holds the buttons down now and, shifted by 8, the ones pressed since the
last frame: `(down keys key_left)`, `(pressed keys key_start)`.

| Key | Buttons |
|-----|---------|
| `key_left`, `key_right`, `key_up`, `key_down` | Arrows, WASD |
| `key_a`, `key_b` | Space or Z; X or Shift |
| `key_start` | Enter |
| `key_quit` | Escape, closing the window, or the end of a headless run |

`(mouse)` and `(ticks)` are effects too, read with `io_wait`.

## More than one effect a frame

`game` is `run` with one frame per turn. A turn is any effect that ends in
`io_next` (the next state) or `io_done`, so a game can print, read files or call
other C functions between frames:

```scheme
(define turn (\s (play (draw s) (\keys
  (if (down keys key_quit) io_done (io_print (score s) (io_next (update s keys))))))))
(run turn start)
```

## Performance

Each turn the effects runner hands the game a fresh copy of its step, forces the
new state as data, and reclaims what the last turn left unreachable, so memory
stays flat over any number of frames. The function compiler
(`std/drivers/fn.c`) compiles the game's recursive functions over its state and
reads the state into them each frame. It also remembers the calls it cannot
compile, so it does not try them again every turn.

`leaves.lin` takes about 25 ms a frame natively, headless, and about 47 ms in
WebAssembly under Node. Most of that is `step` and `scene` evaluated on the net:
their non-recursive parts are not compiled yet.
