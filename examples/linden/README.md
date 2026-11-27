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
to catch falling leaves. `examples/linden/three.lin` is a 3D scene: a tree of
Gaussian splats on a checkered ground, rendered per pixel by a shader written in
Lin that runs on the GPU (see [3D, and the GPU](#3d-and-the-gpu)).

## Files

| File | Contents |
|------|----------|
| `linden.lin` | The Lin side: `game`, `run`, the drawing commands, keys and mouse |
| `linden.c` | The plugin: a rasteriser into a `0xRRGGBB` buffer, shown in a window, a PPM file or a canvas |
| `leaves.lin` | The example game |
| `three.lin` | The 3D example: a camera, a sky, a ground and Gaussian splats, its shader in Lin |

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
| `(image x y w h pixels r)` | A `w` by `h` block of pixels: a vector of colours, row by row |

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

## 3D, and the GPU

A 3D game renders its own picture and draws it with `image`. The picture is a
vector built one pixel at a time:

```scheme
(define tab (\cam (\i (\n (\acc
  (if (eq i n) acc (tab cam (add i 1) n (apush acc (shade cam i)))))))))
(image 0 0 W H (tab cam 0 (mul W H) (array 0 0)) rest)
```

`shade` is the shader: an ordinary Lin function of the pixel's index and of
values the whole frame shares (the camera, a vector of splats). Nothing marks it
as one. Each pixel is independent of the others, so the function compiler
(`std/drivers/fn.c`, A LOOP WHOSE STEPS ARE INDEPENDENT) writes the loop as a
GLSL compute kernel generated from the same definitions. The gpu driver
(`std/drivers/gpu.c`, KERNELS) compiles it with `glslangValidator` and runs it
through Vulkan. Without a device, or for a loop too small to be worth a dispatch
(`LIN_GPU_MIN`, 1024 pixels by default), the same loop runs on the CPU's threads.
Both give the same picture bit for bit. Floats are IEEE doubles on both, and
`fsin`/`fcos` share one argument reduction (`std/runtime/i64.h`). `fpow`,
`fatan2` and `ftan` keep a loop on the CPU, and `three.lin` writes its own `exp`.

`three.lin` projects its splats through the camera and sorts them by depth on
the CPU each frame. Each pixel then composites them front to back over the sky
or the ground its ray meets.

| Variable | Effect |
|----------|--------|
| `LIN_GPU=0` | Never dispatch to the GPU |
| `LIN_GPU_MIN` | The smallest loop sent to the GPU (default 1024 elements) |
| `LIN_GPU_DEBUG=1` | Report the device and each kernel run |
| `LIN_GLSLANG` | The shader compiler (default `glslangValidator` on the `PATH`) |

The Nix build puts `glslangValidator` and the Vulkan loader on `lin`'s path, and
the device's own driver comes from the system. To try it without a GPU, point
`VK_ICD_FILENAMES` at Mesa's lavapipe (`lvp_icd.x86_64.json`).

## Performance

Each turn the effects runner hands the game a fresh copy of its step, forces the
new state as data, and reclaims what the last turn left unreachable, so memory
stays flat over any number of frames. The function compiler
(`std/drivers/fn.c`) compiles the game's recursive functions over its state and
reads the state into them each frame. It also remembers the calls it cannot
compile, so it does not try them again every turn.

A frame's pixels reach the plugin flat, without being built in the net. The
numbers that change every frame, such as the frame counter and the camera, reach
the frame's compiled unit as a table it reads, so the unit is compiled with `cc`
once for the whole run, not once per frame.

`leaves.lin` takes about 25 ms a frame natively, headless, and about 47 ms in
WebAssembly under Node. Most of that is `step` and `scene` evaluated on the net:
their non-recursive parts are not compiled yet.

`three.lin` (160x120, about 160 splats) takes about 110 ms a frame headless on a
CPU-only machine. The shader itself takes about 5 ms on lavapipe. The rest is the
function compiler re-deriving the frame's unit from the net every frame before
it finds the unit already compiled. Recognising the same call without re-deriving
it is the next step.
