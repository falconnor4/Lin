# Linden

Linden is a 3D wireframe renderer packaged as a Lin driver that lives outside the
standard library. It shows how an application can bring its own native engine:
the plugin is loaded by path, registered by name, and called through `ccall` like
any other C function.

```scheme
(load_lib "./linden/linden.so")
(set_driver "linden")
(ccall "lin_fp_linden_frame" args)
```

## Files

| File | Contents |
|------|----------|
| `linden.c` | The plugin: a rasteriser with three outputs (characters on standard output, an X11 window, a PPM image) |
| `cube.lin` | A rotating cube drawn as characters in the terminal |
| `cube_1.lin`, `cube_64.lin`, `cube_4096.lin` | The same scene for 1, 64 and 4,096 frames, for timing |
| `view.lin` | The cube in an X11 window |
| `shot.lin` | One frame written to a PPM file, with no window |
| `bench.lin`, `probe.lin` | Small programs used while developing the plugin |

## Building and running

The plugin needs the X11 development headers. From the repository root:

```bash
mkdir -p linden
cc -O2 -fPIC -shared -I src -o linden/linden.so examples/linden/linden.c -lm -lX11
./lin examples/linden/cube.lin
```

The programs load `./linden/linden.so` relative to the working directory, so run
them from the directory that contains `linden/`.

## The argument list

A scene is passed as one flat list of numbers:

```
W H nv ne   x0 y0 z0 ...   i0 j0 ...   t0 dt frames
```

The grid size, the vertex and edge counts, the vertices, the edges as pairs of
vertex indices, then the start angle, the angle step and the number of frames.
Nothing about the mesh is built into the plugin: another list is another picture.
