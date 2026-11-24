/* Linden -- a small game engine for Lin.  THIS FILE DOES NOT LIVE IN std/: an engine is an application's,
 * not the standard library's.  A program loads it by path (examples/linden/linden.lin does this):
 *
 *     (load_lib "examples/linden/linden.so")
 *
 * Natively that dlopens this file's shared object, whose constructor registers the calls below; in a
 * static build (the browser) the same line starts the copy linked in.  Nothing else differs.
 *
 * THE WHOLE INTERFACE IS ONE CALL A FRAME.  A game is an effect loop over its state (std/io.lin's io_loop):
 *
 *     (io_loop start (\s (io_wait (ccall "linden_frame" (draw s)) (\keys (io_next (update s keys))))))
 *
 * (linden.lin's `game draw update start` is that loop.)
 * `draw s` is a flat list of integers -- the frame's size, then drawing commands -- and the call
 * answers with the input held at that moment.  The game's state is an ordinary Lin value; Linden
 * keeps nothing of it.  So a frame is a pure function of the state, and the loop is the one place the
 * program meets the world.
 *
 *     W H  op args  op args ...
 *
 *     0 c                     clear to colour c
 *     1 x y w h c             filled rectangle
 *     2 x0 y0 x1 y1 c         line
 *     3 cx cy r c             filled circle
 *     4 x0 y0 x1 y1 x2 y2 c   filled triangle
 *     5 x y n s c             the integer n, glyphs s pixels per dot
 *     6 x y ch s c            one character (its code)
 *     7 x y w h c             rectangle outline
 *
 * Colours are 0xRRGGBB.  A command cut short by the end of the list is ignored, as is an unknown op
 * (which ends the frame: its length is not known, so nothing after it can be read).
 *
 * THE ANSWER (keys): the buttons held, and in bits 8..15 the ones pressed since the last frame.
 *     1 left  2 right  4 up  8 down  16 A (space, z)  32 B (x, shift)  64 start (enter)  128 quit
 * `quit` is the window closing or Escape -- or, headless, the frame budget running out.
 *
 *     linden_mouse   x + 65536*y + 2^32*buttons, in frame pixels
 *     linden_ticks   milliseconds since the first frame
 *
 * THREE PLACES A FRAME CAN GO, one rasteriser (a 0xRRGGBB buffer of W*H):
 *   an X11 window      when there is a display: scaled up, paced to LINDEN_FPS (default 60).
 *   nowhere (headless) LINDEN_HEADLESS=1, or no display.  LINDEN_FRAMES=n quits after n frames,
 *                      LINDEN_KEYS="m0,m1,..." is the input of frame 0, 1, ... (the last repeats), and
 *                      LINDEN_PPM=path writes the last frame ("%d" in the path: every frame).
 *                      This is how a game is tested, and how it is benchmarked: no pacing.
 *   a canvas           the browser build (web/): the page shows the buffer and the io loop gives the page
 *                      its turn after each frame (lin_io_yield), resuming on the next animation frame.
 */
#include "../../src/lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#define LD_EXPORT EMSCRIPTEN_KEEPALIVE
#else
#define LD_EXPORT
#include <unistd.h>
#ifndef LINDEN_NO_X11
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/XKBlib.h>
#endif
#endif

enum { K_LEFT = 1, K_RIGHT = 2, K_UP = 4, K_DOWN = 8, K_A = 16, K_B = 32, K_START = 64, K_QUIT = 128 };

static int W, H;                 /* the current frame's size (the program states it every frame) */
static uint32_t *fb;             /* W*H, 0xRRGGBB */
static int held, prev_held;      /* buttons */
static int mouse_x, mouse_y, mouse_b;
static int64_t nframes;
static double t_start;

static double now_ms(void) {
  struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1000.0 + (double)ts.tv_nsec / 1e6;
}

/* ---------------- the rasteriser ---------------- */
static inline void px(int x, int y, uint32_t c) { if ((unsigned)x < (unsigned)W && (unsigned)y < (unsigned)H) fb[(size_t)y * W + x] = c; }

static void fill_rect(int64_t x, int64_t y, int64_t w, int64_t h, uint32_t c) {
  int64_t x0 = x < 0 ? 0 : x, y0 = y < 0 ? 0 : y, x1 = x + w > W ? W : x + w, y1 = y + h > H ? H : y + h;
  for (int64_t j = y0; j < y1; j++) for (int64_t i = x0; i < x1; i++) fb[(size_t)j * W + i] = c;
}

static void line(int64_t x0, int64_t y0, int64_t x1, int64_t y1, uint32_t c) {
  int64_t dx = x1 > x0 ? x1 - x0 : x0 - x1, dy = -(y1 > y0 ? y1 - y0 : y0 - y1);
  int64_t sx = x0 < x1 ? 1 : -1, sy = y0 < y1 ? 1 : -1, e = dx + dy;
  /* (clipped by the walk's own bound: a line far off screen still ends, it just draws nothing) */
  for (;;) {
    px((int)x0, (int)y0, c);
    if (x0 == x1 && y0 == y1) break;
    int64_t e2 = 2 * e;
    if (e2 >= dy) { e += dy; x0 += sx; }
    if (e2 <= dx) { e += dx; y0 += sy; }
  }
}

static void circle(int64_t cx, int64_t cy, int64_t r, uint32_t c) {
  if (r < 0) return;
  for (int64_t j = -r; j <= r; j++) {
    int64_t y = cy + j; if (y < 0 || y >= H) continue;
    int64_t w = 0; while ((w + 1) * (w + 1) + j * j <= r * r) w++;
    fill_rect(cx - w, y, 2 * w + 1, 1, c);
  }
}

static void tri(int64_t x0, int64_t y0, int64_t x1, int64_t y1, int64_t x2, int64_t y2, uint32_t c) {
  int64_t minx = x0 < x1 ? x0 : x1; if (x2 < minx) minx = x2;
  int64_t maxx = x0 > x1 ? x0 : x1; if (x2 > maxx) maxx = x2;
  int64_t miny = y0 < y1 ? y0 : y1; if (y2 < miny) miny = y2;
  int64_t maxy = y0 > y1 ? y0 : y1; if (y2 > maxy) maxy = y2;
  minx = minx < 0 ? 0 : minx; miny = miny < 0 ? 0 : miny;
  maxx = maxx >= W ? W - 1 : maxx; maxy = maxy >= H ? H - 1 : maxy;
  int64_t area = (x1 - x0) * (y2 - y0) - (y1 - y0) * (x2 - x0);
  if (area == 0) return;
  for (int64_t y = miny; y <= maxy; y++)
    for (int64_t x = minx; x <= maxx; x++) {
      int64_t w0 = (x1 - x) * (y2 - y) - (y1 - y) * (x2 - x);
      int64_t w1 = (x2 - x) * (y0 - y) - (y2 - y) * (x0 - x);
      int64_t w2 = (x0 - x) * (y1 - y) - (y0 - y) * (x1 - x);
      if (area > 0 ? (w0 >= 0 && w1 >= 0 && w2 >= 0) : (w0 <= 0 && w1 <= 0 && w2 <= 0)) fb[(size_t)y * W + x] = c;
    }
}

/* A 3x5 font: each glyph is five rows of three dots, written as the dots themselves. */
static const char *font_src[] = {
  "0111101101101111", "1010110010010111", "2111001111100111", "3111001111001111", "4101101111001001",
  "5111100111001111", "6111100111101111", "7111001010010010", "8111101111101111", "9111101111001111",
  "A010101111101101", "B110101110101110", "C011100100100011", "D110101101101110", "E111100110100111",
  "F111100110100100", "G011100101101011", "H101101111101101", "I111010010010111", "J001001001101010",
  "K101101110101101", "L100100100100111", "M101111111101101", "N110101101101101", "O010101101101010",
  "P110101110100100", "Q010101101110011", "R110101110101101", "S011100010001110", "T111010010010010",
  "U101101101101111", "V101101101101010", "W101101111111101", "X101101010101101", "Y101101010010010",
  "Z111001010100111", "-000000111000000", ":000010000010000", ".000000000000010", "!010010010000010",
  "?111001010000010", "/001001010100100", "+000010111010000", "=000111000111000", ",000000000010100",
  "'010010000000000", "(001010010010001", ")100010010010100", "*101010101000000", "<001010100010001",
  ">100010001010100", "#101111101111101", "%101001010100101", "_000000000000111",
};
static uint16_t glyph[128];
static void font_init(void) {
  for (size_t g = 0; g < sizeof font_src / sizeof *font_src; g++) {
    uint16_t m = 0;
    for (int b = 0; b < 15; b++) m = (uint16_t)(m << 1 | (font_src[g][1 + b] == '1'));
    glyph[(unsigned char)font_src[g][0]] = m;
  }
}
static void draw_char(int64_t x, int64_t y, int64_t ch, int64_t s, uint32_t c) {
  if (ch >= 'a' && ch <= 'z') ch -= 32;
  if (ch < 0 || ch >= 128 || s < 1) return;
  uint16_t m = glyph[ch];
  for (int r = 0; r < 5; r++) for (int k = 0; k < 3; k++)
    if (m >> (14 - (r * 3 + k)) & 1) fill_rect(x + k * s, y + r * s, s, s, c);
}
static void draw_num(int64_t x, int64_t y, int64_t n, int64_t s, uint32_t c) {
  char buf[32]; int len = snprintf(buf, sizeof buf, "%lld", (long long)n);
  for (int i = 0; i < len; i++) draw_char(x + i * 4 * s, y, buf[i], s, c);
}

/* Run a frame's commands.  0: the list does not even state a size. */
static int render(int argc, const int64_t *a) {
  if (argc < 2 || a[0] <= 0 || a[1] <= 0) return 0;
  if (a[0] != W || a[1] != H || !fb) {
    uint32_t *nb = realloc(fb, (size_t)a[0] * (size_t)a[1] * sizeof *fb);
    if (!nb) return 0;
    fb = nb; W = (int)a[0]; H = (int)a[1];
    memset(fb, 0, (size_t)W * H * sizeof *fb);
  }
  static const int len[] = { 1, 5, 5, 4, 7, 5, 5, 5 };
  int i = 2;
  while (i < argc) {
    int64_t op = a[i++];
    if (op < 0 || op >= (int64_t)(sizeof len / sizeof *len)) break;
    if (i + len[op] > argc) break;
    const int64_t *p = a + i; i += len[op];
    switch (op) {
      case 0: { uint32_t c = (uint32_t)p[0]; for (size_t k = 0; k < (size_t)W * H; k++) fb[k] = c; } break;
      case 1: fill_rect(p[0], p[1], p[2], p[3], (uint32_t)p[4]); break;
      case 2: line(p[0], p[1], p[2], p[3], (uint32_t)p[4]); break;
      case 3: circle(p[0], p[1], p[2], (uint32_t)p[3]); break;
      case 4: tri(p[0], p[1], p[2], p[3], p[4], p[5], (uint32_t)p[6]); break;
      case 5: draw_num(p[0], p[1], p[2], p[3], (uint32_t)p[4]); break;
      case 6: draw_char(p[0], p[1], p[2], p[3], (uint32_t)p[4]); break;
      case 7: fill_rect(p[0], p[1], p[2], 1, (uint32_t)p[4]); fill_rect(p[0], p[1] + p[3] - 1, p[2], 1, (uint32_t)p[4]);
              fill_rect(p[0], p[1], 1, p[3], (uint32_t)p[4]); fill_rect(p[0] + p[2] - 1, p[1], 1, p[3], (uint32_t)p[4]); break;
    }
  }
  return 1;
}

static int answer(void) {
  int pressed = held & ~prev_held;
  prev_held = held;
  return held | pressed << 8;
}

/* ---------------- the browser: the page reads the buffer and writes the input ---------------- */
#ifdef __EMSCRIPTEN__
LD_EXPORT uint32_t *linden_fb(void) { return fb; }
LD_EXPORT int linden_w(void) { return W; }
LD_EXPORT int linden_h(void) { return H; }
LD_EXPORT void linden_input(int keys, int mx, int my, int mb) { held = keys; mouse_x = mx; mouse_y = my; mouse_b = mb; }
static int present(void) { lin_io_yield = 1; return answer(); }   /* the page's turn: show it, then resume */
#else

/* ---------------- headless ---------------- */
static int headless = -1;
static int64_t frame_budget = -1;
static const char *ppm_path;

static void write_ppm(const char *path) {
  if (!fb) return;
  FILE *f = fopen(path, "wb");
  if (!f) { fprintf(stderr, "linden: cannot write '%s'\n", path); return; }
  fprintf(f, "P6\n%d %d\n255\n", W, H);
  for (size_t i = 0; i < (size_t)W * H; i++) { unsigned char rgb[3] = { fb[i] >> 16, fb[i] >> 8, fb[i] }; fwrite(rgb, 1, 3, f); }
  fclose(f);
}
static void at_exit(void) { if (ppm_path && !strchr(ppm_path, '%')) write_ppm(ppm_path); }

static int scripted_keys(int64_t f) {
  const char *s = getenv("LINDEN_KEYS");
  if (!s || !*s) return 0;
  int64_t k = 0; long v = strtol(s, NULL, 0);
  for (const char *p = s; *p && k < f; p++) if (*p == ',') { k++; v = strtol(p + 1, NULL, 0); }
  return (int)v;
}

/* ---------------- X11 ---------------- */
#ifndef LINDEN_NO_X11
static Display *dpy; static Window win; static XImage *img; static GC gc; static Atom wm_delete;
static int scale = 0, PW, PH;
static int key_bit(KeySym ks) {
  switch (ks) {
    case XK_Left: case XK_a: case XK_A: return K_LEFT;
    case XK_Right: case XK_d: case XK_D: return K_RIGHT;
    case XK_Up: case XK_w: case XK_W: return K_UP;
    case XK_Down: case XK_s: case XK_S: return K_DOWN;
    case XK_space: case XK_z: case XK_Z: case XK_j: return K_A;
    case XK_x: case XK_X: case XK_Shift_L: case XK_Shift_R: case XK_k: return K_B;
    case XK_Return: return K_START;
    case XK_Escape: return K_QUIT;
  }
  return 0;
}
static int x_open(void) {
  dpy = XOpenDisplay(NULL);
  if (!dpy) return 0;
  const char *sc = getenv("LINDEN_SCALE");
  scale = sc ? atoi(sc) : 0;
  if (scale < 1) { scale = 960 / W; if (scale < 1) scale = 1; }
  PW = W * scale; PH = H * scale;
  int s = DefaultScreen(dpy);
  win = XCreateSimpleWindow(dpy, RootWindow(dpy, s), 0, 0, (unsigned)PW, (unsigned)PH, 0, BlackPixel(dpy, s), BlackPixel(dpy, s));
  XStoreName(dpy, win, getenv("LINDEN_TITLE") ? getenv("LINDEN_TITLE") : "Linden");
  XSelectInput(dpy, win, KeyPressMask | KeyReleaseMask | ButtonPressMask | ButtonReleaseMask | PointerMotionMask | StructureNotifyMask);
  wm_delete = XInternAtom(dpy, "WM_DELETE_WINDOW", False);
  XSetWMProtocols(dpy, win, &wm_delete, 1);
  XkbSetDetectableAutoRepeat(dpy, True, NULL);   /* a held key is held, not pressed again and again */
  XMapWindow(dpy, win);
  gc = DefaultGC(dpy, s);
  img = XCreateImage(dpy, DefaultVisual(dpy, s), (unsigned)DefaultDepth(dpy, s), ZPixmap, 0, malloc((size_t)PW * PH * 4), (unsigned)PW, (unsigned)PH, 32, 0);
  return img != NULL;
}
static void x_present(void) {
  if (W * scale != PW || H * scale != PH) {    /* the program changed its size: the window follows */
    PW = W * scale; PH = H * scale;
    XResizeWindow(dpy, win, (unsigned)PW, (unsigned)PH);
    XDestroyImage(img);
    int s = DefaultScreen(dpy);
    img = XCreateImage(dpy, DefaultVisual(dpy, s), (unsigned)DefaultDepth(dpy, s), ZPixmap, 0, malloc((size_t)PW * PH * 4), (unsigned)PW, (unsigned)PH, 32, 0);
  }
  uint32_t *d = (uint32_t *)img->data;
  for (int y = 0; y < PH; y++) {
    const uint32_t *row = fb + (size_t)(y / scale) * W;
    for (int x = 0; x < PW; x++) d[(size_t)y * PW + x] = row[x / scale];
  }
  XPutImage(dpy, win, gc, img, 0, 0, 0, 0, (unsigned)PW, (unsigned)PH);
  XFlush(dpy);
  while (XPending(dpy)) {
    XEvent ev; XNextEvent(dpy, &ev);
    switch (ev.type) {
      case KeyPress: held |= key_bit(XLookupKeysym(&ev.xkey, 0)); break;
      case KeyRelease: held &= ~key_bit(XLookupKeysym(&ev.xkey, 0)); break;
      case MotionNotify: mouse_x = ev.xmotion.x / scale; mouse_y = ev.xmotion.y / scale; break;
      case ButtonPress: mouse_b |= 1 << (ev.xbutton.button - 1); break;
      case ButtonRelease: mouse_b &= ~(1 << (ev.xbutton.button - 1)); break;
      case ClientMessage: if ((Atom)ev.xclient.data.l[0] == wm_delete) held |= K_QUIT; break;
      case DestroyNotify: held |= K_QUIT; break;
    }
  }
}
#endif

static int present(void) {
  if (headless < 0) {
    const char *h = getenv("LINDEN_HEADLESS"), *fr = getenv("LINDEN_FRAMES");
    headless = h && *h && strcmp(h, "0");
    if (fr && *fr) frame_budget = strtoll(fr, NULL, 10);
    ppm_path = getenv("LINDEN_PPM");
    if (ppm_path && *ppm_path) atexit(at_exit); else ppm_path = NULL;
#ifndef LINDEN_NO_X11
    if (!headless && !x_open()) headless = 1;
#else
    headless = 1;
#endif
    if (headless && frame_budget < 0 && !getenv("LINDEN_KEYS"))
      fprintf(stderr, "linden: no window (headless); the game runs until it ends -- LINDEN_FRAMES=n stops it\n");
  }
  if (ppm_path && strchr(ppm_path, '%')) {
    size_t n = strlen(ppm_path) + 32; char path[n];
    snprintf(path, n, ppm_path, (int)nframes);
    write_ppm(path);
  }
  if (headless) held = scripted_keys(nframes);
#ifndef LINDEN_NO_X11
  else {
    x_present();
    static double next; const char *fps = getenv("LINDEN_FPS");
    double period = 1000.0 / (fps && atof(fps) > 0 ? atof(fps) : 60.0), t = now_ms();
    if (next == 0 || t > next + period) next = t;      /* (late: do not try to catch up) */
    next += period;
    if (next > t) usleep((useconds_t)((next - t) * 1000));
  }
#endif
  if (frame_budget >= 0 && nframes + 1 >= frame_budget) held |= K_QUIT;
  return answer();
}
#endif

/* ---------------- the calls ---------------- */
static int linden_ops(const char *fn, int argc, const int64_t *args, int64_t *out, int *outkind) {
  if (strncmp(fn, "linden_", 7)) return 0;
  if (argc < 0) return 0;                       /* (the ownership query: these calls observe the world -- not pure) */
  fn += 7;
  *outkind = 1;
  if (!strcmp(fn, "frame")) {
    if (!t_start) t_start = now_ms();
    if (!render(argc, args)) { *out = K_QUIT; return 1; }
    *out = present();
    nframes++;
    return 1;
  }
  if (!strcmp(fn, "mouse")) { *out = (int64_t)mouse_x + 65536 * (int64_t)mouse_y + ((int64_t)mouse_b << 32); return 1; }
  if (!strcmp(fn, "ticks")) { *out = t_start ? (int64_t)(now_ms() - t_start) : 0; return 1; }
  return 0;
}

LIN_PLUGIN_INIT(linden) {
  static int started;
  if (started) return;
  started = 1;
  font_init();
  lin_scalar_ops_add(linden_ops, 0);
}

/* Registered by name too (`(set_driver "linden")` finds it), though it offers calls, not a reduction strategy. */
LinDriver lin_linden_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = sizeof(Net),
  .name = "linden", .description = "Linden: a game engine (frames in, input out)",
  .caps = 0, .priority = 100, .claim = NULL, .reduce = NULL, .size = sizeof(LinDriver),
};
