/* Linden — the 3D wireframe renderer, a plugin of its own.  THIS FILE DOES NOT LIVE IN std/:
 * Linden is an application's engine, not part of the standard library, and the std's job is to
 * stay small.  A program loads it from wherever it lives, by path:
 *
 *     (load_lib "./linden/linden.so")       std/ffi.lin's wrapper over dlopen(RTLD_NOW|RTLD_GLOBAL)
 *     (ccall "lin_fp_linden_window" <args>)
 *
 * The names it answers to follow the general convention stated in std/drivers/readback.c
 * (`lin_f` then how the result comes back: `s` a string value, `p` printed output).  Nothing in
 * the std knows what a mesh is; that knowledge lives here, which is the point of the division.
 *
 * THE OPERAND LIST IS THE WHOLE PROBLEM, so nothing is special-cased:
 *
 *     W H nv ne  x0 y0 z0 …  i0 j0 …  t0 dt frames
 *
 * grid, vertex count, edge count, mesh, edges, then the run.  Limits are derived from it (a C99
 * VLA and the va_list), so another mesh is another picture and a bigger grid a bigger picture.
 *
 * THREE WAYS OUT, one rasteriser:
 *   lin_fp_linden_frame   the frames as characters on stdout.
 *   lin_fp_linden_window  the frames into an X11 window, one PutImage each -- and, because a
 *                         headless check must be able to SEE the result, the last frame as a PPM.
 *   lin_fp_linden_ppm     the frames straight to a PPM, no window (the check without a display).
 *
 * WHY IT IS FAST: the reference renderer tests every cell against every edge; this rejects an edge
 * per ROW first, and renders frames concurrently -- a frame depends on no other frame, which is the
 * second architectural goal stated as code.
 */
#include "../src/lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <math.h>
#include <time.h>
#include <unistd.h>
#include <X11/Xlib.h>
#include <X11/Xutil.h>

#define LD_TILT 0.45      /* the camera's lean, not the scene's: a Y-rotation then shows three faces */

static void ld_project(int W, int H, int nv, const double *v, double t, double *px, double *py) {
  double c = cos(t), s = sin(t), ct = cos(LD_TILT), st = sin(LD_TILT);
  double sc = W * 0.82, dist = 4.0, asp = (double)H / (double)W * 2.0;
  for (int i = 0; i < nv; i++) {
    double x = v[3*i], y = v[3*i+1], z = v[3*i+2];
    double rx = x*c + z*s, rz = z*c - x*s;          /* rotate about Y by t   */
    double ry = y*ct - rz*st, rz2 = y*st + rz*ct;   /* then lean about X     */
    double d = rz2 + dist;                          /* perspective: by depth */
    px[i] = W/2.0 + sc*rx/d;
    py[i] = H/2.0 - asp*sc*ry/d;
  }
}

typedef struct { double ax, ay, dx, dy, inv_den, lo, hi; } LdEdge;

static inline void ld_prep_edges(int ne, const int *e, const double *px, const double *py, LdEdge *ep) {
  for (int k = 0; k < ne; k++) {
    double ax = px[e[2*k]], ay = py[e[2*k]], bx = px[e[2*k+1]], by = py[e[2*k+1]];
    ep[k].ax = ax; ep[k].ay = ay;
    ep[k].dx = bx - ax; ep[k].dy = by - ay;
    ep[k].lo = (ay < by ? ay : by) - 0.5;
    ep[k].hi = (ay < by ? by : ay) + 0.5;
    double den = ep[k].dx * ep[k].dx + ep[k].dy * ep[k].dy;
    ep[k].inv_den = den > 0.0 ? 1.0 / den : 0.0;
  }
}

static void ld_ascii(int W, int H, int nv, int ne, const double *v, const int *e, double t, char *out) {
  double px[nv], py[nv];
  ld_project(W, H, nv, v, t, px, py);
  LdEdge ep[ne];
  ld_prep_edges(ne, e, px, py, ep);
  for (int y = 0; y < H; y++) {
    int act[ne], nact = 0;
    for (int k = 0; k < ne; k++)
      if (y >= ep[k].lo && y <= ep[k].hi) act[nact++] = k;
    for (int x = 0; x < W; x++) {
      int hit = 0;
      for (int i = 0; i < nact; i++) {
        int k = act[i];
        double dx = ep[k].dx, dy = ep[k].dy;
        double u = ((x - ep[k].ax)*dx + (y - ep[k].ay)*dy) * ep[k].inv_den;
        if (u < 0.0 || u > 1.0) continue;
        double qx = ep[k].ax + u*dx, qy = ep[k].ay + u*dy;
        if ((x - qx)*(x - qx) + (y - qy)*(y - qy) < 0.25) { hit = 1; break; }
      }
      out[y*(W+1) + x] = hit ? '#' : '.';
    }
    out[y*(W+1) + W] = '\n';
  }
  out[(size_t)(W+1) * (size_t)H] = 0;
}

/* Greyscale into a W*H*4 buffer.  Brightness falls off from the screen centre: a depth cue that
   costs a multiply, so the form reads without a z-buffer. */
static void ld_grey(int W, int H, int nv, int ne, const double *v, const int *e, double t, unsigned char *buf) {
  double px[nv], py[nv];
  ld_project(W, H, nv, v, t, px, py);
  LdEdge ep[ne];
  ld_prep_edges(ne, e, px, py, ep);
  memset(buf, 0, (size_t)W * (size_t)H * 4);
  for (int y = 0; y < H; y++) {
    int act[ne], nact = 0;
    for (int k = 0; k < ne; k++)
      if (y >= ep[k].lo && y <= ep[k].hi) act[nact++] = k;
    for (int x = 0; x < W; x++) {
      int hit = 0;
      for (int i = 0; i < nact; i++) {
        int k = act[i];
        double dx = ep[k].dx, dy = ep[k].dy;
        double u = ((x - ep[k].ax)*dx + (y - ep[k].ay)*dy) * ep[k].inv_den;
        if (u < 0.0 || u > 1.0) continue;
        double qx = ep[k].ax + u*dx, qy = ep[k].ay + u*dy;
        if ((x - qx)*(x - qx) + (y - qy)*(y - qy) < 0.25) { hit = 1; break; }
      }
      if (!hit) continue;
      double dx = (x - W/2.0) / (W/2.0), dy = (y - H/2.0) / (H/2.0);
      double r = dx*dx + dy*dy; if (r > 1) r = 1;
      unsigned char c = (unsigned char)(255 * (1.0 - 0.7*r));
      unsigned char *p4 = buf + ((size_t)y * (size_t)W + (size_t)x) * 4;
      p4[0] = c; p4[1] = c; p4[2] = c; p4[3] = 0;
    }
  }
}

static int ld_write_ppm(const char *path, int W, int H, const unsigned char *buf) {
  FILE *f = fopen(path, "wb");
  if (!f) { fprintf(stderr, "linden: cannot write '%s'\n", path); return 0; }
  fprintf(f, "P6\n%d %d\n255\n", W, H);
  for (size_t i = 0; i < (size_t)W * (size_t)H; i++)
    fwrite(buf + i*4 + 2, 1, 1, f), fwrite(buf + i*4 + 1, 1, 1, f), fwrite(buf + i*4, 1, 1, f);
  fclose(f);
  return 1;
}

/* The operand list, read once.  Counts first, so the list states its own shape. */
#define LD_ARGS(AP)                                                                \
  int W = (int)w, H = (int)h, nv = (int)nvd, ne = (int)ned;                        \
  if (W <= 0 || H <= 0 || nv <= 0 || ne <= 0) return 0;                            \
  double vv[3*nv]; int ei[2*ne];                                                   \
  for (int i = 0; i < 3*nv; i++) vv[i] = va_arg(AP, double);                       \
  for (int i = 0; i < 2*ne; i++) ei[i] = (int)va_arg(AP, double);                  \
  double t0 = va_arg(AP, double), dt = va_arg(AP, double);                         \
  int nf = (int)va_arg(AP, double); if (nf < 1) nf = 1

/* ---- terminal: characters on stdout, one dispatch for the whole run ------------- */
int lin_fp_linden_frame(double w, double h, double nvd, double ned, ...) {
  va_list ap; va_start(ap, ned);
  LD_ARGS(ap);
  va_end(ap);
  size_t fsz = (size_t)(W+1) * (size_t)H + 1;
  char *all = malloc(fsz * (size_t)nf);
  if (!all) return 0;
#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
  for (int f = 0; f < nf; f++) ld_ascii(W, H, nv, ne, vv, ei, t0 + dt*f, all + fsz*(size_t)f);
  fwrite(all, 1, fsz*(size_t)nf, stdout);
  fflush(stdout);
  free(all);
  return nf;
}

static char *lin_fs_buf = NULL;
static size_t lin_fs_cap = 0;

char *lin_fs_linden_frame(double w, double h, double nvd, double ned, ...) {
  va_list ap; va_start(ap, ned);
  LD_ARGS(ap);
  va_end(ap);
  size_t fsz = (size_t)(W+1) * (size_t)H + 1;
  size_t total = fsz * (size_t)nf;
  if (total + 1 > lin_fs_cap) {
    char *nb = realloc(lin_fs_buf, total + 1);
    if (!nb) return "";
    lin_fs_buf = nb; lin_fs_cap = total + 1;
  }
#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
  for (int f = 0; f < nf; f++) ld_ascii(W, H, nv, ne, vv, ei, t0 + dt*f, lin_fs_buf + fsz*(size_t)f);
  lin_fs_buf[total] = 0;
  return lin_fs_buf;
}

/* ---- window: X11, one PutImage per frame, last frame dumped as a PPM -------------- */
int lin_fp_linden_window(double w, double h, double nvd, double ned, ...) {
  va_list ap; va_start(ap, ned);
  LD_ARGS(ap);
  int scale = (int)va_arg(ap, double);                 /* window pixels per grid cell */
  const char *dump = "linden-frame.ppm";               /* the last frame, for a headless look */
  va_end(ap);
  if (scale < 1) scale = 1;
  int PW = W*scale, PH = H*scale;
  unsigned char *grey = malloc((size_t)W * (size_t)H * 4);
  Display *d = XOpenDisplay(NULL);
  if (!d || !grey) { fprintf(stderr, "linden: no display (%s)\n", d ? "buffer" : "DISPLAY"); free(grey); return 0; }
  int scr = DefaultScreen(d);
  Window win = XCreateSimpleWindow(d, RootWindow(d, scr), 0, 0, (unsigned)PW, (unsigned)PH,
                                   0, BlackPixel(d, scr), BlackPixel(d, scr));
  XStoreName(d, win, "Linden - wireframe");
  XSelectInput(d, win, ExposureMask | KeyPressMask | StructureNotifyMask);
  XMapWindow(d, win);
  XFlush(d);
  XImage *img = XCreateImage(d, DefaultVisual(d, scr), 24, ZPixmap, 0, NULL,
                             (unsigned)PW, (unsigned)PH, 32, 0);
  if (!img) { XDestroyWindow(d, win); XCloseDisplay(d); free(grey); return 0; }
  GC gc = DefaultGC(d, scr);
  int shown = 0, alive = 1;
  for (int f = 0; f < nf && alive; f++) {
    ld_grey(W, H, nv, ne, vv, ei, t0 + dt*f, grey);
    for (int y = 0; y < PH; y++)                      /* nearest-neighbour upscale */
      for (int x = 0; x < PW; x++) {
        const unsigned char *s = grey + ((size_t)(y/scale) * W + (size_t)(x/scale)) * 4;
        unsigned char *t = (unsigned char *)img->data + ((size_t)y * (size_t)PW + (size_t)x) * 4;
        t[0] = s[0]; t[1] = s[1]; t[2] = s[2]; t[3] = 0;
      }
    XPutImage(d, win, gc, img, 0, 0, 0, 0, (unsigned)PW, (unsigned)PH);
    XFlush(d);
    shown = f + 1;
    while (XPending(d)) {                             /* a key or a close ends it early */
      XEvent ev; XNextEvent(d, &ev);
      if (ev.type == KeyPress || ev.type == DestroyNotify) alive = 0;
      if (ev.type == ClientMessage) alive = 0;
    }
    struct timespec ts = {0, 33 * 1000 * 1000};
    nanosleep(&ts, NULL);
  }
  if (dump && dump[0]) ld_write_ppm(dump, W, H, grey);
  XDestroyImage(img);
  XDestroyWindow(d, win);
  XCloseDisplay(d);
  free(grey);
  return shown;
}

/* ---- no window at all: the same frames to a PPM (the headless check) -------------- */
int lin_fp_linden_ppm(double w, double h, double nvd, double ned, ...) {
  va_list ap; va_start(ap, ned);
  LD_ARGS(ap);
  double at = va_arg(ap, double);                      /* which frame to dump */
  const char *dump = "linden-frame.ppm";
  va_end(ap);
  unsigned char *grey = malloc((size_t)W * (size_t)H * 4);
  if (!grey) return 0;
  ld_grey(W, H, nv, ne, vv, ei, at, grey);
  int ok = (dump && dump[0]) ? ld_write_ppm(dump, W, H, grey) : 0;
  free(grey);
  return ok;
}

/* Registration: kept so a future, proper loader can take this plugin by NAME too, not only by
   path.  It offers calls, not a reduction strategy, so it claims no tags and registers nothing. */
LinDriver lin_linden_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = sizeof(Net),
  .name = "linden", .description = "Linden wireframe renderer: a mesh in, frames out",
  .caps = 0, .priority = 100, .claim = NULL, .reduce = NULL, .size = sizeof(LinDriver),
};
