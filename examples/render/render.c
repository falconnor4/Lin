/* Lin window renderer helper (renderer-specific C, NOT part of the Lin engine).
   Exposes a small flat long-in/long-out ABI so a pure-Lin program can open a
   window and draw line segments via Lin's generic FFI (ccallN).  All 3D math
   lives in render.lin; this file only owns the framebuffer + SDL blit. */
#include <SDL2/SDL.h>
#include <stdlib.h>
#include <string.h>

static SDL_Window   *win;
static SDL_Renderer *ren;
static SDL_Texture  *tex;
static Uint32       *fb;      /* ARGB8888 software framebuffer */
static int           W, H;

/* 16-entry palette: Lin passes a SMALL index (Lin ints are Scott/unary, so a
   full 0xRRGGBB would be infeasibly large).  index 0 = white for edges. */
static const Uint32 pal[16] = {
  0xFFFFFF, 0xFF0000, 0x00FF00, 0x0000FF, 0xFFFF00, 0xFF00FF, 0x00FFFF,
  0x808080, 0xFF8000, 0x8000FF, 0x00FF80, 0xFF0080, 0x80FF00, 0x0080FF,
  0x4080C0, 0xC04080
};

/* open a W x H window + ARGB8888 streaming texture */
long lin_render_init(long w, long h) {
  W = (int)w; H = (int)h;
  if (SDL_Init(SDL_INIT_VIDEO) != 0) return -1;
  win = SDL_CreateWindow("lin", SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED,
                         W, H, SDL_WINDOW_SHOWN);
  if (!win) return -2;
  ren = SDL_CreateRenderer(win, -1, SDL_RENDERER_ACCELERATED);
  if (!ren) ren = SDL_CreateRenderer(win, -1, SDL_RENDERER_SOFTWARE);
  tex = SDL_CreateTexture(ren, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_STREAMING, W, H);
  fb  = calloc((size_t)W * H, sizeof(Uint32));
  return (ren && tex && fb) ? 0 : -3;
}

/* fill the whole framebuffer with palette[color] */
long lin_render_clear(long color) {
  if (!fb) return -1;
  Uint32 c = pal[color & 15] | 0xFF000000u;
  for (int i = 0; i < W * H; i++) fb[i] = c;
  return 0;
}

/* one-frame key/state poll; returns nonzero if the close (Esc) was requested */
long lin_render_quit(void) {
  if (!win) return 1;
  SDL_Event e;
  while (SDL_PollEvent(&e))
    if (e.type == SDL_QUIT) return 1;
  const Uint8 *k = SDL_GetKeyboardState(NULL);
  return k[SDL_SCANCODE_ESCAPE] ? 1 : 0;
}

/* integer Bresenham line segment into the framebuffer */
static void put(int x, int y, Uint32 c) {
  if (x >= 0 && x < W && y >= 0 && y < H) fb[y * W + x] = c;
}

long lin_render_seg(long x0, long y0, long x1, long y1, long color) {
  if (!fb) return -1;
  Uint32 c = pal[color & 15] | 0xFF000000u;
  int dx = (int)(x1 > x0 ? x1 - x0 : x0 - x1), sx = x0 < x1 ? 1 : -1;
  int dy = -((int)(y1 > y0 ? y1 - y0 : y0 - y1)), sy = y0 < y1 ? 1 : -1;
  int err = dx + dy;
  for (;;) {
    put((int)x0, (int)y0, c);
    if (x0 == x1 && y0 == y1) break;
    int e2 = 2 * err;
    if (e2 >= dy) { err += dy; x0 += sx; }
    if (e2 <= dx) { err += dx; y0 += sy; }
  }
  return 0;
}

/* upload framebuffer -> texture -> screen, present */
long lin_render_present(void) {
  if (!fb || !tex || !ren) return -1;
  void *px; int pitch;
  if (SDL_LockTexture(tex, NULL, &px, &pitch) == 0) {
    memcpy(px, fb, (size_t)W * H * sizeof(Uint32));
    SDL_UnlockTexture(tex);
  }
  SDL_RenderClear(ren);
  SDL_RenderCopy(ren, tex, NULL, NULL);
  SDL_RenderPresent(ren);
  return 0;
}

long lin_render_close(void) {
  if (fb) { free(fb); fb = NULL; }
  if (tex) SDL_DestroyTexture(tex);
  if (ren) SDL_DestroyRenderer(ren);
  if (win) SDL_DestroyWindow(win);
  SDL_Quit();
  return 0;
}

/* hold the frame for `ms` milliseconds and pump events; returns 1 if a quit
   (window close / Esc) was requested so the caller can stop animating */
long lin_render_wait(long ms) {
  SDL_Delay((Uint32)ms);
  return lin_render_quit();
}
