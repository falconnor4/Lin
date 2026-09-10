/* Lin framebuffer output primitive (general-purpose pixel output, like
   io_putchar but 2D).  Exposes a flat long-in/long-out ABI: Lin computes every
   pixel in Lin and calls lin_fb_plot; this file only owns the SDL window,
   a software framebuffer, and the texture blit.  No geometry, no shading, no
   rasterization here — that is all Lin (see render.lin). */
#include <SDL2/SDL.h>
#include <stdlib.h>
#include <string.h>

static SDL_Window   *win;
static SDL_Renderer *ren;
static SDL_Texture  *tex;
static Uint32       *fb;      /* ARGB8888 software framebuffer */
static int           W, H;

/* open a W x H window + ARGB8888 streaming texture; 0 on success */
long lin_fb_open(long w, long h) {
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

/* set one pixel to palette[color] (color 0..15, so Lin passes small Scott ints) */
long lin_fb_plot(long x, long y, long color) {
  static const Uint32 pal[16] = {
    0xFFFFFF, 0xFF0000, 0x00FF00, 0x0000FF, 0xFFFF00, 0xFF00FF, 0x00FFFF,
    0x808080, 0xFF8000, 0x8000FF, 0x00FF80, 0xFF0080, 0x80FF00, 0x0080FF,
    0x4080C0, 0xC04080
  };
  if (!fb) return -1;
  if (x >= 0 && x < W && y >= 0 && y < H) fb[y * W + x] = pal[color & 15] | 0xFF000000u;
  return 0;
}

/* upload framebuffer -> texture -> screen */
long lin_fb_present(void) {
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

/* pump events, return 1 if quit (Esc / window close) requested */
long lin_fb_quit(void) {
  if (!win) return 1;
  SDL_Event e;
  while (SDL_PollEvent(&e))
    if (e.type == SDL_QUIT) return 1;
  const Uint8 *k = SDL_GetKeyboardState(NULL);
  return k[SDL_SCANCODE_ESCAPE] ? 1 : 0;
}

long lin_fb_close(void) {
  if (fb) { free(fb); fb = NULL; }
  if (tex) SDL_DestroyTexture(tex);
  if (ren) SDL_DestroyRenderer(ren);
  if (win) SDL_DestroyWindow(win);
  SDL_Quit();
  return 0;
}