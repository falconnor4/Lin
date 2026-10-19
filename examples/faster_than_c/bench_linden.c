/* ==============================================================================
 * Benchmark 3: Linden 3D Wireframe Rendering Engine
 * OpenMP C Reference (compiled with -O3 -fopenmp).
 *
 * Parallel wireframe rasterizer rendering 65,536 frames of a rotating cube
 * on a 32x16 grid with edge precomputation and row-rejection.
 * ============================================================================== */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <omp.h>

#define W 32
#define H 16

static double V[8][3] = {
  {-1,-1,-1}, {1,-1,-1}, {-1,1,-1}, {1,1,-1},
  {-1,-1,1},  {1,-1,1},  {-1,1,1},  {1,1,1}
};

static int E[12][2] = {
  {0,1}, {0,2}, {1,3}, {2,3}, {4,5}, {4,6},
  {5,7}, {6,7}, {0,4}, {1,5}, {2,6}, {3,7}
};

static void frame(double t, char *out) {
  double px[8], py[8];
  double c = cos(t), s = sin(t), ct = cos(0.45), st = sin(0.45);
  double sc = W * 0.82, asp = (double)H / W * 2.0;

  for (int i = 0; i < 8; i++) {
    double x = V[i][0], y = V[i][1], z = V[i][2];
    double rx = x*c + z*s, rz = z*c - x*s;
    double ry = y*ct - rz*st, rz2 = y*st + rz*ct, d = rz2 + 4.0;
    px[i] = W/2.0 + sc*rx/d;
    py[i] = H/2.0 - asp*sc*ry/d;
  }

  for (int y = 0; y < H; y++) {
    for (int x = 0; x < W; x++) {
      int hit = 0;
      for (int k = 0; k < 12 && !hit; k++) {
        double ax = px[E[k][0]], ay = py[E[k][0]], bx = px[E[k][1]], by = py[E[k][1]];
        double lo = ay < by ? ay : by, hi = ay < by ? by : ay;
        if (y < lo - 0.5 || y > hi + 0.5) continue;
        double dx = bx - ax, dy = by - ay, den = dx*dx + dy*dy;
        double u = den > 0.0 ? ((x - ax)*dx + (y - ay)*dy) / den : 0.0;
        if (u < 0.0 || u > 1.0) continue;
        double qx = ax + u*dx, qy = ay + u*dy;
        if ((x - qx)*(x - qx) + (y - qy)*(y - qy) < 0.25) hit = 1;
      }
      out[y*(W+1) + x] = hit ? '#' : '.';
    }
    out[y*(W+1) + W] = '\n';
  }
  out[(size_t)(W+1)*H] = 0;
}

int main(void) {
  int N = 65536;
  size_t fsz = (size_t)(W+1)*H + 1;
  char *all = malloc(fsz * (size_t)N);

  struct timespec start, end;
  clock_gettime(CLOCK_MONOTONIC, &start);

#pragma omp parallel for schedule(static)
  for (int f = 0; f < N; f++) {
    frame(0.3 * f, all + fsz * (size_t)f);
  }

  clock_gettime(CLOCK_MONOTONIC, &end);
  double elapsed = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;

  printf("[C -O3 + OpenMP] %d frames in %.4f s (%.4f ms/frame)\n",
         N, elapsed, elapsed * 1000.0 / N);

  free(all);
  return 0;
}
