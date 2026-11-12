/* spectral-norm (Computer Language Benchmarks Game), n = 1000: ten power-method steps with the matrix
   A(i,j) = 1 / ((i+j)(i+j+1)/2 + i + 1), never stored.  The answer is the norm, in billionths. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
static double a(long i, long j) { return 1.0 / (double)((i + j) * (i + j + 1) / 2 + i + 1); }
static void av(long n, const double *u, double *o) { for (long i = 0; i < n; i++) { double s = 0.0; for (long j = 0; j < n; j++) s = s + a(i, j) * u[j]; o[i] = s; } }
static void atv(long n, const double *u, double *o) { for (long i = 0; i < n; i++) { double s = 0.0; for (long j = 0; j < n; j++) s = s + a(j, i) * u[j]; o[i] = s; } }
static void atav(long n, const double *u, double *o, double *t) { av(n, u, t); atv(n, t, o); }
int main(void) {
  long n = 1000; double *u = malloc(n * sizeof *u), *v = malloc(n * sizeof *v), *t = malloc(n * sizeof *t), *w = malloc(n * sizeof *w);
  for (long i = 0; i < n; i++) u[i] = 1.0;
  /* u <- (AtA)(AtA) u, ten times; then v = AtA u */
  for (int k = 0; k < 10; k++) { atav(n, u, v, t); atav(n, v, u, t); }
  atav(n, u, w, t);
  double uv = 0.0, vv = 0.0;
  for (long i = 0; i < n; i++) { uv = uv + u[i] * w[i]; vv = vv + w[i] * w[i]; }
  printf("%ld\n", (long)floor(1000000000.0 * sqrt(uv / vv))); free(u); free(v); free(t); free(w); return 0;
}
