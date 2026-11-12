/* n-body (Computer Language Benchmarks Game): the Sun and the four giant planets, 200,000 steps of 0.01 days.
   Each body is pulled by every other; the answer is the system's energy afterwards, in billionths. */
#include <stdio.h>
#include <math.h>
#define N 5
typedef struct { double x, y, z, vx, vy, vz, m; } B;
static const double SM = 39.47841760435743, DP = 365.24;
int main(void) {
  B b[N] = {
    {0, 0, 0, 0, 0, 0, SM},
    {4.84143144246472090, -1.16032004402742839, -0.103622044471123109, 0.00166007664274403694 * DP, 0.00769901118419740425 * DP, -0.0000690460016972063023 * DP, 0.000954791938424326609 * SM},
    {8.34336671824457987, 4.12479856412430479, -0.403523417114321381, -0.00276742510726862411 * DP, 0.00499852801234917238 * DP, 0.0000230417297573763929 * DP, 0.000285885980666130812 * SM},
    {12.8943695621391310, -15.1111514016986312, -0.223307578892655734, 0.00296460137564761618 * DP, 0.00237847173959480950 * DP, -0.0000296589568540237556 * DP, 0.0000436624404335156298 * SM},
    {15.3796971148509165, -25.9193146099879641, 0.179258772950371181, 0.00268067772490389322 * DP, 0.00162824170038242295 * DP, -0.0000951592254519715870 * DP, 0.0000515138902046611451 * SM}};
  double dt = 0.01;
  for (int s = 0; s < 200000; s++) {
    B nb[N];
    for (int i = 0; i < N; i++) {
      B c = b[i];
      for (int j = 0; j < N; j++) {
        double dx = c.x - b[j].x, dy = c.y - b[j].y, dz = c.z - b[j].z, d2 = dx * dx + dy * dy + dz * dz;
        if (d2 == 0.0) continue;
        double mag = dt / (d2 * sqrt(d2)), k = b[j].m * mag;
        c.vx -= dx * k; c.vy -= dy * k; c.vz -= dz * k;
      }
      c.x += dt * c.vx; c.y += dt * c.vy; c.z += dt * c.vz;
      nb[i] = c;
    }
    for (int i = 0; i < N; i++) b[i] = nb[i];
  }
  double e = 0.0;
  for (int i = 0; i < N; i++) {
    double p = 0.0;
    for (int j = 0; j < N; j++) {
      double dx = b[i].x - b[j].x, dy = b[i].y - b[j].y, dz = b[i].z - b[j].z, d2 = dx * dx + dy * dy + dz * dz;
      if (d2 != 0.0) p = p + b[i].m * b[j].m / sqrt(d2);
    }
    e = e + 0.5 * b[i].m * (b[i].vx * b[i].vx + b[i].vy * b[i].vy + b[i].vz * b[i].vz) - 0.5 * p;
  }
  printf("%ld\n", (long)floor(1000000000.0 * e)); return 0;
}
