/* pidigits (Computer Language Benchmarks Game): the first 2,000 digits of pi by Gibbons' unbounded spigot, on
   arbitrary-precision numbers written here (base 10^9 limbs, least significant first) -- the same operations
   the Lin program's library provides.  The accumulator is signed: it goes below zero after a digit is taken out.
   The answer is a checksum of every digit with its position. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { long *d; long n, cap; } Big;
enum { BASE = 1000000000 };
static void reserve(Big *a, long n) { if (n > a->cap) { a->cap = n * 2; a->d = realloc(a->d, (size_t)a->cap * sizeof(long)); } }
static void trim(Big *a) { while (a->n > 0 && a->d[a->n - 1] == 0) a->n--; }
static void set(Big *a, long v) { a->n = 0; reserve(a, 3); while (v) { a->d[a->n++] = v % BASE; v /= BASE; } }
static void copy(Big *r, const Big *a) { reserve(r, a->n); memcpy(r->d, a->d, (size_t)a->n * sizeof(long)); r->n = a->n; }
static void mul_small(Big *r, const Big *a, long k) {   /* r may be a */
  reserve(r, a->n + 2); long c = 0, n = a->n;
  for (long i = 0; i < n; i++) { long p = a->d[i] * k + c; r->d[i] = p % BASE; c = p / BASE; }
  r->n = n; while (c) { r->d[r->n++] = c % BASE; c /= BASE; } trim(r);
}
static void add(Big *r, const Big *a, const Big *b) {   /* r may be a or b */
  long n = a->n > b->n ? a->n : b->n; reserve(r, n + 1); long c = 0;
  for (long i = 0; i < n; i++) { long s = (i < a->n ? a->d[i] : 0) + (i < b->n ? b->d[i] : 0) + c; c = s >= BASE; r->d[i] = c ? s - BASE : s; }
  r->n = n; if (c) r->d[r->n++] = 1;
}
static void sub(Big *r, const Big *a, const Big *b) {   /* a >= b; r may be a */
  reserve(r, a->n); long c = 0;
  for (long i = 0; i < a->n; i++) { long d = a->d[i] - (i < b->n ? b->d[i] : 0) - c; c = d < 0; r->d[i] = c ? d + BASE : d; }
  r->n = a->n; trim(r);
}
static int cmp(const Big *a, const Big *b) {
  if (a->n != b->n) return a->n < b->n ? -1 : 1;
  for (long i = a->n - 1; i >= 0; i--) if (a->d[i] != b->d[i]) return a->d[i] < b->d[i] ? -1 : 1;
  return 0;
}
typedef struct { Big m; int neg; } Int;   /* a sign and a magnitude */
static Big t1, t2, t3;
static void iadd(Int *r, const Big *b) {     /* r += b, b >= 0 */
  if (!r->neg) { add(&r->m, &r->m, b); return; }
  if (cmp(&r->m, b) > 0) { sub(&r->m, &r->m, b); return; }
  copy(&t3, b); sub(&t3, &t3, &r->m); copy(&r->m, &t3); r->neg = 0;
}
static void isub(Int *r, const Big *b) {     /* r -= b, b >= 0 */
  if (r->neg) { add(&r->m, &r->m, b); return; }
  if (cmp(&r->m, b) >= 0) { sub(&r->m, &r->m, b); return; }
  copy(&t3, b); sub(&t3, &t3, &r->m); copy(&r->m, &t3); r->neg = 1;
}
static long extract(const Big *nu, const Int *ac, const Big *de, long nth) {   /* numer <= accum: the sum is positive */
  mul_small(&t1, nu, nth); if (ac->neg) sub(&t1, &t1, &ac->m); else add(&t1, &t1, &ac->m);
  long q = 0; t2.n = 0;
  for (;;) { add(&t2, &t2, de); if (cmp(&t2, &t1) > 0) return q; q++; }
}
int main(void) {
  Big nu = {0}, de = {0}, t = {0}; Int ac = {{0}, 0}; set(&nu, 1); set(&ac.m, 0); set(&de, 1);
  long n = 2000, sum = 0;
  for (long i = 0, k = 1; i < n; k++) {
    long k2 = k * 2 + 1;
    mul_small(&t, &nu, 2); iadd(&ac, &t); mul_small(&ac.m, &ac.m, k2); mul_small(&de, &de, k2); mul_small(&nu, &nu, k);
    if (ac.neg || cmp(&nu, &ac.m) > 0) continue;
    long d = extract(&nu, &ac, &de, 3);
    if (d != extract(&nu, &ac, &de, 4)) continue;
    sum += d * (i % 97 + 1); i++;
    mul_small(&t, &de, d); isub(&ac, &t); mul_small(&ac.m, &ac.m, 10); if (!ac.m.n) ac.neg = 0; mul_small(&nu, &nu, 10);
  }
  printf("%ld\n", sum); return 0;
}
