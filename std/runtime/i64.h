/* ============================================================================
 * i64.h -- THE integer semantics, stated once.
 *
 * Lin's integers are 64-bit two's complement, wrapping, exactly int64_t with the
 * undefined cases defined: overflow wraps, x / 0 = x % 0 = 0, INT64_MIN / -1 wraps,
 * pow with a negative exponent is 0, a shift by a negative count is 0, shl past the width
 * is 0 and shr past it is the sign (shr is arithmetic).  The net's own arithmetic (std/num.lin, pure
 * Lin over bit chains) computes the same function; every driver that folds integer
 * arithmetic -- arith's table, native's compiled cones, simd -- uses THESE lines, and
 * native compiles their text (LIN_I64_SRC), so no two paths can disagree.
 * ==========================================================================*/
#ifndef LIN_I64_H
#define LIN_I64_H
#include <stdint.h>
#define LIN_I64_DEFS \
  static inline int64_t lin_i64_add(int64_t a, int64_t b) { return (int64_t)((uint64_t)a + (uint64_t)b); } \
  static inline int64_t lin_i64_sub(int64_t a, int64_t b) { return (int64_t)((uint64_t)a - (uint64_t)b); } \
  static inline int64_t lin_i64_mul(int64_t a, int64_t b) { return (int64_t)((uint64_t)a * (uint64_t)b); } \
  static inline int64_t lin_i64_div(int64_t a, int64_t b) { return b == 0 ? 0 : (b == -1 ? lin_i64_sub(0, a) : a / b); } \
  static inline int64_t lin_i64_mod(int64_t a, int64_t b) { return (b == 0 || b == -1) ? 0 : a % b; } \
  static inline int64_t lin_i64_pow(int64_t b, int64_t e) { int64_t r = 1; if (e < 0) return (b == 1) ? 1 : (b == -1 ? ((e & 1) ? -1 : 1) : 0); \
    while (e > 0) { if (e & 1) r = lin_i64_mul(r, b); b = lin_i64_mul(b, b); e >>= 1; } return r; } \
  static inline int64_t lin_i64_band(int64_t a, int64_t b) { return a & b; } \
  static inline int64_t lin_i64_bor(int64_t a, int64_t b) { return a | b; } \
  static inline int64_t lin_i64_bxor(int64_t a, int64_t b) { return a ^ b; } \
  static inline int64_t lin_i64_shl(int64_t a, int64_t k) { return (k < 0 || k >= (int64_t)(sizeof(int64_t) * 8)) ? 0 : (int64_t)((uint64_t)a << k); } \
  static inline int64_t lin_i64_shr(int64_t a, int64_t k) { return k < 0 ? 0 : (k >= (int64_t)(sizeof(int64_t) * 8) ? (a < 0 ? -1 : 0) : (a >> k)); }
LIN_I64_DEFS
/* FLOATS: IEEE-754 doubles carried as their 64-bit patterns (a float travels in an `int64_t` like every value), with
   the undefined cases defined: x / 0.0 = 0.0, sqrt of a negative = 0.0, floor gives an INTEGER.  (Needs <math.h>.)
   SINE AND COSINE are computed here, not by the C library: every target computes them with these operations in this
   order -- the GPU's kernels too (std/drivers/fn.c, THE GPU), whose text is this one in GLSL -- so a float is the
   same bits wherever it was computed.  (A quadrant reduction by pi/2 in three parts and fdlibm's kernels: within an
   ulp or two of the true value for |x| up to about a million; past 1e15, where no bit of the angle is left, 0 and 1.) */
#define LIN_F64_DEFS \
  static inline double lin_d(int64_t x) { double d; __builtin_memcpy(&d, &x, 8); return d; } \
  static inline int64_t lin_l(double d) { int64_t x; __builtin_memcpy(&x, &d, 8); return x; } \
  static inline int64_t lin_f64_add(int64_t a, int64_t b) { return lin_l(lin_d(a) + lin_d(b)); } \
  static inline int64_t lin_f64_sub(int64_t a, int64_t b) { return lin_l(lin_d(a) - lin_d(b)); } \
  static inline int64_t lin_f64_mul(int64_t a, int64_t b) { return lin_l(lin_d(a) * lin_d(b)); } \
  static inline int64_t lin_f64_div(int64_t a, int64_t b) { return lin_l(lin_d(b) != 0.0 ? lin_d(a) / lin_d(b) : 0.0); } \
  static inline int64_t lin_f64_pow(int64_t a, int64_t b) { return lin_l(pow(lin_d(a), lin_d(b))); } \
  static inline int64_t lin_f64_atan2(int64_t a, int64_t b) { return lin_l(atan2(lin_d(a), lin_d(b))); } \
  static inline int64_t lin_f64_min(int64_t a, int64_t b) { return lin_d(a) < lin_d(b) ? a : b; } \
  static inline int64_t lin_f64_max(int64_t a, int64_t b) { return lin_d(a) > lin_d(b) ? a : b; } \
  static inline int64_t lin_f64_sqrt(int64_t a) { return lin_l(lin_d(a) >= 0.0 ? sqrt(lin_d(a)) : 0.0); } \
  static inline double lin_trig(double x, int64_t c) { \
    if (!(fabs(x) <= 1e15)) return c ? (x - x) + 1.0 : x - x; \
    double n = floor(x * 6.36619772367581382433e-01 + 0.5); \
    double r = ((x - n * 1.57079632673412561417e+00) - n * 6.07710050630396597660e-11) - n * 2.02226624871116645580e-21; \
    int64_t q = ((int64_t)n + c) & 3; double z = r * r; \
    double s = r + r * z * (-1.66666666666666324348e-01 + z * (8.33333333332248946124e-03 + z * (-1.98412698298579493134e-04 + z * (2.75573137070700676789e-06 + z * (-2.50507602534068634195e-08 + z * 1.58969099521155010221e-10))))); \
    double k = (1.0 - 0.5 * z) + z * z * (4.16666666666666019037e-02 + z * (-1.38888888888741095749e-03 + z * (2.48015872894767294178e-05 + z * (-2.75573143513906633035e-07 + z * (2.08757232129817482790e-09 + z * -1.13596475577881948265e-11))))); \
    return q == 0 ? s : q == 1 ? k : q == 2 ? -s : -k; } \
  static inline int64_t lin_f64_sin(int64_t a) { return lin_l(lin_trig(lin_d(a), 0)); } \
  static inline int64_t lin_f64_cos(int64_t a) { return lin_l(lin_trig(lin_d(a), 1)); } \
  static inline int64_t lin_f64_tan(int64_t a) { return lin_l(tan(lin_d(a))); } \
  static inline int64_t lin_f64_abs(int64_t a) { return lin_l(fabs(lin_d(a))); } \
  static inline int64_t lin_f64_sign(int64_t a) { return lin_l(lin_d(a) >= 0.0 ? 1.0 : -1.0); } \
  static inline int64_t lin_f64_fract(int64_t a) { return lin_l(lin_d(a) - floor(lin_d(a))); } \
  static inline int64_t lin_f64_eq(int64_t a, int64_t b) { return lin_d(a) == lin_d(b); } \
  static inline int64_t lin_f64_lt(int64_t a, int64_t b) { return lin_d(a) < lin_d(b); } \
  static inline int64_t lin_f64_leq(int64_t a, int64_t b) { return lin_d(a) <= lin_d(b); } \
  static inline int64_t lin_f64_floor(int64_t a) { double f = floor(lin_d(a)); return (f != f || f >= 9223372036854775808.0 || f < -9223372036854775808.0) ? (-9223372036854775807L - 1) : (int64_t)f; } \
  static inline int64_t lin_f64_floorf(int64_t a) { return lin_l(floor(lin_d(a))); } \
  static inline int64_t lin_f64_of_int(int64_t i) { return lin_l((double)i); }
#ifdef LIN_WANT_F64
LIN_F64_DEFS
#endif
#define LIN_I64_STR2(...) #__VA_ARGS__
#define LIN_I64_STR(x) LIN_I64_STR2(x)
/* the same definitions as C source, for a driver that compiles code */
#define LIN_I64_SRC "#include <stdint.h>\n#include <inttypes.h>\n" LIN_I64_STR(LIN_I64_DEFS) "\n"
#define LIN_F64_SRC "#include <math.h>\n" LIN_I64_STR(LIN_F64_DEFS) "\n"
#endif
