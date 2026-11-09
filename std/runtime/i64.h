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
#define LIN_I64_DEFS \
  static inline long lin_i64_add(long a, long b) { return (long)((unsigned long)a + (unsigned long)b); } \
  static inline long lin_i64_sub(long a, long b) { return (long)((unsigned long)a - (unsigned long)b); } \
  static inline long lin_i64_mul(long a, long b) { return (long)((unsigned long)a * (unsigned long)b); } \
  static inline long lin_i64_div(long a, long b) { return b == 0 ? 0 : (b == -1 ? lin_i64_sub(0, a) : a / b); } \
  static inline long lin_i64_mod(long a, long b) { return (b == 0 || b == -1) ? 0 : a % b; } \
  static inline long lin_i64_pow(long b, long e) { long r = 1; if (e < 0) return (b == 1) ? 1 : (b == -1 ? ((e & 1) ? -1 : 1) : 0); \
    while (e > 0) { if (e & 1) r = lin_i64_mul(r, b); b = lin_i64_mul(b, b); e >>= 1; } return r; } \
  static inline long lin_i64_band(long a, long b) { return a & b; } \
  static inline long lin_i64_bor(long a, long b) { return a | b; } \
  static inline long lin_i64_bxor(long a, long b) { return a ^ b; } \
  static inline long lin_i64_shl(long a, long k) { return (k < 0 || k >= (long)(sizeof(long) * 8)) ? 0 : (long)((unsigned long)a << k); } \
  static inline long lin_i64_shr(long a, long k) { return k < 0 ? 0 : (k >= (long)(sizeof(long) * 8) ? (a < 0 ? -1 : 0) : (a >> k)); }
LIN_I64_DEFS
/* FLOATS: IEEE-754 doubles carried as their 64-bit patterns (a float travels in a `long` like every value), with
   the undefined cases defined: x / 0.0 = 0.0, sqrt of a negative = 0.0, floor gives an INTEGER.  (Needs <math.h>.) */
#define LIN_F64_DEFS \
  static inline double lin_d(long x) { double d; __builtin_memcpy(&d, &x, 8); return d; } \
  static inline long lin_l(double d) { long x; __builtin_memcpy(&x, &d, 8); return x; } \
  static inline long lin_f64_add(long a, long b) { return lin_l(lin_d(a) + lin_d(b)); } \
  static inline long lin_f64_sub(long a, long b) { return lin_l(lin_d(a) - lin_d(b)); } \
  static inline long lin_f64_mul(long a, long b) { return lin_l(lin_d(a) * lin_d(b)); } \
  static inline long lin_f64_div(long a, long b) { return lin_l(lin_d(b) != 0.0 ? lin_d(a) / lin_d(b) : 0.0); } \
  static inline long lin_f64_pow(long a, long b) { return lin_l(pow(lin_d(a), lin_d(b))); } \
  static inline long lin_f64_atan2(long a, long b) { return lin_l(atan2(lin_d(a), lin_d(b))); } \
  static inline long lin_f64_min(long a, long b) { return lin_d(a) < lin_d(b) ? a : b; } \
  static inline long lin_f64_max(long a, long b) { return lin_d(a) > lin_d(b) ? a : b; } \
  static inline long lin_f64_sqrt(long a) { return lin_l(lin_d(a) >= 0.0 ? sqrt(lin_d(a)) : 0.0); } \
  static inline long lin_f64_sin(long a) { return lin_l(sin(lin_d(a))); } \
  static inline long lin_f64_cos(long a) { return lin_l(cos(lin_d(a))); } \
  static inline long lin_f64_tan(long a) { return lin_l(tan(lin_d(a))); } \
  static inline long lin_f64_abs(long a) { return lin_l(fabs(lin_d(a))); } \
  static inline long lin_f64_sign(long a) { return lin_l(lin_d(a) >= 0.0 ? 1.0 : -1.0); } \
  static inline long lin_f64_fract(long a) { return lin_l(lin_d(a) - floor(lin_d(a))); } \
  static inline long lin_f64_eq(long a, long b) { return lin_d(a) == lin_d(b); } \
  static inline long lin_f64_lt(long a, long b) { return lin_d(a) < lin_d(b); } \
  static inline long lin_f64_leq(long a, long b) { return lin_d(a) <= lin_d(b); } \
  static inline long lin_f64_floor(long a) { return (long)floor(lin_d(a)); } \
  static inline long lin_f64_of_int(long i) { return lin_l((double)i); }
#ifdef LIN_WANT_F64
LIN_F64_DEFS
#endif
#define LIN_I64_STR2(...) #__VA_ARGS__
#define LIN_I64_STR(x) LIN_I64_STR2(x)
/* the same definitions as C source, for a driver that compiles code */
#define LIN_I64_SRC LIN_I64_STR(LIN_I64_DEFS) "\n"
#define LIN_F64_SRC "#include <math.h>\n" LIN_I64_STR(LIN_F64_DEFS) "\n"
#endif
