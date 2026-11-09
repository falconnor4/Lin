/* ============================================================================
 * i64.h -- THE integer semantics, stated once.
 *
 * Lin's integers are 64-bit two's complement, wrapping, exactly int64_t with the
 * undefined cases defined: overflow wraps, x / 0 = x % 0 = 0, INT64_MIN / -1 wraps,
 * pow with a negative exponent is 0.  The net's own arithmetic (std/num.lin, pure
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
    while (e > 0) { if (e & 1) r = lin_i64_mul(r, b); b = lin_i64_mul(b, b); e >>= 1; } return r; }
LIN_I64_DEFS
#define LIN_I64_STR2(...) #__VA_ARGS__
#define LIN_I64_STR(x) LIN_I64_STR2(x)
/* the same definitions as C source, for a driver that compiles code */
#define LIN_I64_SRC LIN_I64_STR(LIN_I64_DEFS) "\n"
#endif
