#include "../../src/lin.h"
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <math.h>

/* ---------------------------------------------------------------------- *
 *  Native scalar arithmetic & comparison driver (goal 3).
 *
 *  Holds ALL pure integer/float arithmetic + comparison builtins that used to
 *  live in the core's `run_ffi` (`lin_add`, `lin_sub`, `lin_mul`, `lin_div`,
 *  `lin_mod`, `lin_pow`, `lin_eq`..`lin_geq`, `lin_ffloor`, every `lin_f*`
 *  float op, `lin_lerp`, `lin_fclamp`).  The core delegates to us through the
 *  `lin_arith_register` hook (see src/io.c), so base-engine folding, readback,
 *  and the composed/head-fold paths all resolve arithmetic through one
 *  plugin authority without the core reimplementing math.
 *
 *  Non-movable C stays in the core (memory/device/OS, float parsing, string
 *  compare, fold accounting).  We are also a claimable wavefront driver of
 *  the native-num class, so `(driver_add "arith")` / `(set_driver "arith")`
 *  lets arithmetic fold directly in the reducer pipeline too.  Whatever row we
 *  own is authoritative in both paths.
 * ---------------------------------------------------------------------- */

/* eval(fn, argc, args, out, outkind): pure scalar int/bool/float evaluator.
 * outkind: 1=int, 3=bool (out=0/1), 4=float (out = IEEE-754 bits).  Returns 1
 * if `fn` is one of our arithmetic/comparison rows, else 0 (declined). */
static int arith_eval(const char *fn, int argc, const long *a, long *out, int *outkind) {
  *outkind = 0;
  if (!fn) return 0;

  /* float binary ops: args are IEEE-754 bits carried as longs; result float */
  if      (fn[0]=='l' && fn[1]=='i' && fn[2]=='n' && !strncmp(fn, "lin_fadd", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x+y; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fsub", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x-y; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fmul", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x*y; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fdiv", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=y!=0.0?x/y:0.0; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fpow", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=pow(x,y); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fatan2", 10)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=atan2(x,y); memcpy(out,&r,8); *outkind=4; return 1; }
  /* float binary min/max */
  else if (!strncmp(fn, "lin_fmin", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x<y?x:y; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fmax", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x>y?x:y; memcpy(out,&r,8); *outkind=4; return 1; }
  /* float unary ops -> float */
  else if (!strncmp(fn, "lin_fsqrt", 9)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=x>=0.0?sqrt(x):0.0; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fsin", 8)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=sin(x); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fcos", 8)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=cos(x); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_ftan", 8)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=tan(x); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fabs", 8)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=fabs(x); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fsign", 9)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=x>=0.0?1.0:-1.0; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_ffract", 10)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=x-floor(x); memcpy(out,&r,8); *outkind=4; return 1; }
  /* float comparisons -> Church bool */
  else if (!strncmp(fn, "lin_feq", 7)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); *out=x==y; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_flt", 7)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); *out=x<y;  *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_fleq", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); *out=x<=y; *outkind=3; return 1; }
  /* float -> int / 3-arg float combinators */
  if (!strncmp(fn, "lin_ffloor", 10)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); *out=(long)floor(x); *outkind=1; return 1; }
  if (!strncmp(fn, "lin_fmin", 8) || !strncmp(fn, "lin_fmax", 8)) { /* handled above */ }
  if (!strncmp(fn, "lin_lerp", 8) && argc >= 3) { double x,y,t; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); memcpy(&t,&a[2],8); double r=x+(y-x)*t; memcpy(out,&r,8); *outkind=4; return 1; }
  if (!strncmp(fn, "lin_fclamp", 10) && argc >= 3) { double x,lo,hi; memcpy(&x,&a[0],8); memcpy(&lo,&a[1],8); memcpy(&hi,&a[2],8); double r=x<lo?lo:(x>hi?hi:x); memcpy(out,&r,8); *outkind=4; return 1; }

  /* integer arithmetic / comparisons */
  if (argc < 2) return 0;                       /* every int op needs 2 args */
  if      (!strncmp(fn, "lin_add", 7)) *out = a[0] + a[1];
  else if (!strncmp(fn, "lin_sub", 7)) *out = a[0] >= a[1] ? a[0] - a[1] : 0;
  else if (!strncmp(fn, "lin_mul", 7)) *out = a[0] * a[1];
  else if (!strncmp(fn, "lin_div", 7)) *out = a[1] ? a[0] / a[1] : 0;
  else if (!strncmp(fn, "lin_mod", 7)) *out = a[1] ? a[0] % a[1] : 0;
  else if (!strncmp(fn, "lin_pow", 7)) { long b=a[0], e=a[1], r=1; while (e>0) { if (e&1) r*=b; b*=b; e>>=1; } *out=r; }
  else if (!strncmp(fn, "lin_eq", 6)) { *out = a[0] == a[1]; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_lt", 6)) { *out = a[0] <  a[1]; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_leq", 7)) { *out = a[0] <= a[1]; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_gt", 6)) { *out = a[0] >  a[1]; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_geq", 7)) { *out = a[0] >= a[1]; *outkind=3; return 1; }
  else return 0;
  *outkind = 1;
  return 1;
}

/* ---- optional wavefront driver ----
   The run_ffi hook above is the primary (and only required) mechanism: the
   base engine's lin_fold_ffi/readback calls run_ffi, which delegates here.
   We also export a LinDriver so `(driver_add "arith")` is accepted, but claim
   is a no-op (we deliberately do NOT steal redexes from the base engine's
   fold/deferral, which already routes arithmetic here through the hook). */
static int arith_claim(const Net *n, Port p1, Port p2) { (void)n; (void)p1; (void)p2; return 0; }
static int arith_reduce(Net *n, Port *redexes, int nred, long limit, int *changed) { (void)redexes;(void)limit;(void)changed; return 0; (void)nred; }

/* ---- registration ---- */
static void __attribute__((constructor)) arith_load(void) {
  lin_arith_register(arith_eval);
}

LinDriver lin_arith_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI,
  .name = "arith", .description = "native scalar integer/float arithmetic (run_ffi hook + claimable driver)",
  .caps = LIN_CAP_NATIVE_NUM, .priority = 20,
  .claim = arith_claim, .reduce = arith_reduce,
};