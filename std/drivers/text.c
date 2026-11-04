/* std/drivers/text.c -- the TEXT domain: O(1) access to a source string.
   ---------------------------------------------------------------------------
   A Lin string is a cons chain, so reading the n-th character of source is n reductions, and a
   front end written in Lin then costs a net's worth of firing per character (measured: 0.28 s per
   character on the bootstrap reader).  Nothing about that is a property of the LANGUAGE: a string
   already has a C form wherever it is interned, and indexing it is what strcspn does.

   These rows are that: the SOURCE is a string, the indices are numbers, and every result is a
   number except `lin_tsub` (named with the `ts` prefix, which is how readback learns its result is
   a string as well).  They are pure functions of their operands -- no state, no effect -- so a
   build may fold them, exactly like `add`.

   Loaded by std/drivers/text.lin: `(set_driver "text")` dlopens this plugin, and the symbols below
   become reachable through `ccall` like any other FFI row. */
#include <stdint.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include "../../src/lin.h"

long lin_tlen(const char *s) { return s ? (long)strlen(s) : 0; }

/* The byte at `i`, or -1 past the end: past-the-end is how every caller here spells "no more". */
long lin_tget(const char *s, long i) {
  if (!s || i < 0) return -1;
  size_t n = strlen(s);
  return (size_t)i < n ? (long)(unsigned char)s[i] : -1;
}

/* First `ch` at or after `i`.  NOT FOUND IS THE END OF THE TEXT, not -1: every caller wants to
   continue THERE, and a -1 would have to be compared before it could be used. */
long lin_tfind(const char *s, long i, long ch) {
  if (!s || i < 0 || ch < 0 || ch > (long)UCHAR_MAX) return 0;
  size_t n = strlen(s);
  if ((size_t)i >= n) return (long)n;
  const char *p = strchr(s + i, (int)ch);
  return p ? (long)(p - s) : (long)n;
}

/* First byte at or after `i` that is in `stops`, i.e. strcspn: one call finds the end of a token. */
long lin_tfindany(const char *s, long i, const char *stops) {
  if (!s || !stops || i < 0) return 0;
  size_t n = strlen(s);
  if ((size_t)i >= n) return (long)n;
  return (long)(i + (long)strcspn(s + i, stops));
}

/* Is `i` at or past the end?  A boolean, so a reader's loop head branches on it with no compare. */
long lin_tbend(const char *s, long i) { return !s || i < 0 || (size_t)i >= strlen(s); }

/* First byte at or after `i` that is NOT in `accept`, i.e. strspn: the end of a run. */
long lin_trun(const char *s, long i, const char *accept) {
  if (!s || !accept || i < 0 || (size_t)i > strlen(s)) return -1;
  return (long)(i + (long)strspn(s + i, accept));
}

/* Does the text at `i` begin with `lit`?  `b` = the result is a BOOLEAN, so the caller's `if`
   consumes it directly: a numeric result would have to be compared, and a comparison inside a
   recursive definition is the expensive shape this whole domain exists to avoid. */
long lin_tbhas(const char *s, long i, const char *lit) {
  if (!s || !lit || i < 0) return 0;
  size_t n = strlen(s);
  if ((size_t)i > n) return 0;
  return strncmp(s + i, lit, strlen(lit)) == 0;
}

/* The same test, numerically (1/0), for a caller that wants a value rather than a branch. */
long lin_tmatch(const char *s, long i, const char *lit) {
  if (!s || !lit || i < 0) return 0;
  size_t n = strlen(s);
  if ((size_t)i > n) return 0;
  return strncmp(s + i, lit, strlen(lit)) == 0;
}

/* A substring.  The result is read back as a Lin STRING (`ts` prefix), so the buffer must outlive
   the call: a small ring is used rather than a malloc per token, and the ring is large enough that
   the few slices a reader holds at once never collide. */
/* SCRATCH FOR SLICES, GROWN FROM THE TEXT, NOT CHOSEN: a bump arena that doubles when it fills, so
   there is no per-slice bound, and a wrap simply reuses the block.  A returned slice stays valid
   until the arena is exhausted, and callers materialize it at once (readback copies a string into
   the net as it reads it). */
static char *slice_arena;
static size_t slice_cap, slice_used;
char *lin_tsub(const char *s, long i, long n) {
  size_t len = s ? strlen(s) : 0, take = 0;
  if (s && i >= 0 && n > 0 && (size_t)i < len) {
    take = (size_t)n;
    if (take > len - (size_t)i) take = len - (size_t)i;
  }
  size_t need = take + 1;
  if (slice_used + need > slice_cap) {
    size_t want = slice_cap ? slice_cap * 2 : need;
    if (want < need) want = need;
    char *grown = realloc(slice_arena, want);
    if (!grown) return "";                    /* out of memory: an empty slice, never a bad pointer */
    slice_arena = grown; slice_cap = want; slice_used = 0;
  }
  char *out = slice_arena + slice_used;
  slice_used += need;
  if (take) memcpy(out, s + i, take);
  out[take] = 0;
  return out;
}

/* ---------------- the pure-call registry ----------------
   A call whose result feeds a CONDITION must be FOLDED, not applied: `if` applies its condition to two
   thunks, so an `_ffi` closure reached there is beta-reduced with an extra argument and answers
   garbage (measured: `(if (streq "a" "a") 111 222)` printed 108).  The fold asks the registry who
   supplies a call and whether it DECLARED those calls pure; a provider that answers is dispatched
   through `lin_scalar_ops_run`, and the value lands in the consumer.  So every numeric and boolean row
   here is registered, exactly as the arithmetic provider registers its own -- the slice row (`lin_tsub`)
   cannot be, because a scalar reply carries a number, and a string is read back by the FFI path. */
static int text_known(const char *fn) {
  static const char *const rows[] = {"lin_tlen", "lin_tget", "lin_tbend", "lin_tbhas", "lin_tfind",
                                     "lin_tfindany", "lin_trun", "lin_tmatch"};
  for (size_t i = 0; i < sizeof rows / sizeof *rows; i++) if (!strcmp(fn, rows[i])) return 1;
  return 0;
}
static int text_ops(const char *fn, int argc, const long *a, long *out, int *outkind) {
  if (argc < 0) return text_known(fn);                 /* the OWNERSHIP query: is it ours, and pure */
  if (!text_known(fn) || !a) return 0;
  const char *s = (const char *)(intptr_t)a[0];
  const char *t = argc > 2 ? (const char *)(intptr_t)a[2] : NULL;
  if (!strcmp(fn, "lin_tlen")) { *out = lin_tlen(s); *outkind = 1; return 1; }
  if (!strcmp(fn, "lin_tget")) { *out = lin_tget(s, a[1]); *outkind = 1; return 1; }
  if (!strcmp(fn, "lin_tbend")) { *out = lin_tbend(s, a[1]) ? 1 : 0; *outkind = 3; return 1; }
  if (!strcmp(fn, "lin_tbhas")) { *out = lin_tbhas(s, a[1], t) ? 1 : 0; *outkind = 3; return 1; }
  if (!strcmp(fn, "lin_tfind")) { *out = lin_tfind(s, a[1], a[2]); *outkind = 1; return 1; }
  if (!strcmp(fn, "lin_tfindany")) { *out = lin_tfindany(s, a[1], t); *outkind = 1; return 1; }
  if (!strcmp(fn, "lin_trun")) { *out = lin_trun(s, a[1], t); *outkind = 1; return 1; }
  if (!strcmp(fn, "lin_tmatch")) { *out = lin_tmatch(s, a[1], t); *outkind = 1; return 1; }
  return 0;
}

LinDriver lin_text_driver;
static void __attribute__((constructor)) text_load(void) {
  static int registered = 0;
  if (registered) return;
  registered = 1;
  lin_driver_add(&lin_text_driver);
  lin_scalar_ops_add(text_ops, 1);
}

/* No strategy, no claim, no state: this driver exists so its SYMBOLS are loaded (RTLD_GLOBAL) and
   the FFI can reach them.  `(set_driver "text")` is the load, nothing else. */
LinDriver lin_text_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "text", .description = "string indexing for source text (no state: FFI rows only)",
  .caps = 0, .priority = 0, .wants = 0,
};
