/* ============================================================================
 * Shared on-net decoder (std — not part of the pure src/ core).
 *
 * #included into src/io.c (unity build) so it shares that TU's statics
 * (N, wire, skip_dup, net_read_*); the functions are also EXPORTED so driver
 * plugins (simd.c, gpu.c, future) can reuse THE SAME decoder instead of each
 * carrying its own arg-spine / DUP-hop walker.
 *
 * A saturated `_ffi` closure is the shape
 *     \_ffi. \_ret. ((_ffi "lin_*") args)         args = `_cl`-spine of scalars
 * These helpers locate the fn name, walk the arg spine, and decode each arg to
 * a Val (int / bool / float-bits / string), recursing into nested `_ffi`
 * closures so composed arithmetic composes.
 * ========================================================================== */

/* Deref a DUP (port 0) chain to the underlying wire; pure, no allocation. */
Port net_dhop(Net *n, Port p) {
  N = n;
  return skip_dup(n, p);
}

/* Read the fn name of the `_ffi` closure rooted at port p (port 0). */
int net_ffi_fn(Net *n, Port p, char *fn, int fnmax) {
  N = n;
  Port a1;
  if (!ffi_header(n, p, &a1, 0)) return 0;
  if (a1.node < 0 || a1.port != 1 || n->tag[a1.node] != APP) return 0;
  return net_read_string(n, wire((Port){a1.node, 2}), fn, (size_t)fnmax) >= 0;
}

/* Decode a single argument port into a Val.  int/bool/float/string directly; a
   nested `_ffi` closure is folded (run_ffi) first.  Returns 1 on success. */
static int dec_arg(Net *n, Port p, Val *v) {
  N = n;
  p = skip_dup(n, p);
  if (p.node < 0 || p.node >= n->nn || n->dead[p.node] || n->tag[p.node] != LAM) return 0;
  if (ctor_tag(NNM(n, p.node)) == DT_FFI) { *v = run_ffi(n, (Port){p.node, 0}); return v->kind != 0; }
  if (ctor_tag(NNM(n, p.node)) == DT_FLOAT) { double d; if (!net_read_float(n, p, &d)) return 0; memcpy(&v->iv, &d, 8); v->kind = 4; return 1; }
  if (ctor_tag(NNM(n, p.node)) == DT_BOOL) { int b = net_read_bool(n, p); if (b < 0) return 0; v->iv = b; v->kind = 3; return 1; }
  if (ctor_tag(NNM(n, p.node)) == DT_STR) { if (net_read_string(n, p, v->sv, sizeof(v->sv)) < 0) return 0; v->kind = 2; return 1; }
  long x = net_read_int(n, p); if (x < 0) return 0; v->iv = x; v->kind = 1; return 1;
}

/* Decode a `_cl`-spine argument list rooted at port `argp` into up to `max`
   Vals.  The single spine walk shared by the `_ffi` closure (net_ffi_args) and
   the `_op` redex fold (net_spine_args).  Returns the arg count; 0 if none
   (a single non-spine arg is decoded too). */
static int decode_spine(Net *n, Port argp, Val *vals, int max) {
  int argc = 0; Port cur = skip_dup(n, argp);
  if (cur.node >= 0 && cur.node < n->nn && n->tag[cur.node] == LAM &&
      ctor_tag(NNM(n, cur.node)) == DT_STR) {
    Port bn = skip_dup(n, wire((Port){cur.node, 2}));
    if (bn.node >= 0 && bn.port == 0 && n->tag[bn.node] == LAM) {
      for (int step = 0; step < n->nn && argc < max; step++) {
        cur = skip_dup(n, cur);
        if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node] || n->tag[cur.node] != LAM) break;
        Port inner = skip_dup(n, wire((Port){cur.node, 2}));
        if (inner.node < 0 || inner.port != 0 || n->tag[inner.node] != LAM) break;
        Port body = skip_dup(n, wire((Port){inner.node, 2}));
        if (body.node < 0 || n->tag[body.node] != APP) break;
        Port ia = skip_dup(n, wire((Port){body.node, 0}));
        if (ia.node >= 0 && n->tag[ia.node] == APP) {
          if (dec_arg(n, wire((Port){ia.node, 2}), &vals[argc])) argc++;
        }
        cur = wire((Port){body.node, 2});
      }
    }
  }
  if (argc == 0 && dec_arg(n, argp, &vals[0])) argc = 1;
  return argc;
}

/* Walk the `_cl`-spine arg list of the `_ffi` closure rooted at `lam` (same
   shape as net_ffi_fn); delegates the spine walk to decode_spine. */
int net_ffi_args(Net *n, Port lam, Val *vals, int max) {
  N = n;
  Port argp;
  if (!ffi_header(n, lam, 0, &argp)) return 0;
  return decode_spine(n, argp, vals, max);
}

/* Decode a `_cl`-spine argument list rooted at port `argp` (not inside a closure
   body): the `_op` redex fold reads a saturated arith op's raw operands this
   way.  Exported so driver plugins reuse the shared decoder. */
int net_spine_args(Net *n, Port argp, Val *vals, int max) {
  N = n;
  return decode_spine(n, argp, vals, max);
}
