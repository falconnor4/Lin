/* Lin readback / IO-effect runtime (std — not core). #included into src/io.c: value rendering, net printer, and the monadic IO/effect runner (_iod/_iop/_ior/_iow), sharing io.c's statics. */

/* render one decoded value to a stream (1=int, 2=str, 3=bool, 4=float); returns 1 if rendered, else 0 */
static int render_val(FILE *f, Val v) {
  if (v.kind == 1) fprintf(f, "%ld", v.iv);
  else if (v.kind == 2) fputs(v.sv, f);
  else if (v.kind == 3) fputs(v.iv ? "true" : "false", f);
  else if (v.kind == 4) { double d; memcpy(&d, &v.iv, 8); fprintf(f, "%g", d); }
  else return 0;
  fflush(f); return 1;
}

/* Decode a non-FFI port as a value: string (2), int (1), bool (3), float (4). */
static Val decode(Net *n, Port p) {
  Val v = {0};
  if (net_read_string(n, p, v.sv, sizeof(v.sv)) >= 0) v.kind = 2;
  else { double d; if (net_read_float(n, p, &d)) { memcpy(&v.iv, &d, 8); v.kind = 4; } }
  if (!v.kind && (v.iv = net_read_int(n, p)) >= 0) v.kind = 1;
  if (!v.kind && (v.iv = net_read_bool(n, p)) >= 0) v.kind = 3;
  return v;
}

static int net_try_ffi(Net *n, Port p) {
  return render_val(stdout, run_ffi(n, p));
}

static unsigned char *vis_print = NULL;
/* capacity of vis_print (and 3x for viz_txt).  Printing can ALLOCATE: node 0's
   LAM case calls net_read_int, whose readback peek asks the drivers to
   materialise a closure, and a driver does that with net_alloc_scott.  So
   `N->nn` grows while we print and the arrays must be indexed against the
   capacity they were allocated with, not against the current node count. */
static size_t vis_cap = 0;

/* Readback renders into a buffer so a shared (DAG) subterm is rendered ONCE and
   replayed from a memo on later visits; re-walking it was exponential in the number
   of sharing points (bench_combinators: 62 s of printing for 1.1 s of reduction). */
static char *ob_buf = NULL; static size_t ob_len, ob_cap;
static char **viz_txt = NULL;      /* memo: node*3+port -> rendered text */
static long qmarks = 0;            /* '?' (cycle/over-depth) marks emitted so far */

static void ob_need(size_t k) {
  if (ob_len + k + 1 > ob_cap) {
    size_t c = ob_cap ? ob_cap : 256;
    while (c < ob_len + k + 1) c *= 2;
    ob_buf = realloc(ob_buf, c); ob_cap = c;
  }
}
static void ob_putc(int c) { ob_need(1); ob_buf[ob_len++] = (char)c; }
static void ob_puts(const char *s) { size_t k = strlen(s); ob_need(k); memcpy(ob_buf + ob_len, s, k); ob_len += k; }
static void ob_printf(const char *f, ...) {
  char tmp[128]; va_list ap; va_start(ap, f);
  int k = vsnprintf(tmp, sizeof tmp, f, ap); va_end(ap);
  if (k > 0) ob_puts(tmp);
}

/* Render a port representation into the output buffer. */
static void print_port(Port p, int depth) {
  if (depth > N->nn || p.node < 0 || p.node >= N->nn) { ob_putc('?'); qmarks++; return; }
  if (N->dead[p.node]) { ob_putc('_'); return; }
  if (N->tag[p.node] == LAM && p.port == 1) { ob_puts(NNM(N, p.node)); return; }
  size_t key = (size_t)p.node * 3 + (size_t)p.port;
  int in_vis = (size_t)p.node < vis_cap, in_txt = key < vis_cap * 3;
  if (viz_txt && in_txt && viz_txt[key]) { ob_puts(viz_txt[key]); return; }
  if (vis_print && in_vis && vis_print[p.node]) { ob_putc('?'); qmarks++; return; }
  if (vis_print && in_vis) vis_print[p.node] = 1;
  long q0 = qmarks; size_t o0 = ob_len;
  switch (N->tag[p.node]) {
  case ROOT: print_port(wire(p), depth + 1); break;
  case ERA: ob_putc('_'); break;
  case DUP: print_port(p.port == 0 ? wire((Port){p.node, 1}) : wire((Port){p.node, 0}), depth + 1); break;
  case APP:
    ob_putc('('); print_port(wire((Port){p.node, 0}), depth + 1); ob_putc(' ');
    print_port(wire((Port){p.node, 2}), depth + 1); ob_putc(')'); break;
  case LAM:
    if (p.port == 0) {
      double d; if (net_read_float(N, p, &d)) { ob_printf("%g", d); break; }
      long v = net_read_int(N, p); if (v >= 0) { ob_printf("%ld", v); break; }
      int b = net_read_bool(N, p); if (b >= 0) { ob_puts(b ? "true" : "false"); break; }
      ob_printf("(\\%s ", NNM(N, p.node)); print_port(wire((Port){p.node, 2}), depth + 1); ob_putc(')'); break;
    }
    print_port(wire(p), depth + 1); break;
  }
  if (vis_print && in_vis) vis_print[p.node] = 0;
  /* memoise only context-free renders: a '?' on the way in means this text was
     shaped by an in-progress ancestor (a real cycle), so it must not be replayed. */
  if (viz_txt && in_txt && qmarks == q0) {
    size_t k = ob_len - o0;
    char *t = malloc(k + 1);
    if (t) { memcpy(t, ob_buf + o0, k); t[k] = 0; viz_txt[key] = t; }
  }
}

int net_print(Net *n) {
  N = n;
  Port r = dup_hop(n, wire((Port){0, 0}));
  if (r.node >= 0 && r.node < n->nn && n->tag[r.node] == LAM) {
    if (net_try_ffi(n, r)) return 0;
    Val v = decode(n, r);
    if (v.kind == 2) { printf("\"%s\"", v.sv); return 0; }
    if (render_val(stdout, v)) return 0;
  }
  vis_cap = (size_t)(n->nn + 1);
  vis_print = calloc(vis_cap, 1);
  viz_txt = calloc(vis_cap * 3, sizeof *viz_txt);
  ob_len = 0; qmarks = 0;
  print_port(r, 0);
  fwrite(ob_buf, 1, ob_len, stdout);
  if (viz_txt) { for (size_t i = 0; i < vis_cap * 3; i++) free(viz_txt[i]); free(viz_txt); viz_txt = NULL; }
  free(vis_print); vis_print = NULL; vis_cap = 0;
  return 0;
}

static Port net_alloc_string(Net *n, const char *s) {
  Scope sc = scope_nil();
  Port c_nil = net_alloc(n, LAM, sc, "_cl"), n_nil = net_alloc(n, LAM, sc, "_nl");
  Port bt = net_alloc(n, LAM, sc, "_bt"), bf = net_alloc(n, LAM, sc, "_bf");
  net_link(n, (Port){c_nil.node, 2}, (Port){n_nil.node, 0}, 0); net_link(n, (Port){n_nil.node, 2}, (Port){bt.node, 0}, 0);
  net_link(n, (Port){bt.node, 2}, (Port){bf.node, 0}, 0);       net_link(n, (Port){bf.node, 2}, (Port){bt.node, 1}, 0);
  Port cur = (Port){c_nil.node, 0};
  for (long i = (long)strlen(s) - 1; i >= 0; i--) {
    Port ch = net_alloc_scott(n, (unsigned char)s[i]);
    Port c_lam = net_alloc(n, LAM, sc, "_cl"), n_lam = net_alloc(n, LAM, sc, "_nl");
    Port a1 = net_alloc(n, APP, sc, ""), a2 = net_alloc(n, APP, sc, "");
    net_link(n, (Port){c_lam.node, 2}, (Port){n_lam.node, 0}, 0);
    net_link(n, (Port){a1.node, 0}, (Port){c_lam.node, 1}, 0); net_link(n, (Port){a1.node, 2}, ch, 0);
    net_link(n, (Port){a2.node, 0}, (Port){a1.node, 1}, 0); net_link(n, (Port){a2.node, 2}, cur, 0);
    net_link(n, (Port){n_lam.node, 2}, (Port){a2.node, 1}, 0);
    cur = (Port){c_lam.node, 0};
  }
  return cur;
}

static void chomp(char *s) { size_t l = strlen(s); if (l > 0 && s[l - 1] == '\n') s[l - 1] = 0; }
static void read_stream(FILE *f, char *buf, size_t sz, int is_pipe) {
  if (!f) return;
  size_t nr = fread(buf, 1, sz - 1, f);
  buf[nr] = 0;
  chomp(buf);
  if (is_pipe) pclose(f); else fclose(f);
}
static void read_stdin(char *buf, size_t sz) { if (!fgets(buf, (int)sz, stdin)) buf[0] = 0; else chomp(buf); }

static inline int is_io_tag(const char *s) { return ctor_tag(s) == DT_EFF; }

/* apply effect continuation `fn` to value `arg`, relink ROOT, and re-reduce: the single monadic step shared by every effect (print/read/wait/ffi) */
static void eff_apply(Net *n, Port fn, Port arg) {
  Port app = net_alloc(n, APP, scope_nil(), "");
  net_link(n, (Port){app.node, 0}, fn, 1); net_link(n, (Port){app.node, 2}, arg, 1);
  net_link(n, (Port){0, 0}, (Port){app.node, 1}, 1);
}

int net_run_io(Net *n, long step_limit) {
  N = n;
  int did_io = 0;
  for (;;) {
    Port r = dup_hop(n, wire((Port){0, 0}));
    if (r.node < 0 || r.node >= n->nn || n->dead[r.node] || n->tag[r.node] != LAM) break;
    if (!strcmp(NNM(n, r.node), "_iod")) return 1;
    if (!strcmp(NNM(n, r.node), "_iop")) {
      Port body = dup_hop(n, wire((Port){r.node, 2}));
      if (body.node < 0 || n->tag[body.node] != APP) break;
      Port a0 = dup_hop(n, wire((Port){body.node, 0}));
      if (a0.node < 0 || n->tag[a0.node] != APP) break;
      Port a00 = dup_hop(n, wire((Port){a0.node, 0}));
      FILE *out_fp = stdout;
      Port msg_p = dup_hop(n, wire((Port){a0.node, 2}));
      if (a00.node >= 0 && n->tag[a00.node] == APP) {
        long dst_fd = net_read_int(n, dup_hop(n, wire((Port){a00.node, 2})));
        if (dst_fd == 2) out_fp = stderr;
      }
      if (!net_try_ffi(n, msg_p)) {
        Val mv = decode(n, msg_p);
        if (!render_val(out_fp, mv)) fputs("?", out_fp);
      }
      fflush(out_fp);
      Port next_p = wire((Port){body.node, 2});
      if (next_p.node >= 0 && next_p.node < n->nn && !n->dead[next_p.node] && n->tag[next_p.node] == LAM && !is_io_tag(NNM(n, next_p.node)))
        eff_apply(n, next_p, net_alloc_scott(n, 0));
      else net_link(n, (Port){0, 0}, next_p, 1);
      net_reduce(n, step_limit);
      did_io = 1;
      continue;
    }
    if (!strcmp(NNM(n, r.node), "_ior") || !strcmp(NNM(n, r.node), "_iow")) {
      Port body = dup_hop(n, wire((Port){r.node, 2}));
      if (body.node < 0 || n->tag[body.node] != APP) break;
      Port a0 = dup_hop(n, wire((Port){body.node, 0}));
      Port cb = wire((Port){body.node, 2});
      Port src_p = (a0.node >= 0 && n->tag[a0.node] == APP) ? dup_hop(n, wire((Port){a0.node, 2})) : (Port){-1, 0};

      char in_buf[4096] = {0};
      long res_int = -1; int is_int = 0;
      Val fv = (src_p.node >= 0) ? run_ffi(n, src_p) : (Val){0};
      if (fv.kind == 1) { res_int = fv.iv; is_int = 1; }
      else if (fv.kind == 3) is_int = 2;                      /* bool result */
      else if (fv.kind == 2) snprintf(in_buf, sizeof(in_buf), "%s", fv.sv);
      else if (src_p.node < 0) read_stdin(in_buf, sizeof(in_buf));
      else {
        long fd = net_read_int(n, src_p);
        if (fd == 0) read_stdin(in_buf, sizeof(in_buf));
        else if (fd > 0) { ssize_t nr = read((int)fd, in_buf, sizeof(in_buf) - 1); if (nr > 0) { in_buf[nr] = 0; chomp(in_buf); } }
        else {
          char src[1024];
          if (net_read_string(n, src_p, src, sizeof(src)) >= 0) {
            if (!strcmp(src, "stdin") || !strcmp(src, "0")) read_stdin(in_buf, sizeof(in_buf));
            else if (src[0] == '!' || !strncmp(src, "cmd:", 4)) read_stream(popen(src[0] == '!' ? src + 1 : src + 4, "r"), in_buf, sizeof(in_buf), 1);
            else if (!strncmp(src, "sleep:", 6)) { res_int = strtol(src + 6, NULL, 10); if (res_int > 0) usleep((useconds_t)(res_int * 1000)); is_int = 1; }
            else read_stream(fopen(!strncmp(src, "file:", 5) ? src + 5 : src, "r"), in_buf, sizeof(in_buf), 0);
          }
        }
      }
      char *endptr = NULL;
      long val = (!is_int && in_buf[0]) ? strtol(in_buf, &endptr, 10) : -1;
      Port arg = (is_int == 2) ? net_alloc_bool(n, (int)fv.iv) : is_int ? net_alloc_scott(n, res_int) : (in_buf[0] && endptr && !*endptr && val >= 0) ? net_alloc_scott(n, val) : net_alloc_string(n, in_buf);
      eff_apply(n, cb, arg);
      net_reduce(n, step_limit); did_io = 1; continue;
    }
    break;
  }
  return did_io;
}
