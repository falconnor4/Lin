#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>

// =============================================================================
// Configuration
// =============================================================================
#define NODE_CAP 1000000
#define ACTIVE_CAP 500000
#define MAX_STEPS 10000000
#define NAME_LEN 64
#define ENV_CAP 4096

#define CPY_NAME(d,s) do { memcpy(d,s,NAME_LEN-1); d[NAME_LEN-1]=0; } while(0)

// =============================================================================
// Node Tags
// =============================================================================
enum { LAM, APP, DUP, ERA, ROOT, NTAGS };

static int arity(int t) {
  switch (t) { case LAM: case APP: case DUP: return 2; case ERA: return 1; default: return 0; }
}

// =============================================================================
// Scope Path (non-abelian gauge word over {1,2}*)
// =============================================================================
typedef struct { uint64_t bits; int len; } Scope;

static Scope scope_nil(void) { return (Scope){ 0, 0 }; }
static int scope_eq(Scope a, Scope b) { return a.len == b.len && a.bits == b.bits; }

// =============================================================================
// Port
// =============================================================================
typedef struct { int node; int port; } Port;
#define PORT_NONE ((Port){ -1, -1 })

// =============================================================================
// Net: flat-array interaction net
// =============================================================================
typedef struct {
  int cap, next_node;
  int* tag;
  Port* wire;
  Scope* scope;
  char (*name)[NAME_LEN];
  Port* active;
  int active_top;
  int steps;
} Net;

static Net* net_new(int cap) {
  Net* n = calloc(1, sizeof(Net));
  n->cap = cap;
  n->tag = calloc(cap, sizeof(int));
  n->wire = calloc(cap * 3, sizeof(Port));
  n->scope = calloc(cap, sizeof(Scope));
  n->name = calloc(cap, NAME_LEN);
  n->active = calloc(ACTIVE_CAP, sizeof(Port));
  n->next_node = 1;
  n->tag[0] = ROOT;
  n->scope[0] = scope_nil();
  for (int i = 0; i < 3; i++) n->wire[i] = PORT_NONE;
  return n;
}

static int net_alloc(Net* n, int tag, Scope sc) {
  int id = n->next_node++;
  if (id >= n->cap) {
    int nc = n->cap * 2;
    n->tag = realloc(n->tag, nc * sizeof(int));
    n->wire = realloc(n->wire, nc * 3 * sizeof(Port));
    n->scope = realloc(n->scope, nc * sizeof(Scope));
    n->name = realloc(n->name, nc * NAME_LEN);
    n->cap = nc;
  }
  n->tag[id] = tag;
  n->scope[id] = sc;
  n->name[id][0] = 0;
  int a = arity(tag);
  for (int i = 0; i <= a; i++) n->wire[id * 3 + i] = PORT_NONE;
  return id;
}

static Port wire_get(Net* n, int node, int port) {
  return n->wire[node * 3 + port];
}

static void wire_connect(Net* n, Port a, Port b) {
  n->wire[a.node * 3 + a.port] = b;
  n->wire[b.node * 3 + b.port] = a;
  if (a.port == 0 && b.port == 0) {
    n->active[n->active_top++] = a;
    n->active[n->active_top++] = b;
  }
}

// =============================================================================
// Term AST
// =============================================================================
typedef struct Term {
  int type;
  char name[NAME_LEN];
  struct Term *left, *right;
} Term;

static Term* term_alloc(int type, const char* name, Term* l, Term* r) {
  Term* t = calloc(1, sizeof(Term));
  t->type = type;
  if (name && name[0]) { CPY_NAME(t->name, name); }
  t->left = l; t->right = r;
  return t;
}

static void term_free(Term* t) {
  if (!t) return;
  term_free(t->left); term_free(t->right); free(t);
}

// =============================================================================
// Parser
// =============================================================================
static const char* g_input;
static int g_pos;

static int parse_skip_ws(void) {
  while (g_input[g_pos] && (g_input[g_pos] == ' ' || g_input[g_pos] == '\t' || g_input[g_pos] == '\n')) g_pos++;
  return g_input[g_pos];
}

static void parse_symbol(char* buf, int bufsz) {
  int i = 0;
  while (g_input[g_pos] && !isspace(g_input[g_pos]) && g_input[g_pos] != '(' && g_input[g_pos] != ')' && i < bufsz - 1)
    buf[i++] = g_input[g_pos++];
  buf[i] = 0;
}

static int is_all_digits(const char* s) {
  if (!s || !s[0]) return 0;
  for (int i = 0; s[i]; i++) if (!isdigit((unsigned char)s[i])) return 0;
  return 1;
}

static Term* copy_term(Term* t);

static Term* make_church(int val) {
  Term* f = term_alloc(0, "_cf", NULL, NULL);
  Term* x = term_alloc(0, "_cx", NULL, NULL);
  Term* body = copy_term(x);
  for (int i = 0; i < val; i++)
    body = term_alloc(2, "", copy_term(f), body);
  Term* lx = term_alloc(1, "_cx", body, NULL);
  Term* lf = term_alloc(1, "_cf", lx, NULL);
  term_free(f); term_free(x);
  return lf;
}

static Term* parse_term(void);

static Term* parse_app(Term* first) {
  Term* t = first;
  while (parse_skip_ws() && g_input[g_pos] != ')') {
    Term* arg = parse_term();
    t = term_alloc(2, "", t, arg);
  }
  return t;
}

static Term* parse_term(void) {
  parse_skip_ws();
  if (g_input[g_pos] == '(') {
    g_pos++;
    parse_skip_ws();
    char buf[NAME_LEN];
    // If next char is '(', recursively parse a subterm as the first element
    if (g_input[g_pos] == '(') {
      Term* first = parse_term();
      Term* t = parse_app(first);
      parse_skip_ws();
      if (g_input[g_pos] == ')') g_pos++;
      return t;
    }
    parse_symbol(buf, sizeof(buf));
    if (strcmp(buf, "\\") == 0 || strcmp(buf, "lambda") == 0 || strcmp(buf, "lam") == 0 || strcmp(buf, "\xce\xbb") == 0) {
      parse_skip_ws();
      char vn[NAME_LEN];
      parse_symbol(vn, sizeof(vn));
      parse_skip_ws();
      Term* body = parse_term();
      body = parse_app(body);
      parse_skip_ws();
      if (g_input[g_pos] == ')') g_pos++;
      return term_alloc(1, vn, body, NULL);
    } else if (strcmp(buf, "define") == 0) {
      parse_skip_ws();
      char dn[NAME_LEN];
      parse_symbol(dn, sizeof(dn));
      parse_skip_ws();
      Term* val = parse_term();
      parse_skip_ws();
      if (g_input[g_pos] == ')') g_pos++;
      return term_alloc(100, dn, val, NULL);
    } else {
      Term* first = term_alloc(0, buf, NULL, NULL);
      Term* t = parse_app(first);
      parse_skip_ws();
      if (g_input[g_pos] == ')') g_pos++;
      return t;
    }
  }
  char buf[NAME_LEN];
  parse_symbol(buf, sizeof(buf));
  if (is_all_digits(buf)) return term_alloc(3, buf, NULL, NULL);
  return term_alloc(0, buf, NULL, NULL);
}

// =============================================================================
// Compilation: Term -> Net
// =============================================================================
typedef struct {
  char name[NAME_LEN];
  Port binding;       // LAM.port1
  Port first_target;  // saved target of binding port from first usage
  int count;          // number of usages
  Port extras[ENV_CAP]; // ERA ports for usages beyond the first
  int nextra;
} EnvEntry;
typedef struct { EnvEntry entries[ENV_CAP]; int n; } Env;

static Env* env_new(void) { return calloc(1, sizeof(Env)); }
static void env_free(Env* e) { free(e); }

static EnvEntry* env_find(Env* e, const char* name) {
  for (int i = e->n - 1; i >= 0; i--)
    if (strcmp(e->entries[i].name, name) == 0) return &e->entries[i];
  return NULL;
}

static void env_push(Env* e, const char* name, Port binding) {
  if (e->n < ENV_CAP) {
    CPY_NAME(e->entries[e->n].name, name);
    e->entries[e->n].binding = binding;
    e->entries[e->n].first_target = PORT_NONE;
    e->entries[e->n].count = 0;
    e->entries[e->n].nextra = 0;
    e->n++;
  }
}

static void env_pop(Env* e, const char* name) {
  for (int i = e->n - 1; i >= 0; i--) {
    if (strcmp(e->entries[i].name, name) == 0) {
      for (int k = i; k < e->n - 1; k++) e->entries[k] = e->entries[k + 1];
      e->n--; return;
    }
  }
}

static Port compile_term(Term* t, Scope sc, Net* n, Env* e);

static Port compile_term(Term* t, Scope sc, Net* n, Env* e) {
  if (t->type == 0) {
    EnvEntry* ent = env_find(e, t->name);
    if (ent) {
      ent->count++;
      if (ent->count == 1) return ent->binding; // first usage: return binding port
      // Subsequent usage: save first target, create ERA for DUP leaf
      if (ent->count == 2) ent->first_target = wire_get(n, ent->binding.node, ent->binding.port);
      int era = net_alloc(n, ERA, sc);
      CPY_NAME(n->name[era], t->name);
      Port ep = (Port){ era, 1 };
      if (ent->nextra < ENV_CAP) ent->extras[ent->nextra++] = ep;
      return ep;
    }
    int era = net_alloc(n, ERA, sc);
    CPY_NAME(n->name[era], t->name);
    return (Port){ era, 1 };
  }
  if (t->type == 1) {
    int id = net_alloc(n, LAM, sc);
    CPY_NAME(n->name[id], t->name);
    Port var_slot = (Port){ id, 1 };
    Port body_slot = (Port){ id, 2 };
    env_push(e, t->name, var_slot);
    Port body_res = compile_term(t->left, sc, n, e);
    EnvEntry* ent = env_find(e, t->name);
    int cnt = ent ? ent->count : 0;
    Port ft = ent ? ent->first_target : PORT_NONE;
    Port* extras = ent ? ent->extras : NULL;
    int nx = ent ? ent->nextra : 0;
    env_pop(e, t->name);
    wire_connect(n, body_slot, body_res);
    if (cnt == 0) {
      int era = net_alloc(n, ERA, sc);
      wire_connect(n, var_slot, (Port){ era, 1 });
    } else if (cnt > 1) {
      Port root = var_slot;
      for (int i = 0; i < nx; i++) {
        int dup = net_alloc(n, DUP, sc);
        Port prev = (i == 0) ? ft : root;
        wire_connect(n, (Port){ dup, 1 }, prev);
        Port usage = wire_get(n, extras[i].node, extras[i].port);
        wire_connect(n, (Port){ dup, 2 }, usage);
        root = (Port){ dup, 0 };
      }
      wire_connect(n, var_slot, root);
    }
    // cnt == 1: single usage via direct binding port wire — nothing extra
    return (Port){ id, 0 };
  }
  if (t->type == 2) {
    int id = net_alloc(n, APP, sc);
    Port app_fun = (Port){ id, 0 };
    Port app_ret = (Port){ id, 1 };
    Port app_arg = (Port){ id, 2 };
    Port fun_res = compile_term(t->left, sc, n, e);
    wire_connect(n, app_fun, fun_res);
    Port arg_res = compile_term(t->right, sc, n, e);
    wire_connect(n, app_arg, arg_res);
    return app_ret;
  }
  if (t->type == 3) {
    int val = atoi(t->name);
    if (val < 0 || val > 100000) return PORT_NONE;
    Term* ct = make_church(val);
    Port res = compile_term(ct, sc, n, e);
    term_free(ct);
    return res;
  }
  return PORT_NONE;
}

static Net* compile(Term* t) {
  Net* n = net_new(NODE_CAP);
  Env* e = env_new();
  Port res = compile_term(t, scope_nil(), n, e);
  env_free(e);
  wire_connect(n, (Port){ 0, 0 }, res);
  return n;
}

// =============================================================================
// Reduction
// =============================================================================
static void interact(Net* n, Port p1, Port p2) {
  if (n->tag[p1.node] > n->tag[p2.node] ||
      (n->tag[p1.node] == n->tag[p2.node] && p1.node > p2.node)) {
    Port t = p1; p1 = p2; p2 = t;
  }
  int t1 = n->tag[p1.node], t2 = n->tag[p2.node];

  if (t1 == LAM && t2 == APP) {
    Port p1v = wire_get(n, p1.node, 1);
    Port p1b = wire_get(n, p1.node, 2);
    Port p2r = wire_get(n, p2.node, 1);
    Port p2a = wire_get(n, p2.node, 2);
    n->wire[p1.node * 3 + 0] = PORT_NONE;
    n->wire[p2.node * 3 + 0] = PORT_NONE;
    int is_id = (p1v.node == p1.node && p1v.port == 2) && (p1b.node == p1.node && p1b.port == 1);
    if (is_id) {
      wire_connect(n, p2a, p2r);
    } else {
      wire_connect(n, p1v, p2a);
      wire_connect(n, p1b, p2r);
    }
  }
  else if (t1 == DUP && t2 == DUP && scope_eq(n->scope[p1.node], n->scope[p2.node])) {
    Port p1a = wire_get(n, p1.node, 1);
    Port p1b = wire_get(n, p1.node, 2);
    Port p2a = wire_get(n, p2.node, 1);
    Port p2b = wire_get(n, p2.node, 2);
    wire_connect(n, p1a, p2a);
    wire_connect(n, p1b, p2b);
  }
  else if (t1 == LAM && t2 == DUP) {
    Port p1v=wire_get(n,p1.node,1), p1b=wire_get(n,p1.node,2);
    Scope sl=n->scope[p1.node], sd=n->scope[p2.node];
    int is_id = (p1v.node==p1.node&&p1v.port==2)&&(p1b.node==p1.node&&p1b.port==1);
    if (is_id) {
      Port p2a=wire_get(n,p2.node,1), p2b=wire_get(n,p2.node,2);
      uint64_t b1=0,b2=0; int l1=0,l2=0;
      b1=sd.bits; l1=sd.len; b1=(b1<<sl.len)|sl.bits; l1+=sl.len; b1=(b1<<1)|0; l1+=1;
      b2=sd.bits; l2=sd.len; b2=(b2<<sl.len)|sl.bits; l2+=sl.len; b2=(b2<<1)|1; l2+=1;
      for (int i=0;i<3;i++) n->wire[p1.node*3+i]=PORT_NONE;
      for (int i=0;i<3;i++) n->wire[p2.node*3+i]=PORT_NONE;
      int n1=net_alloc(n,LAM,(Scope){b1,l1});
      int n2=net_alloc(n,LAM,(Scope){b2,l2});
      CPY_NAME(n->name[n1],n->name[p1.node]);
      CPY_NAME(n->name[n2],n->name[p1.node]);
      wire_connect(n,(Port){n1,1},(Port){n1,2});  // identity copy 1
      wire_connect(n,(Port){n2,1},(Port){n2,2});  // identity copy 2
      wire_connect(n,(Port){n1,0},p2a);
      wire_connect(n,(Port){n2,0},p2b);
    } else {
      int nn=n->next_node; n->next_node+=4;
      int nl1=nn,nl2=nn+1,nd1=nn+2,nd2=nn+3;
      uint64_t b1=0,b2=0; int l1=0,l2=0;
      b1=sd.bits; l1=sd.len; b1=(b1<<sl.len)|sl.bits; l1+=sl.len; b1=(b1<<1)|0; l1+=1;
      b2=sd.bits; l2=sd.len; b2=(b2<<sl.len)|sl.bits; l2+=sl.len; b2=(b2<<1)|1; l2+=1;
      for(int i=0;i<3;i++){n->wire[(nl1)*3+i]=PORT_NONE;n->wire[(nl2)*3+i]=PORT_NONE;n->wire[(nd1)*3+i]=PORT_NONE;n->wire[(nd2)*3+i]=PORT_NONE;}
      n->tag[nl1]=LAM;n->scope[nl1]=(Scope){b1,l1};
      CPY_NAME(n->name[nl1],n->name[p1.node]);
      n->tag[nl2]=LAM;n->scope[nl2]=(Scope){b2,l2};
      CPY_NAME(n->name[nl2],n->name[p1.node]);
      n->tag[nd1]=DUP;n->scope[nd1]=sd;
      n->tag[nd2]=DUP;n->scope[nd2]=sd;
      wire_connect(n,(Port){nd1,1},(Port){nl1,1});
      wire_connect(n,(Port){nd1,2},(Port){nl2,1});
      wire_connect(n,(Port){nd2,1},(Port){nl1,2});
      wire_connect(n,(Port){nd2,2},(Port){nl2,2});
      Port p2a=wire_get(n,p2.node,1), p2b=wire_get(n,p2.node,2);
      wire_connect(n,(Port){nd1,0},p1v); wire_connect(n,(Port){nd2,0},p1b);
      wire_connect(n,(Port){nl1,0},p2a); wire_connect(n,(Port){nl2,0},p2b);
    }
  }
  else if (t1 == APP && t2 == DUP) {
    Scope sa = n->scope[p1.node], sd = n->scope[p2.node];
    int nn = n->next_node; n->next_node += 4;
    int na1 = nn, na2 = nn+1, nd1 = nn+2, nd2 = nn+3;
    uint64_t b1=0,b2=0; int l1=0,l2=0;
    b1=sd.bits; l1=sd.len; b1=(b1<<sa.len)|sa.bits; l1+=sa.len; b1=(b1<<1)|0; l1+=1;
    b2=sd.bits; l2=sd.len; b2=(b2<<sa.len)|sa.bits; l2+=sa.len; b2=(b2<<1)|1; l2+=1;
    for (int i = 0; i < 3; i++) {
      n->wire[(na1)*3+i]=PORT_NONE; n->wire[(na2)*3+i]=PORT_NONE;
      n->wire[(nd1)*3+i]=PORT_NONE; n->wire[(nd2)*3+i]=PORT_NONE;
    }
    n->tag[na1]=APP; n->scope[na1]=(Scope){b1,l1};
    n->tag[na2]=APP; n->scope[na2]=(Scope){b2,l2};
    n->tag[nd1]=DUP; n->scope[nd1]=sd;
    n->tag[nd2]=DUP; n->scope[nd2]=sd;
    wire_connect(n,(Port){nd1,1},(Port){na1,1});
    wire_connect(n,(Port){nd1,2},(Port){na2,1});
    wire_connect(n,(Port){nd2,1},(Port){na1,2});
    wire_connect(n,(Port){nd2,2},(Port){na2,2});
    Port p1r=wire_get(n,p1.node,1), p1a=wire_get(n,p1.node,2);
    Port p2a=wire_get(n,p2.node,1), p2b=wire_get(n,p2.node,2);
    wire_connect(n,(Port){nd1,0},p1r); wire_connect(n,(Port){nd2,0},p1a);
    wire_connect(n,(Port){na1,0},p2a); wire_connect(n,(Port){na2,0},p2b);
  }
}

static void reduce(Net* n, int max_steps) {
  for (int s = 0; s < max_steps && n->active_top > 0; s++) {
    Port p2 = n->active[--n->active_top];
    Port p1 = n->active[--n->active_top];
    if (p1.port != 0 || p2.port != 0) continue;
    Port c = wire_get(n, p1.node, 0);
    if (c.node != p2.node || c.port != 0) continue;
    c = wire_get(n, p2.node, 0);
    if (c.node != p1.node || c.port != 0) continue;
    n->steps = s + 1;
    interact(n, p1, p2);
  }
}

// =============================================================================
// Readback
// =============================================================================
typedef struct { int* visited; int cap; int n; } Visited;

static Visited* visited_new(int cap) {
  Visited* v = calloc(1, sizeof(Visited));
  v->visited = calloc(cap, sizeof(int)); v->cap = cap; v->n = 0;
  return v;
}

static int visited_mark(Visited* v, int node) {
  for (int i = 0; i < v->n; i++) if (v->visited[i] == node) return 1;
  if (v->n < v->cap) v->visited[v->n++] = node;
  return 0;
}

static void visited_free(Visited* v) { free(v->visited); free(v); }

static int church_to_int(Net* n, int node) {
  if (n->tag[node] != LAM) return -1;
  Port bf = wire_get(n, node, 2);
  if (bf.node < 0 || n->tag[bf.node] != LAM) return -1;
  int lam_x = bf.node;
  Port bx = wire_get(n, lam_x, 2);
  if (bx.node < 0) return -1;
  // Church numeral 0: inner body is x (inner LAM's port 1)
  if (bx.node == lam_x && bx.port == 1) return 0;
  int count = 0;
  Port cur = bx;
  for (int safety = 0; safety < 100000; safety++) {
    if (cur.node < 0 || n->tag[cur.node] != APP) break;
    Port fun = wire_get(n, cur.node, 0);
    Port arg = wire_get(n, cur.node, 2);
    int found_f = 0;
    Port fc = fun;
    for (int d = 0; d < 100; d++) {
      if (fc.node == node && fc.port == 1) { found_f = 1; break; }
      if (fc.node < 0 || n->tag[fc.node] != DUP) break;
      fc = wire_get(n, fc.node, 0);
    }
    if (!found_f) return -1;
    count++;
    cur = arg;
  }
  if (cur.node == lam_x && cur.port == 1) return count;
  return -1;
}

static void print_term(Net* n, Port p, Visited* v, FILE* out);

static void print_term(Net* n, Port p, Visited* v, FILE* out) {
  if (p.node < 0) { fprintf(out, "?"); return; }
  int node = p.node;
  int tag = n->tag[node];
  int port = p.port;

  if (tag == ROOT) {
    print_term(n, wire_get(n, node, 0), v, out);
  }
  else if (tag == LAM) {
    if (visited_mark(v, node)) { fprintf(out, "%s", n->name[node]); return; }
    int ci = church_to_int(n, node);
    if (ci >= 0) {
      fprintf(out, "#%d", ci);
      return;
    }
    if (port == 0) {
      fprintf(out, "(\\%s ", n->name[node]);
      print_term(n, wire_get(n, node, 2), v, out);
      fprintf(out, ")");
    } else if (port == 1) {
      fprintf(out, "%s", n->name[node]);
    } else {
      print_term(n, wire_get(n, node, 2), v, out);
    }
  }
  else if (tag == APP) {
    Port fun = wire_get(n, node, 0);
    Port arg = wire_get(n, node, 2);
    // If principal port (0) is disconnected, this APP was consumed
    // — read the argument as the result of substitution
    if (port == 1 && fun.node < 0) {
      print_term(n, arg, v, out);
    } else if (port == 0 || port == 1) {
      fprintf(out, "(");
      print_term(n, fun, v, out);
      fprintf(out, " ");
      print_term(n, arg, v, out);
      fprintf(out, ")");
    } else {
      print_term(n, fun, v, out);
    }
  }
  else if (tag == ERA) {
    fprintf(out, "%s", n->name[node]);
  }
  else if (tag == DUP) {
    Port in = wire_get(n, node, 0);
    if (in.node >= 0) print_term(n, in, v, out);
    else fprintf(out, "?");
  }
  else fprintf(out, "?");
}

static void readback(Net* n, FILE* out) {
  Visited* v = visited_new(n->next_node);
  print_term(n, (Port){ 0, 0 }, v, out);
  visited_free(v);
}

// =============================================================================
// GoI Spectral Invariant
// =============================================================================
static int64_t mod = 1000000007;

static int64_t mod_inv(int64_t a) {
  int64_t e = mod - 2, r = 1, b = a % mod;
  while (e) { if (e & 1) r = (r * b) % mod; b = (b * b) % mod; e >>= 1; }
  return r;
}

static int64_t goi_det(Net* n) {
  int dim = n->next_node * 3;
  if (dim == 0) return 1;
  int64_t* M = calloc((size_t)dim * dim, sizeof(int64_t));
  for (int i = 0; i < dim; i++) M[i * dim + i] = 2;
  for (int nd = 0; nd < n->next_node; nd++) {
    int a = arity(n->tag[nd]);
    for (int pi = 0; pi <= a; pi++) {
      Port w = n->wire[nd * 3 + pi];
      if (w.node >= 0 && w.node < n->next_node) {
        int r = nd * 3 + pi;
        int c = w.node * 3 + w.port;
        if (r < dim && c < dim) M[r * dim + c] = (M[r * dim + c] - 1 + mod) % mod;
      }
    }
  }
  int64_t det = 1;
  for (int k = 0; k < dim; k++) {
    int pivot = -1;
    for (int i = k; i < dim; i++) if (M[i * dim + k] != 0) { pivot = i; break; }
    if (pivot < 0) { det = 0; break; }
    if (pivot != k) {
      det = (mod - det) % mod;
      for (int j = k; j < dim; j++) { int64_t t = M[k*dim+j]; M[k*dim+j] = M[pivot*dim+j]; M[pivot*dim+j] = t; }
    }
    int64_t piv = M[k * dim + k];
    det = (det * piv) % mod;
    int64_t inv = mod_inv(piv);
    for (int i = k + 1; i < dim; i++) {
      int64_t fac = M[i * dim + k];
      if (fac == 0) continue;
      int64_t mult = (fac * inv) % mod;
      for (int j = k; j < dim; j++) {
        M[i * dim + j] = (M[i * dim + j] - mult * M[k * dim + j]) % mod;
        if (M[i * dim + j] < 0) M[i * dim + j] += mod;
      }
    }
  }
  free(M);
  return (det % mod + mod) % mod;
}

// =============================================================================
// Standard Library (embedded Lin definitions)
// =============================================================================
static const char* std_src =
  "(define true (\\ t (\\ f t)))\n"
  "(define false (\\ t (\\ f f)))\n"
  "(define not (\\ b (\\ t (\\ f ((b f) t)))))\n"
  "(define and (\\ p (\\ q ((p q) false))))\n"
  "(define or (\\ a (\\ b ((a true) b))))\n"
  "(define xor (\\ a (\\ b ((a (not b)) b))))\n"
  "(define if (\\ c (\\ t (\\ e ((c t) e)))))\n"
  "(define succ (\\ n (\\ f (\\ x (f ((n f) x))))))\n"
  "(define add (\\ m (\\ n (\\ f (\\ x ((m f) ((n f) x)))))))\n"
  "(define mul (\\ m (\\ n (\\ f (m (n f))))))\n"
  "(define pow (\\ m (\\ n (n m))))\n"
  "(define pred (\\ n (\\ f (\\ x (((n (\\ g (\\ h (h (g f))))) (\\ u x)) (\\ u u))))))\n"
  "(define sub (\\ m (\\ n ((n pred) m))))\n"
  "(define is_zero (\\ n ((n (\\ x false)) true)))\n"
  "(define leq (\\ m (\\ n (is_zero ((sub m) n)))))\n"
  "(define eq (\\ m (\\ n ((and (leq m n)) (leq n m)))))\n"
  "(define lt (\\ m (\\ n (not (leq n m)))))\n"
  "(define gt (\\ m (\\ n (not (leq m n)))))\n"
  "(define pair (\\ x (\\ y (\\ s ((s x) y)))))\n"
  "(define fst (\\ p (p (\\ x (\\ y x)))))\n"
  "(define snd (\\ p (p (\\ x (\\ y y)))))\n"
  "(define nil (\\ c (\\ n n)))\n"
  "(define cons (\\ h (\\ t (\\ c (\\ n ((c h) (t c n)))))))\n"
  "(define head (\\ l (l (\\ h (\\ t h)) nil)))\n"
  "(define tail (\\ l (l (\\ h (\\ t t)) nil)))\n"
  "(define is_empty (\\ l (l (\\ h (\\ t false)) true)))\n"
  "(define Y (\\ f ((\\ x (f (x x))) (\\ x (f (x x))))))\n"
  ;
typedef struct { char name[NAME_LEN]; Term* term; } Def;
static Def defs[1024];
static int ndefs = 0;

static Term* copy_term(Term* t) {
  if (!t) return NULL;
  return term_alloc(t->type, t->name, copy_term(t->left), copy_term(t->right));
}

static Term* expand_defs(Term* t) {
  if (!t) return NULL;
  if (t->type == 0) {
    for (int i = 0; i < ndefs; i++)
      if (strcmp(t->name, defs[i].name) == 0) {
        Term* c = copy_term(defs[i].term);
        free(t);
        return expand_defs(c);
      }
    return t;
  }
  if (t->type == 1) { t->left = expand_defs(t->left); return t; }
  if (t->type == 2) { t->left = expand_defs(t->left); t->right = expand_defs(t->right); return t; }
  if (t->type == 100) { t->left = expand_defs(t->left); return t; }
  return t;
}

static void load_definitions(const char* src) {
  const char* saved_input = g_input;
  int saved_pos = g_pos;
  g_input = src; g_pos = 0;
  while (1) {
    parse_skip_ws();
    if (!g_input[g_pos]) break;
    Term* t = parse_term();
    if (!t) break;
    if (t->type == 100) {
      t->left = expand_defs(t->left);
      if (ndefs < 1024) {
        defs[ndefs].term = t->left;
        CPY_NAME(defs[ndefs].name, t->name);
        ndefs++;
      }
      free(t);
    } else {
      term_free(t);
    }
  }
  g_input = saved_input; g_pos = saved_pos;
}

static void load_file(const char* path) {
  FILE* f = fopen(path, "r");
  if (!f) { printf(":load: cannot open %s\n", path); return; }
  fseek(f, 0, SEEK_END);
  long fsize = ftell(f);
  if (fsize <= 0) { fclose(f); return; }
  rewind(f);
  char* buf = malloc(fsize + 1);
  if (!buf) { fclose(f); return; }
  fread(buf, 1, fsize, f);
  fclose(f);
  buf[fsize] = 0;
  load_definitions(buf);
  free(buf);
}

static void repl(void) {
  load_definitions(std_src);
  char buf[4096];
  printf("Lin: Non-Abelian Scope Gauge Optimal Reduction Engine\n");
  printf("     (:q to quit, :load <file>, :goi <expr>)\n\n");
  while (1) {
    printf("lin> "); fflush(stdout);
    if (!fgets(buf, sizeof(buf), stdin)) break;
    size_t len = strlen(buf);
    while (len > 0 && (buf[len-1]=='\n'||buf[len-1]=='\r')) buf[--len]=0;
    if (len == 0) continue;
    if (strcmp(buf, ":q") == 0 || strcmp(buf, ":quit") == 0) break;

    if (strncmp(buf, ":load ", 6) == 0) { load_file(buf + 6); continue; }

    if (strncmp(buf, ":goi ", 5) == 0) {
      g_input = buf + 5; g_pos = 0;
      Term* t = parse_term();
      if (t) {
        Net* n = compile(t);
        int64_t d = goi_det(n);
        reduce(n, MAX_STEPS);
        printf("det(2I - sigma*M) = %ld, steps = %d, active = %d\n",
               (long)d, n->steps, n->active_top / 2);
        free(n->tag); free(n->wire); free(n->scope); free(n->name); free(n->active); free(n);
      }
      term_free(t); continue;
    }

    g_input = buf; g_pos = 0;
    Term* t = parse_term();
    if (!t) { printf("parse error\n"); continue; }

    if (t->type == 100) {
      t->left = expand_defs(t->left);
      if (ndefs < 1024) {
        defs[ndefs].term = t->left;
        CPY_NAME(defs[ndefs].name, t->name);
        ndefs++;
        printf("defined %s\n", t->name);
      }
      free(t);
      continue;
    }

    t = expand_defs(t);
    Net* net = compile(t);
    term_free(t);
    reduce(net, MAX_STEPS);
    printf("=> "); readback(net, stdout); printf("\n");
    free(net->tag); free(net->wire); free(net->scope); free(net->name); free(net->active); free(net);
  }
}

int main(int argc, char** argv) {
  if (argc > 1) {
    load_definitions(std_src);
    load_file(argv[1]);
    return 0;
  }
  repl(); return 0;
}