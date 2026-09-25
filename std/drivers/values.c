/* ============================================================================
 * values.c -- value STORAGE for a net, as a driver.
 *
 * The core reduces and shares.  What a value is stored as, and which table holds
 * it, is not the core's business: this driver declares the DT_FLOAT domain and
 * supplies the storage behind its boxes.  The box ITSELF stays net structure --
 * a BOXED INDEX over the four tags, built with the core's generic
 * `net_box_index` and read with `net_peel_index` -- so the net remains the only
 * authority and a program without this driver loaded is still a valid program
 * (it just cannot build a float box, and says so once).  The box's shape is its
 * own (LIN_ENC_BOX), so a float and the NUMBER its index encodes are different
 * nets: nothing about a node says which domain it belongs to, and readback has
 * to be able to tell a box from a numeral when the caller states no type.
 *
 * THE TABLE IS PROCESS-WIDE ON PURPOSE, and the reason is a property of the net,
 * not a shortcut.  A box's index is BAKED INTO ITS SPINE, and ct_splice copies a
 * precompiled net node by node, so a per-net table would leave a spliced box
 * indexing the destination net's table -- the wrong number, silently.  Indices
 * are therefore allocated from one process-wide sequence and never reused.
 *
 * What the old core-side design got wrong was the other half: loading an artifact
 * REPLACED the table, so two artifacts alive in one process clobbered each other,
 * and `2.0` and `144.0` could print the same value.  Loading here APPENDS, which
 * is what makes a shared table sound; the artifact carries the entries it added
 * and they keep their indices.
 *
 * This driver deliberately has no claim/reduce: it is a provider, not a strategy,
 * which is also why it is registered with LIN_CAP_PROVIDER -- `(set_driver ...)`
 * selects a strategy and must not drop storage the runtime depends on.
 * ==========================================================================*/
#include "../../src/lin.h"
#include <stdlib.h>
#include <string.h>

static double *tab;
static int ntab, ctab;

static int reserve(int need) {
  if (need <= ctab) return 1;
  int c = ctab ? ctab : 64;
  while (c < need) c *= 2;
  double *t = realloc(tab, (size_t)c * sizeof(double));
  if (!t) return 0;
  tab = t; ctab = c;
  return 1;
}

/* Append entries, keeping every existing index valid: an index already baked into a spine (or into
   a spliced one) must keep meaning what it meant. */
static int append(const double *d, int n) {
  if (n <= 0) return ntab;
  if (!reserve(ntab + n)) return -1;
  int first = ntab;
  memcpy(tab + ntab, d, (size_t)n * sizeof(double));
  ntab += n;
  return first;
}

static Port f_box(Net *n, void *st, const Val *v) {
  (void)st;
  double d;
  memcpy(&d, &v->iv, 8);
  int idx = append(&d, 1);
  if (idx < 0) return (Port){-1, 0};
  return net_box_index(n, idx);
}

static int f_unbox(Net *n, void *st, Port p, Val *v) {
  (void)st;
  long idx = net_peel_index(n, p);
  if (idx < 0 || idx >= ntab) return 0;
  double d = tab[idx];
  memcpy(&v->iv, &d, 8);
  v->kind = 4;
  return 1;
}

/* The entries this net added, so an artifact carries its own floats. */
static int f_save(Net *n, void *st, void **blob, size_t *len) {
  (void)n; (void)st;
  if (ntab <= 0) return 0;
  double *b = malloc((size_t)ntab * sizeof(double));
  if (!b) return 0;
  memcpy(b, tab, (size_t)ntab * sizeof(double));
  *blob = b;
  *len = (size_t)ntab * sizeof(double);
  return 1;
}

/* Entries resume their ORIGINAL indices: a box's index is baked into its spine, so an artifact's
   table is only correct at the offsets its net already names.  Loading therefore writes at those
   offsets rather than appending -- appending would leave every box in a second artifact pointing
   one slot off, which is a wrong number rather than a failure.

   A collision (the process already holds a different value at an index this artifact needs) is
   reported, not hidden: two artifacts built in separate processes both number their boxes from 0,
   so a process that runs both is genuinely ambiguous, and the old design answered that by silently
   clobbering.  The proper fix is for a splice to bring state with it (a `nodes_spliced`
   notification would let a provider rebase), which is a larger ABI question than this migration. */
static int f_load(Net *n, void *st, const void *blob, size_t len) {
  (void)n; (void)st;
  const double *d = (const double *)blob;
  int count = (int)(len / sizeof(double));
  if (count <= 0) return 1;
  if (!reserve(count)) return 0;
  static int warned;
  for (int i = 0; i < count; i++) {
    if (i < ntab && tab[i] != d[i] && !warned) {
      warned = 1;
      fprintf(stderr, "lin: value table conflict at index %d: this artifact wants %g, the process "
                      "already holds %g -- boxes from whichever artifact is not running now will "
                      "read the wrong value\n", i, d[i], tab[i]);
    }
    tab[i] = d[i];
  }
  if (count > ntab) ntab = count;
  return 1;
}

LinDriver lin_values_driver;
static void __attribute__((constructor)) values_load(void) {
  static int registered = 0;
  if (registered) return;
  registered = 1;
  lin_driver_add(&lin_values_driver);
}

LinDriver lin_values_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "values", .description = "value storage for the DT_FLOAT domain (net structure stays in the core)",
  .caps = LIN_CAP_PROVIDER, .priority = 0,
  .wants = LIN_WANT_VALUES | LIN_WANT_CARRY,
  .domains = 1ull << DT_FLOAT,
  .val_box = f_box, .val_unbox = f_unbox,
  .carry_save = f_save, .carry_load = f_load,
};
