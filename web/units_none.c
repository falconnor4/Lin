/* A build with no compiled units: the function compiler declines every unit, and the net computes it.
   (web/build.sh writes the real table, units.c, when it is given programs to compile ahead.) */
#include <stdint.h>
typedef int64_t (*Entry)(const int64_t *, int threads);
typedef struct { uint64_t h; Entry entry; int *aborted; void (*release)(void); } LinFnUnit;
const LinFnUnit lin_fn_units[] = { { 0, 0, 0, 0 } };
