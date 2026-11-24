/* The plugins a static build links in (see LIN_PLUGIN_INIT in src/lin.h).  Each starts when a program first asks
   for it by name -- `(set_driver "readback")`, the std's own loads -- exactly when a shared object would be
   opened.  Not here: native (it compiles with a C compiler as the program runs) and gpu (Vulkan).  Linden, the game
   engine (examples/linden), is: a program's `(load_lib linden.plugin)` names it by its file, and that starts it. */
#include "../src/lin.h"
extern LinDriver lin_arith_driver, lin_readback_driver, lin_text_driver, lin_simd_driver, lin_fn_driver, lin_linden_driver;
void lin_plugin_init_arith(void); void lin_plugin_init_readback(void); void lin_plugin_init_text(void);
void lin_plugin_init_simd(void); void lin_plugin_init_fn(void); void lin_plugin_init_linden(void);
const LinStaticPlugin lin_static_plugins[] = {
  { "arith", lin_plugin_init_arith, &lin_arith_driver },
  { "readback", lin_plugin_init_readback, &lin_readback_driver },
  { "text", lin_plugin_init_text, &lin_text_driver },
  { "simd", lin_plugin_init_simd, &lin_simd_driver },
  { "fn", lin_plugin_init_fn, &lin_fn_driver },
  { "linden", lin_plugin_init_linden, &lin_linden_driver },
  { NULL, NULL, NULL },
};
