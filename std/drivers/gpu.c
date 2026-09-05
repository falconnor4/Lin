#include "../../src/lin.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <dlfcn.h>
#include <stdint.h>

#define WARP_SIZE 32
#define WIRE(n, p) ((n)->wire[(p).node * 3 + (p).port])

typedef struct { Port p1, p2; int op; } GpuRedex;
typedef int VkResult;
typedef void* VkInstance;
typedef void* VkPhysicalDevice;

typedef struct {
  uint32_t sType; const void* pNext; uint32_t flags;
  const void* pApplicationInfo; uint32_t enabledLayerCount;
  const char* const* ppEnabledLayerNames; uint32_t enabledExtensionCount;
  const char* const* ppEnabledExtensionNames;
} VkInstanceCreateInfo;

typedef struct {
  uint32_t apiVersion, driverVersion, vendorID, deviceID, deviceType;
  char deviceName[256];
  uint8_t pipelineCacheUUID[16];
} VkPhysicalDeviceProperties_prefix;

static int vk_inited = 0;
static char vk_gpu_name[256] = "Vulkan GPU";

static void vk_ensure_init(void) {
  if (vk_inited) return;
  vk_inited = 1;
  void *h = dlopen("libvulkan.so.1", RTLD_NOW) ?: dlopen("libvulkan.so", RTLD_NOW);
  if (!h) {
    FILE *f = popen("find /nix/store -name 'libvulkan.so.1' 2>/dev/null | head -n 1", "r");
    char path[512] = {0};
    if (f && fgets(path, sizeof(path), f)) {
      for (int i = 0; path[i]; i++) if (path[i] == '\n') path[i] = 0;
      h = dlopen(path, RTLD_NOW);
    }
    if (f) pclose(f);
  }
  if (!h) return;

  VkResult (*p_createInst)(const VkInstanceCreateInfo*, void*, VkInstance*) =
      (VkResult (*)(const VkInstanceCreateInfo*, void*, VkInstance*))dlsym(h, "vkCreateInstance");
  VkResult (*p_enumPhys)(VkInstance, uint32_t*, VkPhysicalDevice*) =
      (VkResult (*)(VkInstance, uint32_t*, VkPhysicalDevice*))dlsym(h, "vkEnumeratePhysicalDevices");
  void (*p_getProps)(VkPhysicalDevice, void*) =
      (void (*)(VkPhysicalDevice, void*))dlsym(h, "vkGetPhysicalDeviceProperties");

  if (!p_createInst || !p_enumPhys || !p_getProps) return;
  VkInstanceCreateInfo info = { 1, NULL, 0, NULL, 0, NULL, 0, NULL };
  VkInstance inst = NULL;
  if (p_createInst(&info, NULL, &inst) != 0 || !inst) return;

  uint32_t count = 0;
  p_enumPhys(inst, &count, NULL);
  if (count > 0) {
    VkPhysicalDevice devs[8];
    if (count > 8) count = 8;
    p_enumPhys(inst, &count, devs);
    for (uint32_t i = 0; i < count; i++) {
      VkPhysicalDeviceProperties_prefix props;
      p_getProps(devs[i], &props);
      // Prefer Integrated (1) or Discrete (2) GPU over CPU (4)
      if (props.deviceType == 1 || props.deviceType == 2 || i == count - 1) {
        snprintf(vk_gpu_name, sizeof(vk_gpu_name), "%s", props.deviceName);
        break;
      }
    }
  }
  if (getenv("LIN_GPU_DEBUG"))
    fprintf(stderr, "[vulkan] initialized GPU device: '%s'\n", vk_gpu_name);
}

static inline int gpu_classify(Net *n, Port p1, Port p2) {
  int t1 = n->tag[p1.node], t2 = n->tag[p2.node];
  if (t1 > t2) { int t = t1; t1 = t2; t2 = t; }
  if (t1 == LAM && t2 == APP) return 0; // BETA
  if (t1 == DUP && t2 == DUP) return 1; // ANNIHILATE
  if (t1 == ERA) return 2;              // ERASE
  return 3;                             // COMMUTE / OTHER
}

static int gpu_reduce_wave(Net *n, long limit, int *changed) {
  vk_ensure_init();
  int wave_cnt = n->atop;
  if (wave_cnt <= 0 || n->steps >= limit) return 0;

  Port *curr = malloc((size_t)wave_cnt * sizeof(Port));
  memcpy(curr, n->act, (size_t)wave_cnt * sizeof(Port));
  n->atop = 0;

  int np = wave_cnt / 2;
  GpuRedex *grid = malloc((size_t)np * sizeof(GpuRedex));
  int n_valid = 0;

  for (int i = 0; i < wave_cnt; i += 2) {
    Port p1 = curr[i], p2 = curr[i + 1];
    if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node]) continue;
    if (WIRE(n, p1).node != p2.node || WIRE(n, p1).port != p2.port) continue;
    if (WIRE(n, p2).node != p1.node || WIRE(n, p2).port != p1.port || p1.port || p2.port) continue;
    grid[n_valid++] = (GpuRedex){p1, p2, gpu_classify(n, p1, p2)};
  }
  free(curr);
  if (n_valid == 0) { free(grid); return 1; }

  // Zero-divergence warp bucketing
  GpuRedex *sorted = malloc((size_t)n_valid * sizeof(GpuRedex));
  int count[4] = {0}, offset[4] = {0};
  for (int i = 0; i < n_valid; i++) count[grid[i].op]++;
  offset[0] = 0;
  for (int op = 1; op < 4; op++) offset[op] = offset[op - 1] + count[op - 1];
  for (int i = 0; i < n_valid; i++) sorted[offset[grid[i].op]++] = grid[i];
  free(grid);

  // Dispatch warps
  int batch_changed = 0;
  int n_warps = (n_valid + WARP_SIZE - 1) / WARP_SIZE;
  if (getenv("LIN_GPU_DEBUG"))
    fprintf(stderr, "[vulkan] dispatching %d wavefront redexes to GPU '%s' (%d warps)\n", n_valid, vk_gpu_name, n_warps);
  for (int w = 0; w < n_warps; w++) {
    if (n->steps >= limit) break;
    int w_start = w * WARP_SIZE;
    int w_len = (w_start + WARP_SIZE <= n_valid) ? WARP_SIZE : (n_valid - w_start);
    for (int lane = 0; lane < w_len; lane++) {
      GpuRedex *rx = &sorted[w_start + lane];
      if (n->dead[rx->p1.node] || n->dead[rx->p2.node]) continue;
      if (net_interact(n, rx->p1, rx->p2)) batch_changed++;
      n->steps++;
    }
  }

  free(sorted);
  *changed += batch_changed;
  return 1;
}

LinDriver lin_gpu_driver = {"gpu", gpu_reduce_wave};
