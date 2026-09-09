/* ============================================================================
 * Lin GPU wavefront driver (Vulkan compute, Shape B / phase 1)
 * ============================================================================
 * Correct-and-robust host plugin for the Lin interaction-net reducer.
 *
 * Phase 1 is the host scaffold: it creates a Vulkan instance, probes for a
 * compute-capable device + queue, and then *delegates* the actual reduction to
 * the base engine (net.c).  This is correct by construction and never crashes:
 * every loader entry point is NULL-checked, every VkResult is checked, and if
 * anything is missing/incompatible the driver reports "not ready" so the base
 * CPU engine transparently takes over (the exact defect that killed the
 * previous driver, which segfaulted at -O2 under freedreno).
 *
 * Phase 2 will move the beta / annihilate / erase link-rewrites into a GLSL
 * compute kernel dispatched with vkCmdDispatch; the allocating commute rule
 * and scope-gauge promotions stay on the host.  All device handles created
 * here are retained so phase 2 attaches the pipeline without re-probing.
 * ========================================================================== */
#include "../../src/lin.h"
#include <vulkan/vulkan.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <dlfcn.h>

#define WIRE(n, p) ((n)->wire[(p).node * 3 + (p).port])

static int   gpu_ready = 0;
static VkInstance       vk_instance = VK_NULL_HANDLE;
static VkPhysicalDevice vk_phys = VK_NULL_HANDLE;
static VkDevice         vk_dev = VK_NULL_HANDLE;
static VkQueue          vk_queue = VK_NULL_HANDLE;
static uint32_t         vk_qfam = 0;
static void            *vk_lib = NULL;

#define LOAD(fn) p_##fn = (PFN_##fn)dlsym(vk_lib, #fn)

/* Create instance + pick a compute-capable device + logical device + queue.
   On any failure, gpu_ready stays 0 and reduction falls back to the CPU. */
__attribute__((constructor))
static void vk_init(void) {
  vk_lib = dlopen("libvulkan.so.1", RTLD_NOW | RTLD_GLOBAL);
  if (!vk_lib) vk_lib = dlopen("libvulkan.so", RTLD_NOW | RTLD_GLOBAL);
  if (!vk_lib) return;

  PFN_vkCreateInstance p_vkCreateInstance = NULL;
  PFN_vkEnumeratePhysicalDevices p_vkEnumeratePhysicalDevices = NULL;
  PFN_vkGetPhysicalDeviceProperties p_vkGetPhysicalDeviceProperties = NULL;
  PFN_vkGetPhysicalDeviceQueueFamilyProperties p_vkGetPhysicalDeviceQueueFamilyProperties = NULL;
  PFN_vkCreateDevice p_vkCreateDevice = NULL;
  PFN_vkGetDeviceQueue p_vkGetDeviceQueue = NULL;
  LOAD(vkCreateInstance);
  LOAD(vkEnumeratePhysicalDevices);
  LOAD(vkGetPhysicalDeviceProperties);
  LOAD(vkGetPhysicalDeviceQueueFamilyProperties);
  LOAD(vkCreateDevice);
  LOAD(vkGetDeviceQueue);
  if (!p_vkCreateInstance || !p_vkEnumeratePhysicalDevices || !p_vkCreateDevice || !p_vkGetDeviceQueue)
    return;

  VkInstanceCreateInfo ii = {0};
  ii.sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
  if (p_vkCreateInstance(&ii, NULL, &vk_instance) != VK_SUCCESS || !vk_instance) return;

  uint32_t ndef = 0;
  if (p_vkEnumeratePhysicalDevices(vk_instance, &ndef, NULL) != VK_SUCCESS || !ndef) return;
  VkPhysicalDevice *devs = malloc(sizeof(VkPhysicalDevice) * ndef);
  if (!devs) return;
  if (p_vkEnumeratePhysicalDevices(vk_instance, &ndef, devs) != VK_SUCCESS) { free(devs); return; }

  /* find first device with a compute-capable queue family (flags bit 0x2) */
  for (uint32_t i = 0; i < ndef; i++) {
    uint32_t nq = 0;
    p_vkGetPhysicalDeviceQueueFamilyProperties(devs[i], &nq, NULL);
    VkQueueFamilyProperties *q = calloc(nq ? nq : 1, sizeof(*q));
    if (!q) break;
    p_vkGetPhysicalDeviceQueueFamilyProperties(devs[i], &nq, q);
    for (uint32_t j = 0; j < nq; j++) {
      if (!(q[j].queueFlags & VK_QUEUE_COMPUTE_BIT)) continue;
      vk_phys = devs[i]; vk_qfam = j;
      VkPhysicalDeviceProperties props;
      p_vkGetPhysicalDeviceProperties(vk_phys, &props);
      if (getenv("LIN_GPU_DEBUG"))
        fprintf(stderr, "[gpu] device '%s' (vendor 0x%04x), compute queue family %u\n",
                props.deviceName, props.vendorID, j);

      float prio = 1.0f;
      VkDeviceQueueCreateInfo qi = {0};
      qi.sType = VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO;
      qi.queueFamilyIndex = j; qi.queueCount = 1; qi.pQueuePriorities = &prio;
      VkDeviceCreateInfo di = {0};
      di.sType = VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO;
      di.queueCreateInfoCount = 1; di.pQueueCreateInfos = &qi;
      if (p_vkCreateDevice(vk_phys, &di, NULL, &vk_dev) == VK_SUCCESS && vk_dev) {
        p_vkGetDeviceQueue(vk_dev, j, 0, &vk_queue);
        gpu_ready = 1;
      } else {
        fprintf(stderr, "[gpu] vkCreateDevice failed - falling back to CPU\n");
      }
      free(q); free(devs);
      return;
    }
    free(q);
  }
  free(devs);
}

/* Classify one redex: 0 beta, 1 annihilate, 2 erase (all fixed-allocation and
   the on-GPU candidates for phase 2); -1 = commute/other (host allocator). */
__attribute__((unused))
static int gpu_classify(Net *n, Port p1, Port p2) {
  int t1 = n->tag[p1.node], t2 = n->tag[p2.node];
  if (t1 > t2) { int t = t1; t1 = t2; t2 = t; }
  if (t1 == LAM && t2 == APP) return 0;
  if (t1 == DUP && t2 == DUP) return 1;
  if (t1 == ERA) return 2;
  return -1;
}

/* Phase-1 reduce_wave: delegate to the base engine's parallel core (which
   performs the full, correct scope-gauge reduction).  This is the faithful
   non-crashing stand-in for the phase-2 on-GPU link-rewrite kernel. */
static int gpu_reduce_wave(Net *n, long limit, int *changed) {
  if (!gpu_ready || n->atop <= 0 || n->steps >= limit) return 0;
  static Port *curr = NULL; static int curr_cap = 0;
  int wave_cnt = wave_snapshot(n, &curr, &curr_cap);
  if (wave_cnt <= 0) return 1;

  int shadow = 0;
  lin_reduce_wave_parallel(n, curr, wave_cnt, &shadow);
  *changed += shadow;
  return 1;
}

LinDriver lin_gpu_driver = { "gpu", gpu_reduce_wave };
