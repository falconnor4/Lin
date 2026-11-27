/* ============================================================================
 * Lin GPU wavefront driver (Vulkan compute, Shape B)
 * ============================================================================
 * Reduces the fixed-allocation interaction rules on-device:
 *   beta (LAM x APP), annihilate (DUP x DUP, inline scopes), erase (ERA x *).
 * Uses mapped HOST_VISIBLE|HOST_COHERENT buffers shared with the host net
 * (strategy a) so the kernel rewrites wire[]/dead[] in place and the host
 * reads exactly what the GPU produced.  The allocating commute rule and
 * heap-backed scope gauges are delegated to lin_reduce_wave_parallel.
 *
 * Robustness: every loader entry point NULL-checked, every VkResult checked;
 * on any failure gpu_ready=0 so the base CPU engine takes over transparently.
 * ========================================================================== */
#include "../../src/lin.h"
#include "../runtime/pattern.h"     /* the structural recognisers: what a foldable head IS */
#include "selftest.h"          /* canonical per-wave bit-exact differential (std-wide) */
#include <vulkan/vulkan.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <dlfcn.h>

#define WIRE(n, p) ((n)->wire[(p).node * 3 + (p).port])

static int gpu_ready = 0, pipe_ready = 0, gpu_load_done = 0;
static VkInstance vk_instance; static VkPhysicalDevice vk_phys;
static VkDevice vk_dev; static VkQueue vk_queue; static uint32_t vk_qfam;
static void *vk_lib; static int vk_have64; static uint32_t vk_maxgx, vk_maxgy; static char vk_name[VK_MAX_PHYSICAL_DEVICE_NAME_SIZE];

/* Emit a one-time, NON-SILENT fallback notice: the GPU driver loaded but cannot
   produce a usable on-device reducer, so reduction transparently falls back to
   the base CPU engine.  Keeping the user informed is the point of this guard —
   without it a missing shader, loader or device is a silent no-op (and, until
   now, the missing-shader case could even segfault in gpu_reduce).  The
   `warning:` prefix is the repo convention that test/run_tests.sh strips via
   `grep -v '^warning'`, so a functional fallback still passes the suite. */
static int gpu_warned = 0;
static const char *vk_why;   /* why the net reducer is off, said when it is first asked to reduce (gpu_claim): a program
                                that only runs kernels (see KERNELS) loads this driver too, and must hear nothing */
static void gpu_warn(const char *why) {
  if (!vk_why) vk_why = why;
  if (!gpu_load_done) return;
  if (gpu_warned) return;
  gpu_warned = 1;
  /* Informational diagnostic to stderr (never stdout): the value-output stream
     a test harness reads (test/run_tests.sh captures stdout only) must stay
     clean even though gpu.so is dlopen'd mid-expression by set_driver. */
  fprintf(stderr, "warning: GPU driver is unavailable (%s) - reducing on the base CPU engine\n", why);
}

static struct Buf { VkBuffer b; VkDeviceMemory m; VkDeviceSize sz; void *map; }
  g_tags, g_wires, g_deads, g_scopes, g_redex;

static VkPipelineLayout vk_playout; static VkPipeline vk_pipe;
static VkDescriptorSetLayout vk_dsl; static VkDescriptorPool vk_dp; static VkDescriptorSet vk_ds;
static VkCommandPool vk_cp; static VkCommandBuffer vk_cb;

#define LOAD(fn) p_##fn = (PFN_##fn)dlsym(vk_lib, #fn)
static PFN_vkGetPhysicalDeviceMemoryProperties p_vkPMemProps;
static PFN_vkCreateInstance p_vkCreateInstance;
static PFN_vkEnumeratePhysicalDevices p_vkEnumeratePhysicalDevices;
static PFN_vkGetPhysicalDeviceProperties p_vkGetPhysicalDeviceProperties;
static PFN_vkGetPhysicalDeviceQueueFamilyProperties p_vkGetPhysicalDeviceQueueFamilyProperties;
static PFN_vkCreateDevice p_vkCreateDevice;
static PFN_vkGetDeviceQueue p_vkGetDeviceQueue;
static PFN_vkCreateShaderModule p_vkCreateShaderModule;
static PFN_vkCreateDescriptorSetLayout p_vkCreateDescriptorSetLayout;
static PFN_vkCreatePipelineLayout p_vkCreatePipelineLayout;
static PFN_vkCreateComputePipelines p_vkCreateComputePipelines;
static PFN_vkCreateDescriptorPool p_vkCreateDescriptorPool;
static PFN_vkAllocateDescriptorSets p_vkAllocateDescriptorSets;
static PFN_vkUpdateDescriptorSets p_vkUpdateDescriptorSets;
static PFN_vkCreateCommandPool p_vkCreateCommandPool;
static PFN_vkAllocateCommandBuffers p_vkAllocateCommandBuffers;
static PFN_vkBeginCommandBuffer p_vkBeginCommandBuffer;
static PFN_vkCmdBindPipeline p_vkCmdBindPipeline;
static PFN_vkCmdBindDescriptorSets p_vkCmdBindDescriptorSets;
static PFN_vkCmdPushConstants p_vkCmdPushConstants;
static PFN_vkCmdDispatch p_vkCmdDispatch;
static PFN_vkEndCommandBuffer p_vkEndCommandBuffer;
static PFN_vkQueueSubmit p_vkQueueSubmit;
static PFN_vkQueueWaitIdle p_vkQueueWaitIdle;
static PFN_vkCreateBuffer p_vkCreateBuffer;
static PFN_vkGetBufferMemoryRequirements p_vkGetBufferMemoryRequirements;
static PFN_vkAllocateMemory p_vkAllocateMemory;
static PFN_vkBindBufferMemory p_vkBindBufferMemory;
static PFN_vkMapMemory p_vkMapMemory;
static PFN_vkDestroyBuffer p_vkDestroyBuffer; static PFN_vkFreeMemory p_vkFreeMemory; static PFN_vkCmdPipelineBarrier p_vkCmdPipelineBarrier;
static PFN_vkCreateFence p_vkCreateFence; static PFN_vkWaitForFences p_vkWaitForFences; static PFN_vkResetFences p_vkResetFences;
static int vk_devok;

static int g_mem_type = -1;
static int mem_type_for(uint32_t bits) {
  /* validity of a cached type depends on THIS buffer's memoryTypeBits */
  if (g_mem_type >= 0 && (bits & (1u << g_mem_type))) return g_mem_type;
  g_mem_type = -1;
  VkPhysicalDeviceMemoryProperties mp; p_vkPMemProps(vk_phys, &mp);
  VkMemoryPropertyFlags need = VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT;
  for (uint32_t i = 0; i < mp.memoryTypeCount; i++)
    if ((bits & (1u << i)) && (mp.memoryTypes[i].propertyFlags & need) == need) { g_mem_type = (int)i; return g_mem_type; }
  return -1;
}

static int buf_alloc(struct Buf *g, VkDeviceSize sz) {
  g->sz = sz;
  VkBufferCreateInfo bi = {0}; bi.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
  bi.size = sz; bi.usage = VK_BUFFER_USAGE_STORAGE_BUFFER_BIT;
  if (p_vkCreateBuffer(vk_dev, &bi, NULL, &g->b) != VK_SUCCESS || !g->b) return 0;
  VkMemoryRequirements mr; p_vkGetBufferMemoryRequirements(vk_dev, g->b, &mr);
  int mt = mem_type_for(mr.memoryTypeBits); if (mt < 0) return 0;
  VkMemoryAllocateInfo ai = {0}; ai.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
  ai.allocationSize = mr.size; ai.memoryTypeIndex = (uint32_t)mt;
  if (p_vkAllocateMemory(vk_dev, &ai, NULL, &g->m) != VK_SUCCESS) return 0;
  p_vkBindBufferMemory(vk_dev, g->b, g->m, 0);
  return p_vkMapMemory(vk_dev, g->m, 0, sz, 0, &g->map) == VK_SUCCESS;
}

/* Read reduce.spv from <LIN_STD_DIR>/drivers/reduce.spv (or cwd fallback). */
static size_t load_spv(const uint32_t **out) {
  static uint32_t *words; static size_t nw;
  if (words) { if (out) *out = words; return nw; }
  const char *dir = getenv("LIN_STD_DIR");
  char path[4096];
  snprintf(path, sizeof path, "%s/drivers/reduce.spv", dir ? dir : "std");
  FILE *f = fopen(path, "rb"); if (!f) f = fopen("reduce.spv", "rb");
  if (!f) return 0;
  fseek(f, 0, SEEK_END); int64_t sz = ftell(f); fseek(f, 0, SEEK_SET);
  nw = (size_t)sz / 4; words = malloc(sz + 16);
  if (fread(words, 1, (size_t)sz, f) != (size_t)sz) { fclose(f); return 0; }
  fclose(f);
  if (out) *out = words;
  return nw;
}

/* Build the compute pipeline: 5 SSBO descriptor bindings + push constant. */
static void build_pipeline(void) {
  const VkDescriptorSetLayoutBinding binds[5] = {
    {0, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, 1, VK_SHADER_STAGE_COMPUTE_BIT, NULL},
    {1, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, 1, VK_SHADER_STAGE_COMPUTE_BIT, NULL},
    {2, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, 1, VK_SHADER_STAGE_COMPUTE_BIT, NULL},
    {3, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, 1, VK_SHADER_STAGE_COMPUTE_BIT, NULL},
    {4, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, 1, VK_SHADER_STAGE_COMPUTE_BIT, NULL},
  };
  VkDescriptorSetLayoutCreateInfo dli = {0};
  dli.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO;
  dli.bindingCount = 5; dli.pBindings = binds;
  if (getenv("LIN_GPU_DEBUG")) fprintf(stderr, "[gpu] dsl\n");
  if (p_vkCreateDescriptorSetLayout(vk_dev, &dli, NULL, &vk_dsl) != VK_SUCCESS) goto fail;

  VkPushConstantRange pcr = { VK_SHADER_STAGE_COMPUTE_BIT, 0, sizeof(uint32_t) };
  VkPipelineLayoutCreateInfo pli = {0};
  pli.sType = VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO;
  pli.setLayoutCount = 1; pli.pSetLayouts = &vk_dsl;
  pli.pushConstantRangeCount = 1; pli.pPushConstantRanges = &pcr;
  if (getenv("LIN_GPU_DEBUG")) fprintf(stderr, "[gpu] playout\n");
  if (p_vkCreatePipelineLayout(vk_dev, &pli, NULL, &vk_playout) != VK_SUCCESS) goto fail;

  const uint32_t *spv; size_t nw = load_spv(&spv);
  if (getenv("LIN_GPU_DEBUG")) fprintf(stderr, "[gpu] spv nw=%zu\n", nw);
  if (!nw) goto fail;
  VkShaderModuleCreateInfo smi = {0};
  smi.sType = VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO;
  smi.codeSize = (size_t)nw * 4; smi.pCode = spv;
  VkShaderModule smod;
  if (getenv("LIN_GPU_DEBUG")) fprintf(stderr, "[gpu] shader\n");
  if (p_vkCreateShaderModule(vk_dev, &smi, NULL, &smod) != VK_SUCCESS) goto fail;

  VkPipelineShaderStageCreateInfo st = {0};
  st.sType = VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO;
  st.stage = VK_SHADER_STAGE_COMPUTE_BIT; st.module = smod; st.pName = "main";
  VkComputePipelineCreateInfo cpi = {0};
  cpi.sType = VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO;
  cpi.stage = st; cpi.layout = vk_playout;
  if (getenv("LIN_GPU_DEBUG")) fprintf(stderr, "[gpu] pipeline\n");
  if (p_vkCreateComputePipelines(vk_dev, VK_NULL_HANDLE, 1, &cpi, NULL, &vk_pipe) != VK_SUCCESS) goto fail;

  VkDescriptorPoolSize dps = { VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, 5 };
  VkDescriptorPoolCreateInfo dpi = {0};
  dpi.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
  dpi.maxSets = 1; dpi.poolSizeCount = 1; dpi.pPoolSizes = &dps;
  if (getenv("LIN_GPU_DEBUG")) fprintf(stderr, "[gpu] dpool\n");
  if (p_vkCreateDescriptorPool(vk_dev, &dpi, NULL, &vk_dp) != VK_SUCCESS) goto fail;

  VkDescriptorSetAllocateInfo dai = {0};
  dai.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
  dai.descriptorPool = vk_dp; dai.descriptorSetCount = 1; dai.pSetLayouts = &vk_dsl;
  if (getenv("LIN_GPU_DEBUG")) fprintf(stderr, "[gpu] dset\n");
  if (p_vkAllocateDescriptorSets(vk_dev, &dai, &vk_ds) != VK_SUCCESS) goto fail;

  VkCommandPoolCreateInfo cpi2 = {0};
  cpi2.sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO;
  cpi2.queueFamilyIndex = vk_qfam;
  if (getenv("LIN_GPU_DEBUG")) fprintf(stderr, "[gpu] cmdpool\n");
  if (p_vkCreateCommandPool(vk_dev, &cpi2, NULL, &vk_cp) != VK_SUCCESS) goto fail;

  VkCommandBufferAllocateInfo cai = {0};
  cai.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
  cai.commandPool = vk_cp; cai.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
  cai.commandBufferCount = 1;
  if (getenv("LIN_GPU_DEBUG")) fprintf(stderr, "[gpu] cmdbuf\n");
  if (p_vkAllocateCommandBuffers(vk_dev, &cai, &vk_cb) != VK_SUCCESS) goto fail;

  pipe_ready = 1;
  if (getenv("LIN_GPU_DEBUG")) fprintf(stderr, "[gpu] compute pipeline ready\n");
  return;
fail:
  pipe_ready = 0;
}

__attribute__((constructor))
static void vk_init(void) {
  vk_lib = dlopen("libvulkan.so.1", RTLD_NOW | RTLD_GLOBAL);
  if (!vk_lib) vk_lib = dlopen("libvulkan.so", RTLD_NOW | RTLD_GLOBAL);
  if (!vk_lib) { gpu_warn("Vulkan loader (libvulkan.so) not found"); return; }
  LOAD(vkCreateInstance); LOAD(vkEnumeratePhysicalDevices);
  LOAD(vkGetPhysicalDeviceProperties); LOAD(vkGetPhysicalDeviceQueueFamilyProperties);
  LOAD(vkCreateDevice); LOAD(vkGetDeviceQueue);
  p_vkPMemProps = dlsym(vk_lib, "vkGetPhysicalDeviceMemoryProperties");
  if (!p_vkCreateInstance || !p_vkEnumeratePhysicalDevices || !p_vkCreateDevice || !p_vkGetDeviceQueue || !p_vkPMemProps) {
    gpu_warn("Vulkan loader missing required entry points"); return;
  }

  VkInstanceCreateInfo ii = {0}; ii.sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
  if (p_vkCreateInstance(&ii, NULL, &vk_instance) != VK_SUCCESS || !vk_instance) {
    gpu_warn("Vulkan instance creation failed (no ICD / driver?)"); return;
  }

  uint32_t ndef = 0;
  if (p_vkEnumeratePhysicalDevices(vk_instance, &ndef, NULL) != VK_SUCCESS || !ndef) {
    gpu_warn("no Vulkan physical devices enumerated"); return;
  }
  VkPhysicalDevice *devs = malloc(sizeof(VkPhysicalDevice) * ndef);
  if (!devs) return;
  if (p_vkEnumeratePhysicalDevices(vk_instance, &ndef, devs) != VK_SUCCESS) { free(devs); gpu_warn("Vulkan device enumeration failed"); return; }

  for (uint32_t i = 0; i < ndef; i++) {
    uint32_t nq = 0;
    p_vkGetPhysicalDeviceQueueFamilyProperties(devs[i], &nq, NULL);
    VkQueueFamilyProperties *q = calloc(nq ? nq : 1, sizeof(*q));
    if (!q) break;
    p_vkGetPhysicalDeviceQueueFamilyProperties(devs[i], &nq, q);
    for (uint32_t j = 0; j < nq; j++) {
      if (!(q[j].queueFlags & VK_QUEUE_COMPUTE_BIT)) continue;
      vk_phys = devs[i]; vk_qfam = j;
      float prio = 1.0f;
      VkDeviceQueueCreateInfo qi = {0}; qi.sType = VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO;
      qi.queueFamilyIndex = j; qi.queueCount = 1; qi.pQueuePriorities = &prio;
      VkDeviceCreateInfo di = {0}; di.sType = VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO;
      di.queueCreateInfoCount = 1; di.pQueueCreateInfos = &qi;
      VkPhysicalDeviceFeatures have = {0}, want = {0};   /* (the kernels' words are 64-bit integers and doubles) */
      PFN_vkGetPhysicalDeviceFeatures gf = (PFN_vkGetPhysicalDeviceFeatures)dlsym(vk_lib, "vkGetPhysicalDeviceFeatures");
      if (gf) gf(vk_phys, &have);
      want.shaderInt64 = have.shaderInt64; want.shaderFloat64 = have.shaderFloat64; vk_have64 = have.shaderInt64 && have.shaderFloat64;
      di.pEnabledFeatures = &want;
      if (p_vkGetPhysicalDeviceProperties) { VkPhysicalDeviceProperties pr; p_vkGetPhysicalDeviceProperties(vk_phys, &pr); vk_maxgx = pr.limits.maxComputeWorkGroupCount[0]; vk_maxgy = pr.limits.maxComputeWorkGroupCount[1]; snprintf(vk_name, sizeof vk_name, "%s", pr.deviceName); }
      if (p_vkCreateDevice(vk_phys, &di, NULL, &vk_dev) != VK_SUCCESS || !vk_dev) break;
      p_vkGetDeviceQueue(vk_dev, j, 0, &vk_queue);
      if (getenv("LIN_GPU_DEVICE")) gpu_ready = 1;
      else { gpu_ready = 0; gpu_warn("discrete compute accelerator required"); }
      free(q); free(devs);
      goto device_ok;
    }
    free(q);
  }
  free(devs);
  gpu_warn("no Vulkan device with a compute queue found");
  return;
device_ok:
  LOAD(vkCreateShaderModule); LOAD(vkCreateDescriptorSetLayout); LOAD(vkCreatePipelineLayout);
  LOAD(vkCreateComputePipelines); LOAD(vkCreateDescriptorPool); LOAD(vkAllocateDescriptorSets);
  LOAD(vkUpdateDescriptorSets); LOAD(vkCreateCommandPool); LOAD(vkAllocateCommandBuffers);
  LOAD(vkBeginCommandBuffer); LOAD(vkCmdBindPipeline); LOAD(vkCmdBindDescriptorSets);
  LOAD(vkCmdPushConstants); LOAD(vkCmdDispatch); LOAD(vkEndCommandBuffer);
  LOAD(vkQueueSubmit); LOAD(vkQueueWaitIdle); LOAD(vkCreateBuffer);
  LOAD(vkGetBufferMemoryRequirements); LOAD(vkAllocateMemory); LOAD(vkBindBufferMemory); LOAD(vkMapMemory);
  if (getenv("LIN_GPU_DEBUG")) { fprintf(stderr, "[gpu] device ready\n"); }

  LOAD(vkDestroyBuffer); LOAD(vkFreeMemory); LOAD(vkCmdPipelineBarrier); LOAD(vkCreateFence); LOAD(vkWaitForFences); LOAD(vkResetFences);
  vk_devok = 1;
  if (!gpu_ready) return;                /* (the net reducer was not asked for: kernels only, see KERNELS) */
  /* build the compute pipeline now that all device entry points are loaded */
  build_pipeline();
  /* A device was found, but if the compute pipeline (descriptors/shader) could
     not be built we must NOT dispatch on-device: fall back to the CPU engine
     loudly rather than dereference a half-built pipeline (was a segfault). */
  if (!pipe_ready) gpu_warn("Vulkan compute pipeline/shader failed to build");
}

/* Allocate/refresh device buffers sized to the current net. */
static int ensure_buffers(Net *n, int nred) {
  size_t nn = (size_t)n->nn, nredmax = (size_t)nred * 8;
  if (g_tags.sz   < nn*4)     { if (!buf_alloc(&g_tags,   nn*4))     return 0; }
  if (g_wires.sz  < nn*12)    { if (!buf_alloc(&g_wires,  nn*12))    return 0; }
  if (g_deads.sz  < nn*4)     { if (!buf_alloc(&g_deads,  nn*4))     return 0; }
  if (g_scopes.sz < nn*8)     { if (!buf_alloc(&g_scopes, nn*8))     return 0; }
  if (g_redex.sz  < nredmax)  { if (!buf_alloc(&g_redex,  nredmax))  return 0; }
  return 1;
}

/* per-sector usage bitmap: at most one on-GPU redex per 64-node sector */
static unsigned char *gpu_sector_used;
static int gpu_sector_cap;

/* Bit-exact differential check (LIN_GPU_SELFTEST=1): reduce the SAME fixed
   redexes on a host clone of the net and compare wire[]/dead[] against what
   the GPU just wrote into its mapped buffers.  Delegates to the canonical,
   std-wide harness in selftest.h so every device driver shares one oracle. */
static unsigned char *self_deads; static Port *self_wires; static int self_alloc = 0;

static void gpu_selftest(Net *n, int nred) {
  if (!getenv("LIN_GPU_SELFTEST")) return;

  /* decode the packed GPU-committed buffers into the plain wire[]/dead[] layout
     the shared harness expects (same decode the authoritative commit below uses) */
  if (self_alloc < n->nn) {
    self_alloc = n->nn + 64;
    free(self_deads); free(self_wires);
    self_deads = malloc((size_t)self_alloc);
    self_wires = malloc(sizeof(Port) * (size_t)self_alloc * 3);
    if (!self_deads || !self_wires) { free(self_deads); free(self_wires); self_deads=NULL; self_wires=NULL; self_alloc=0; return; }
  }
  uint32_t *gw = (uint32_t *)g_wires.map, *gd = (uint32_t *)g_deads.map;
  for (int i = 0; i < n->nn; i++) {
    self_deads[i] = (unsigned char)gd[i];
    for (int p = 0; p < 3; p++) {
      uint32_t w32 = gw[i*3+p];
      self_wires[i*3+p] = (w32 == 0x3fffffffu) ? (Port){-1,0}
                        : (Port){ (int)(w32 & 0x3fffffff), (int)(w32 >> 30) };
    }
  }

  /* reconstruct the redex Pair list (same encoding the GPU consumed) */
  Port *fp = malloc(sizeof(Port) * (size_t)nred * 2);
  if (!fp) return;
  for (int i = 0; i < nred; i++) {
    uint32_t a = ((uint32_t*)g_redex.map)[i*2], b = ((uint32_t*)g_redex.map)[i*2+1];
    fp[i*2]   = (Port){ (int)(a & 0x3fffffff), (int)(a >> 30) };
    fp[i*2+1] = (Port){ (int)(b & 0x3fffffff), (int)(b >> 30) };
  }
  int bad = lin_selftest_replay(n, fp, nred, self_wires, self_deads, "GPU", "LIN_GPU_SELFTEST");
  free(fp);

  if (bad && getenv("LIN_GPU_SELFTEST_DUMP")) {
    for (int i = 0; i < nred; i++) {
      uint32_t a = ((uint32_t*)g_redex.map)[i*2], b = ((uint32_t*)g_redex.map)[i*2+1];
      fprintf(stderr, "  redex %d: n%d.%d(tag%d) x n%d.%d(tag%d)\n", i,
              (int)(a & 0x3fffffff), (int)(a >> 30), n->tag[a & 0x3fffffff],
              (int)(b & 0x3fffffff), (int)(b >> 30), n->tag[b & 0x3fffffff]);
    }
  }
}

/* A HEAD THE HOST FOLDS: an `_op` head or an `_ffi` closure.  A net carries no label, so the SHAPE
   is the whole of what says which head this is -- the same pair of tests the fold drivers make,
   because this driver has to agree with them about which redexes are theirs.  PURE: `claim` runs
   before any slice exists and must not touch the net. */
static int gpu_foldable_head(const Net *n, int node) {
  LinMatch m;
  if (node < 0 || node >= n->nn || n->dead[node] || n->tag[node] != LAM) return 0;
  if (lin_pat_match((Net *)n, (Port){node, 0}, lin_pat_enc_ffi, LIN_PAT_BUDGET_FOR(n), &m)) return 1;
  return lin_pat_op_head(n, (Port){node, 0}, NULL);
}

/* claim: a fixed-allocation redex (beta, inline-scope annihilate).  Commute /
   heap-scope annihilate / `_ffi` closures are NOT claimed (SIMD claims `_ffi`
   at higher priority; commute is the base engine's). */
static int gpu_claim(const Net *n, Port p1, Port p2) {
  /* A usable device AND a built compute pipeline are both required to handle a
     redex; with either absent we are a pure no-op and the base engine owns the
     wave.  Checking pipe_ready here (not just gpu_ready) prevents claiming a
     redex the driver then cannot dispatch because the shader/pipeline failed. */
  if (!gpu_ready || !pipe_ready) { if (!gpu_load_done) { gpu_load_done = 1; gpu_warn(vk_why ? vk_why : "the device could not be set up"); } return 0; }
  if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node]) return 0;
  /* principal-port validity (mirrors lin_reduce_wave_parallel) */
  if (p1.port || p2.port) return 0;
  if (WIRE(n,p1).node != p2.node || WIRE(n,p1).port != p2.port) return 0;
  if (WIRE(n,p2).node != p1.node || WIRE(n,p2).port != p1.port) return 0;
  int t1 = n->tag[p1.node], t2 = n->tag[p2.node];
  if (t1 > t2) { int t = t1; t1 = t2; t2 = t; Port p = p1; p1 = p2; p2 = p; }
  if (t1 == LAM && t2 == APP) {
    /* The GPU kernel's beta (std/drivers/reduce.comp) ONLY rewires wires — it
       does not fold.  So a LAM x APP redex whose head OR whose applied argument
       is a foldable saturated `_op`/`_ffi` closure must NOT be claimed: the fold
       PRE-EMPTOR (std/drivers/arith.so, priority 5 — ahead of every strategy)
       folds those, including the β-argument edge, into a concrete value, and
       claiming such a redex on-device would beta-reduce instead, leaving a
       different net than the host — the per-wave differential mismatch observed
       under gpu.  Hand them to the pre-emptor. */
    if (gpu_foldable_head(n, p1.node)) return 0;       /* head is a foldable closure */
    /* argument `aa` = APP port 2; a foldable closure argument is eagerly folded
       inside the host's beta (fold_arg), which the kernel cannot replicate */
    Port aa = WIRE(n, ((Port){p2.node, 2}));
    if (aa.node >= 0 && aa.node < n->nn && !n->dead[aa.node]) {
      if (n->tag[aa.node] == LAM) {
        if (gpu_foldable_head(n, aa.node)) return 0;
      } else if (n->tag[aa.node] == APP) {
        Port h = WIRE(n, ((Port){aa.node, 0}));
        if (h.node >= 0 && h.node < n->nn && !n->dead[h.node] && n->tag[h.node] == LAM)
          if (gpu_foldable_head(n, h.node)) return 0;
      }
    }
    return 1;                                                 /* beta */
  }
  /* DUP x DUP: the kernel only annihilates.  With EQUAL gauges that is exactly
     what the base engine does; with differing gauges the base engine *commutes*
     the two fans (Lafont's delta-delta rule), which the kernel does not
     implement, so those redexes must be left to the base engine. */
  if (t1 == DUP && t2 == DUP)
    return scope_eq(n, n->scope[p1.node], n->scope[p2.node]);
  return 0;                                              /* commute / erase */
}

/* reduce: dispatch the (already-claimed) fixed-rule slice on-device, commit,
   and fall back to net_interact for the sector-non-disjoint subset.  The core
   has already routed commute redexes to the base engine. */
static int gpu_reduce(Net *n, Port *redexes, int nred, int64_t limit, int *changed) {
  /* Require a built pipeline: if gpu_ready but pipe_ready is 0 (device found but
     the compute shader/pipeline failed to build, e.g. no reduce.spv), dispatching
     would dereference NULL device objects and segfault.  Fall back to the CPU
     engine instead — gpu_claim already returned 0 in this state, so the base
     engine owns this wave. */
  if (!gpu_ready || !pipe_ready || nred <= 0 || n->steps >= limit) return 0;

  /* reset the per-sector usage bitmap for this wave */
  int nsec = (n->nn + 63) >> 6;
  if (nsec > gpu_sector_cap) { gpu_sector_used = realloc(gpu_sector_used, (size_t)nsec); gpu_sector_cap = nsec; }
  memset(gpu_sector_used, 0, (size_t)nsec);

  if (!ensure_buffers(n, nred)) {
    /* no buffers: host-fallback every fixed redex via net_interact */
    for (int i = 0; i < nred; i++) { if (net_interact(n, redexes[i*2], redexes[i*2+1])) (*changed)++; n->steps++; }
    return nred;
  }

  /* sector-disjoint filter: on-GPU subset vs the rest.  Crucially, the net is
     NOT mutated while collecting the GPU slice: a fallback redex's net_interact
     rewires nodes, and if it shared nodes with a to-dispatch redex the GPU would
     fold a redex whose wire structure no longer matched the claim-time validity
     (and the differential replay) — the per-wave mismatch.  Collect the
     fallback redexes here and re-queue them AFTER the GPU dispatch+commit, so
     the main pipeline resolves them. */
  uint32_t *g = (uint32_t *)g_redex.map;
  int ng = 0;
  Port *fb = NULL; int nfb = 0, fbcap = 0;
  for (int i = 0; i < nred; i++) {
    Port p1 = redexes[i*2], p2 = redexes[i*2+1];
    int u = p1.node, v = p2.node, su = u >> 6, ok = (su == (v >> 6));
    if (ok) {
      int c[4] = { WIRE(n, ((Port){u,1})).node, WIRE(n, ((Port){u,2})).node,
                   WIRE(n, ((Port){v,1})).node, WIRE(n, ((Port){v,2})).node };
      for (int k = 0; k < 4; k++) if (c[k] >= 0 && (c[k] >> 6) != su) { ok = 0; break; }
    }
    if (ok && gpu_sector_used[su]) ok = 0;
    if (ok) {
      gpu_sector_used[su] = 1;
      g[ng*2]   = ((uint32_t)(p1.node & 0x3fffffff)) | (p1.port << 30);
      g[ng*2+1] = ((uint32_t)(p2.node & 0x3fffffff)) | (p2.port << 30);
      ng++;
    } else {
      if (nfb + 2 > fbcap) { fbcap = fbcap ? fbcap * 2 : 128; Port *t = realloc(fb, (size_t)fbcap * sizeof(Port)); if (!t) { free(fb); fb = NULL; nfb = 0; goto gpu_done; } fb = t; }
      fb[nfb++] = p1; fb[nfb++] = p2;
    }
  }

  if (ng > 0) {
    /* upload net arrays into the mapped coherent buffers */
    uint32_t *tags = (uint32_t *)g_tags.map, *deads = (uint32_t *)g_deads.map;
    uint32_t *wires = (uint32_t *)g_wires.map;
    uint64_t *scopes = (uint64_t *)g_scopes.map;
    for (int i = 0; i < n->nn; i++) {
      tags[i] = n->tag[i]; deads[i] = n->dead[i]; scopes[i] = (uint64_t)n->scope[i];
      for (int p = 0; p < 3; p++) {
        Port w = n->wire[i*3+p];
        wires[i*3+p] = w.node < 0 ? 0x3fffffffu : ((uint32_t)(w.node & 0x3fffffff) | (w.port << 30));
      }
    }
    VkDescriptorBufferInfo dbi[5];
    VkBuffer bufs[5] = { g_tags.b, g_wires.b, g_deads.b, g_scopes.b, g_redex.b };
    for (int i = 0; i < 5; i++) { dbi[i].buffer = bufs[i]; dbi[i].offset = 0; dbi[i].range = VK_WHOLE_SIZE; }
    VkWriteDescriptorSet wds[5]; memset(wds, 0, sizeof(wds));
    for (int i = 0; i < 5; i++) {
      wds[i].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
      wds[i].dstSet = vk_ds; wds[i].dstBinding = i; wds[i].descriptorCount = 1;
      wds[i].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; wds[i].pBufferInfo = &dbi[i];
    }
    p_vkUpdateDescriptorSets(vk_dev, 5, wds, 0, NULL);

    VkCommandBufferBeginInfo bi = {0}; bi.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
    p_vkBeginCommandBuffer(vk_cb, &bi);
    p_vkCmdBindPipeline(vk_cb, VK_PIPELINE_BIND_POINT_COMPUTE, vk_pipe);
    p_vkCmdBindDescriptorSets(vk_cb, VK_PIPELINE_BIND_POINT_COMPUTE, vk_playout, 0, 1, &vk_ds, 0, NULL);
    uint32_t nrc = (uint32_t)ng;
    p_vkCmdPushConstants(vk_cb, vk_playout, VK_SHADER_STAGE_COMPUTE_BIT, 0, sizeof(nrc), &nrc);
    p_vkCmdDispatch(vk_cb, (ng + 63) / 64, 1, 1);
    p_vkEndCommandBuffer(vk_cb);
    VkSubmitInfo si = {0}; si.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    si.commandBufferCount = 1; si.pCommandBuffers = &vk_cb;
    p_vkQueueSubmit(vk_queue, 1, &si, VK_NULL_HANDLE);
    p_vkQueueWaitIdle(vk_queue);

    if (getenv("LIN_GPU_DEBUG"))
      fprintf(stderr, "[gpu] dispatched %d redexes on device\n", ng);
    gpu_selftest(n, ng);

    /* authoritative commit: GPU rewrites become the host net's ground truth */
    uint32_t *gw = (uint32_t *)g_wires.map, *gd = (uint32_t *)g_deads.map;
    for (int i = 0; i < n->nn; i++) {
      n->dead[i] = (unsigned char)gd[i];
      for (int p = 0; p < 3; p++) {
        uint32_t w32 = gw[i*3+p];
        n->wire[i*3+p] = (w32 == 0x3fffffffu) ? (Port){-1,0}
                       : (Port){ (int)(w32 & 0x3fffffff), (int)(w32 >> 30) };
      }
    }
    *changed += ng;
    n->steps += ng;
  }

gpu_done:
  /* Host-fallback the sector-conflicted redexes on the (GPU-committed) net.
     There is no parked-redex set to drain any more: the core holds no deferral
     state, and the fold pre-emptor (std/drivers/arith.so) claims a closure ONLY
     when its operands are already concrete, so a `_op`/`_ffi` closure with a
     still-computing operand is never claimed and the core simply β-reduces its
     pure-Lin body.  Nothing can be stranded here. */
  for (int i = 0; i + 1 < nfb; i += 2) {
    if (!n->dead[fb[i].node] && !n->dead[fb[i+1].node] && net_interact(n, fb[i], fb[i+1])) (*changed)++;
    n->steps++;
  }
  free(fb);

  /* Rebuild the active list from the committed net (mirrors net_reduce's gc
     tail): enqueue every principal port directed at a higher-indexed node. */
  for (int i = 1; i < n->nn; i++)
    if (!n->dead[i] && n->wire[i*3].port == 0 && n->wire[i*3].node > i && n->wire[i*3].node >= 0)
      lin_enqueue(n, (Port){i, 0}, n->wire[i*3]);

  return nred;
}

/* ============================================================================
 * KERNELS: a compiled loop's steps, run on the device (std/drivers/fn.c, THE GPU).
 * ============================================================================
 * fn writes a loop's per-state function as GLSL -- the program's own Lin, translated -- and hands this driver the
 * states (n rows of na words) to run it on.  The source is compiled once to SPIR-V by glslangValidator and kept
 * in the native cache under its hash; its pipeline is kept for the run.  A vector argument (a flat vector the loop
 * reads, the same one in every row) is laid out once in a third buffer, as [len, elements...], and the row's word
 * becomes its offset there.  Any failure answers 0, and the loop computes on the CPU what it would have: the
 * device is a way of computing the same thing faster, never a requirement. */
#include <unistd.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <pthread.h>
typedef struct { uint64_t key; VkPipeline pipe; int bad; } Kern;
static Kern *kerns; static int nkern, ckern;
static VkDescriptorSetLayout k_dsl; static VkPipelineLayout k_pl; static VkDescriptorPool k_dp; static VkDescriptorSet k_ds;
static VkCommandPool k_cp; static VkCommandBuffer k_cb; static VkFence k_fence;
static struct Buf k_st, k_out, k_vec;
static int k_state;   /* 0 not yet, 1 ready, 2 not available */
static int k_dbg(void) { static int d = -1; if (d < 0) d = getenv("LIN_GPU_DEBUG") != NULL; return d; }
static void buf_free(struct Buf *g) {
  if (g->b) p_vkDestroyBuffer(vk_dev, g->b, NULL);
  if (g->m) p_vkFreeMemory(vk_dev, g->m, NULL);
  memset(g, 0, sizeof *g);
}
static int buf_need(struct Buf *g, VkDeviceSize sz) {           /* at least sz bytes, doubling */
  if (g->b && g->sz >= sz) return 1;
  VkDeviceSize c = g->sz ? g->sz : 4096; while (c < sz) c *= 2;
  buf_free(g);
  return buf_alloc(g, c);
}
static int k_init(void) {
  if (k_state) return k_state == 1;
  k_state = 2;
  if (!vk_devok) { if (k_dbg()) fprintf(stderr, "[gpu] kernels off: %s\n", vk_why ? vk_why : "no device"); return 0; }
  if (!vk_have64) { if (k_dbg()) fprintf(stderr, "[gpu] kernels off: the device has no 64-bit integers or doubles in shaders\n"); return 0; }
  VkDescriptorSetLayoutBinding binds[3];
  for (int i = 0; i < 3; i++) binds[i] = (VkDescriptorSetLayoutBinding){ (uint32_t)i, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, 1, VK_SHADER_STAGE_COMPUTE_BIT, NULL };
  VkDescriptorSetLayoutCreateInfo dli = { .sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO, .bindingCount = 3, .pBindings = binds };
  if (p_vkCreateDescriptorSetLayout(vk_dev, &dli, NULL, &k_dsl) != VK_SUCCESS) return 0;
  VkPushConstantRange pcr = { VK_SHADER_STAGE_COMPUTE_BIT, 0, 2 * sizeof(uint32_t) };
  VkPipelineLayoutCreateInfo pli = { .sType = VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO, .setLayoutCount = 1, .pSetLayouts = &k_dsl, .pushConstantRangeCount = 1, .pPushConstantRanges = &pcr };
  if (p_vkCreatePipelineLayout(vk_dev, &pli, NULL, &k_pl) != VK_SUCCESS) return 0;
  VkDescriptorPoolSize dps = { VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, 3 };
  VkDescriptorPoolCreateInfo dpi = { .sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO, .maxSets = 1, .poolSizeCount = 1, .pPoolSizes = &dps };
  if (p_vkCreateDescriptorPool(vk_dev, &dpi, NULL, &k_dp) != VK_SUCCESS) return 0;
  VkDescriptorSetAllocateInfo dai = { .sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO, .descriptorPool = k_dp, .descriptorSetCount = 1, .pSetLayouts = &k_dsl };
  if (p_vkAllocateDescriptorSets(vk_dev, &dai, &k_ds) != VK_SUCCESS) return 0;
  VkCommandPoolCreateInfo cpi = { .sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO, .flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT, .queueFamilyIndex = vk_qfam };
  if (p_vkCreateCommandPool(vk_dev, &cpi, NULL, &k_cp) != VK_SUCCESS) return 0;
  VkCommandBufferAllocateInfo cai = { .sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO, .commandPool = k_cp, .level = VK_COMMAND_BUFFER_LEVEL_PRIMARY, .commandBufferCount = 1 };
  if (p_vkAllocateCommandBuffers(vk_dev, &cai, &k_cb) != VK_SUCCESS) return 0;
  VkFenceCreateInfo fi = { .sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO };
  if (!p_vkCreateFence || p_vkCreateFence(vk_dev, &fi, NULL, &k_fence) != VK_SUCCESS) return 0;
  if (k_dbg()) fprintf(stderr, "[gpu] kernels run on %s\n", vk_name);
  k_state = 1; return 1;
}
static const char *k_cache_dir(void) {
  static char dir[4096];
  if (dir[0]) return dir;
  const char *env = getenv("LIN_NATIVE_CACHE"), *xdg = getenv("XDG_CACHE_HOME"), *home = getenv("HOME");
  if (env && env[0]) snprintf(dir, sizeof dir, "%s", env);
  else if (xdg && xdg[0]) snprintf(dir, sizeof dir, "%s/lin/native", xdg);
  else if (home && home[0]) snprintf(dir, sizeof dir, "%s/.cache/lin/native", home);
  else snprintf(dir, sizeof dir, "/tmp/lin-native-%u", (unsigned)getuid());
  size_t L = strlen(dir) + 1; char p[L]; memcpy(p, dir, L);   /* (made, a component at a time) */
  for (char *c = p + 1; *c; c++) if (*c == '/') { *c = 0; mkdir(p, 0755); *c = '/'; }
  mkdir(p, 0755);
  return dir;
}
static uint32_t *k_spirv(const char *src, uint64_t key, size_t *nbytes) {   /* the SPIR-V for src: the cache's, or compiled now */
  const char *dir = k_cache_dir();
  size_t L = strlen(dir) + 64; char spv[L], comp[L], tmp[L];
  snprintf(spv, L, "%s/gk-%016llx.spv", dir, (unsigned long long)key);
  snprintf(comp, L, "%s/gk-%016llx.comp", dir, (unsigned long long)key);
  snprintf(tmp, L, "%s/gk-%016llx.%d.spv", dir, (unsigned long long)key, (int)getpid());
  FILE *f = fopen(spv, "rb");
  if (!f) {
    FILE *c = fopen(comp, "w"); if (!c) return NULL;
    fputs(src, c); fclose(c);
    const char *gl = getenv("LIN_GLSLANG"); if (!gl || !gl[0]) gl = "glslangValidator";
    pid_t pid = fork();
    if (pid == 0) {
      if (!k_dbg()) { int nul = open("/dev/null", O_WRONLY); if (nul >= 0) { dup2(nul, 1); dup2(nul, 2); } }
      execlp(gl, gl, "-V", "--target-env", "vulkan1.1", "-o", tmp, comp, (char *)NULL); _exit(127);
    }
    int stt = 0; if (pid < 0 || waitpid(pid, &stt, 0) < 0 || !WIFEXITED(stt) || WEXITSTATUS(stt)) {
      if (k_dbg()) fprintf(stderr, "[gpu] %s could not compile %s (status %d): the loop runs on the CPU\n", gl, comp, WIFEXITED(stt) ? WEXITSTATUS(stt) : -1);
      unlink(tmp); return NULL;
    }
    if (rename(tmp, spv)) return NULL;
    f = fopen(spv, "rb"); if (!f) return NULL;
  }
  fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
  uint32_t *w = sz > 0 ? malloc((size_t)sz) : NULL;
  if (!w || fread(w, 1, (size_t)sz, f) != (size_t)sz) { free(w); fclose(f); return NULL; }
  fclose(f); *nbytes = (size_t)sz; return w;
}
static VkPipeline k_pipeline(const char *src, uint64_t key) {
  for (int i = 0; i < nkern; i++) if (kerns[i].key == key) return kerns[i].bad ? VK_NULL_HANDLE : kerns[i].pipe;
  if (nkern == ckern) kerns = realloc(kerns, sizeof *kerns * (size_t)(ckern = ckern ? ckern * 2 : 8));
  Kern *k = &kerns[nkern++]; k->key = key; k->pipe = VK_NULL_HANDLE; k->bad = 1;
  size_t nb = 0; uint32_t *code = k_spirv(src, key, &nb);
  if (!code) return VK_NULL_HANDLE;
  VkShaderModuleCreateInfo smi = { .sType = VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO, .codeSize = nb, .pCode = code };
  VkShaderModule sm; VkResult r = p_vkCreateShaderModule(vk_dev, &smi, NULL, &sm); free(code);
  if (r != VK_SUCCESS) return VK_NULL_HANDLE;
  VkComputePipelineCreateInfo cpi = { .sType = VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO, .layout = k_pl,
    .stage = { .sType = VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO, .stage = VK_SHADER_STAGE_COMPUTE_BIT, .module = sm, .pName = "main" } };
  if (p_vkCreateComputePipelines(vk_dev, VK_NULL_HANDLE, 1, &cpi, NULL, &k->pipe) != VK_SUCCESS) { k->pipe = VK_NULL_HANDLE; return VK_NULL_HANDLE; }
  k->bad = 0; return k->pipe;
}
static pthread_mutex_t k_mu = PTHREAD_MUTEX_INITIALIZER;
int lin_gpu_kernel(const char *src, uint64_t key, int64_t n, int na, const int64_t *st, const unsigned char *vecs, int64_t *out) {
  pthread_mutex_lock(&k_mu);
  int ok = 0;
  if (n <= 0 || na <= 0 || !k_init()) goto done;
  /* the vectors: one per argument that is one, the same in every row (else not this kernel's: 0) */
  int64_t vw = 1;                                               /* (word 0 is unused: no offset is 0) */
  for (int j = 0; j < na; j++) if (vecs[j]) {
    for (int64_t i = 1; i < n; i++) if (st[i * na + j] != st[j]) goto done;
    vw += ((const int64_t *)st[j])[0] + 1;
  }
  /* (a kernel indexes its buffers with 32-bit words: a larger dispatch is the CPU's) */
  if ((uint64_t)n * (uint64_t)na >= (1ull << 31) || (uint64_t)vw >= (1ull << 31) || (uint64_t)n >= (1ull << 31)) goto done;
  VkPipeline pipe = k_pipeline(src, key);
  if (!pipe) goto done;
  if (!buf_need(&k_st, (VkDeviceSize)(n * na) * 8) || !buf_need(&k_out, (VkDeviceSize)n * 8) || !buf_need(&k_vec, (VkDeviceSize)vw * 8)) goto done;
  int64_t *S = k_st.map, *Vv = k_vec.map, at = 1;
  memcpy(S, st, (size_t)(n * na) * 8);
  Vv[0] = 0;
  for (int j = 0; j < na; j++) if (vecs[j]) {
    const int64_t *v = (const int64_t *)st[j]; int64_t len = v[0];
    Vv[at] = len; memcpy(&Vv[at + 1], v + 2, (size_t)len * 8);
    for (int64_t i = 0; i < n; i++) S[i * na + j] = at;
    at += len + 1;
  }
  VkDescriptorBufferInfo dbi[3] = { { k_st.b, 0, VK_WHOLE_SIZE }, { k_out.b, 0, VK_WHOLE_SIZE }, { k_vec.b, 0, VK_WHOLE_SIZE } };
  VkWriteDescriptorSet wds[3];
  for (int i = 0; i < 3; i++) wds[i] = (VkWriteDescriptorSet){ .sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET, .dstSet = k_ds, .dstBinding = (uint32_t)i,
    .descriptorCount = 1, .descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, .pBufferInfo = &dbi[i] };
  p_vkUpdateDescriptorSets(vk_dev, 3, wds, 0, NULL);
  uint64_t groups = ((uint64_t)n + 63) / 64, gx = groups < vk_maxgx ? groups : vk_maxgx, gy = (groups + gx - 1) / gx;
  if (gy > vk_maxgy) goto done;
  uint32_t pc[2] = { (uint32_t)n, (uint32_t)(gx * 64) };
  VkCommandBufferBeginInfo bi = { .sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO, .flags = VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT };
  if (p_vkBeginCommandBuffer(k_cb, &bi) != VK_SUCCESS) goto done;
  p_vkCmdBindPipeline(k_cb, VK_PIPELINE_BIND_POINT_COMPUTE, pipe);
  p_vkCmdBindDescriptorSets(k_cb, VK_PIPELINE_BIND_POINT_COMPUTE, k_pl, 0, 1, &k_ds, 0, NULL);
  p_vkCmdPushConstants(k_cb, k_pl, VK_SHADER_STAGE_COMPUTE_BIT, 0, sizeof pc, pc);
  p_vkCmdDispatch(k_cb, (uint32_t)gx, (uint32_t)gy, 1);
  VkMemoryBarrier mb = { .sType = VK_STRUCTURE_TYPE_MEMORY_BARRIER, .srcAccessMask = VK_ACCESS_SHADER_WRITE_BIT, .dstAccessMask = VK_ACCESS_HOST_READ_BIT };
  p_vkCmdPipelineBarrier(k_cb, VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT, VK_PIPELINE_STAGE_HOST_BIT, 0, 1, &mb, 0, NULL, 0, NULL);
  if (p_vkEndCommandBuffer(k_cb) != VK_SUCCESS) goto done;
  VkSubmitInfo si = { .sType = VK_STRUCTURE_TYPE_SUBMIT_INFO, .commandBufferCount = 1, .pCommandBuffers = &k_cb };
  p_vkResetFences(vk_dev, 1, &k_fence);
  if (p_vkQueueSubmit(vk_queue, 1, &si, k_fence) != VK_SUCCESS) goto done;
  if (p_vkWaitForFences(vk_dev, 1, &k_fence, VK_TRUE, UINT64_MAX) != VK_SUCCESS) goto done;
  memcpy(out, k_out.map, (size_t)n * 8);
  if (k_dbg()) fprintf(stderr, "[gpu] kernel %016llx: %lld states\n", (unsigned long long)key, (long long)n);
  ok = 1;
done:
  pthread_mutex_unlock(&k_mu);
  return ok;
}

LinDriver lin_gpu_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),   /* the ABI contract in BOTH directions: the core reads only these, and a plugin that does not reach `slot` is REFUSED (a missing `.size` read every hook as absent and made this driver inert while it reported itself the active strategy) */
  .name = "gpu", .description = "Vulkan compute: fixed-rule interaction reduction",
  .caps = LIN_CAP_FIXED, .priority = 20,
  .claim = gpu_claim, .reduce = gpu_reduce,
};
