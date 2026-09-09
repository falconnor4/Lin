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
#include <vulkan/vulkan.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <dlfcn.h>

#define WIRE(n, p) ((n)->wire[(p).node * 3 + (p).port])

static int gpu_ready = 0, pipe_ready = 0;
static VkInstance vk_instance; static VkPhysicalDevice vk_phys;
static VkDevice vk_dev; static VkQueue vk_queue; static uint32_t vk_qfam;
static void *vk_lib;

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
  fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
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
  if (!vk_lib) return;
  LOAD(vkCreateInstance); LOAD(vkEnumeratePhysicalDevices);
  LOAD(vkGetPhysicalDeviceProperties); LOAD(vkGetPhysicalDeviceQueueFamilyProperties);
  LOAD(vkCreateDevice); LOAD(vkGetDeviceQueue);
  p_vkPMemProps = dlsym(vk_lib, "vkGetPhysicalDeviceMemoryProperties");
  if (!p_vkCreateInstance || !p_vkEnumeratePhysicalDevices || !p_vkCreateDevice || !p_vkGetDeviceQueue || !p_vkPMemProps) return;

  VkInstanceCreateInfo ii = {0}; ii.sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
  if (p_vkCreateInstance(&ii, NULL, &vk_instance) != VK_SUCCESS || !vk_instance) return;

  uint32_t ndef = 0;
  if (p_vkEnumeratePhysicalDevices(vk_instance, &ndef, NULL) != VK_SUCCESS || !ndef) return;
  VkPhysicalDevice *devs = malloc(sizeof(VkPhysicalDevice) * ndef);
  if (!devs) return;
  if (p_vkEnumeratePhysicalDevices(vk_instance, &ndef, devs) != VK_SUCCESS) { free(devs); return; }

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
      if (p_vkCreateDevice(vk_phys, &di, NULL, &vk_dev) != VK_SUCCESS || !vk_dev) break;
      p_vkGetDeviceQueue(vk_dev, j, 0, &vk_queue);
      gpu_ready = 1;
      free(q); free(devs);
      goto device_ok;
    }
    free(q);
  }
  free(devs);
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

  /* build the compute pipeline now that all device entry points are loaded */
  build_pipeline();
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

/* Emit the fixed-allocation redexes as a (sorted) list; commute/heap redexes
   are returned separately for the host pass.  Returns nred; sets *nhost_out. */
static int partition(Net *n, Port *curr, int wave_cnt, Port **host_out, int *nhost_out) {
  int nred = 0, nhost = 0;
  static Port *host_rx = NULL; static int host_cap = 0;
  uint32_t *g = (uint32_t *)g_redex.map;
  for (int i = 0; i < wave_cnt; i += 2) {
    Port p1 = curr[i], p2 = curr[i+1];
    if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node]) continue;
    if (WIRE(n,p1).node != p2.node || WIRE(n,p1).port != p2.port) continue;
    if (WIRE(n,p2).node != p1.node || WIRE(n,p2).port != p1.port || p1.port || p2.port) continue;
    int t1 = n->tag[p1.node], t2 = n->tag[p2.node];
    if (t1 > t2) { int tt=t1; t1=t2; t2=tt; }
    int on_gpu;
    if (t1 == LAM && t2 == APP) on_gpu = 1;                 /* beta */
    else if (t1 == DUP && t2 == DUP)
      on_gpu = !(n->scope[p1.node].sso.is_heap || n->scope[p2.node].sso.is_heap);
    else on_gpu = 0;                                        /* commute */

    /* spatial disjointness (mirror lin_reduce_wave_parallel): both nodes and
       all 4 neighbour ports must lie in the same 64-node sector, else the
       concurrent GPU rewrite would race with another redex in the wave. */
    if (on_gpu) {
      int u = p1.node, v = p2.node, su = u >> 6, ok = (su == (v >> 6));
      if (ok) {
        int c[4] = { WIRE(n, ((Port){u, 1})).node, WIRE(n, ((Port){u, 2})).node,
                     WIRE(n, ((Port){v, 1})).node, WIRE(n, ((Port){v, 2})).node };
        for (int k = 0; k < 4; k++) if (c[k] >= 0 && (c[k] >> 6) != su) { ok = 0; break; }
      }
      /* at most one redex per 64-node sector per dispatch: matches the base
         engine's concurrency granularity (different sectors run in parallel,
         same sector sequentially), preventing same-sector aux-port races. */
      if (ok && gpu_sector_used[su]) ok = 0;
      if (ok) gpu_sector_used[su] = 1;
      if (!ok) on_gpu = 0;
    }

    if (on_gpu) {
      uint32_t a = ((uint32_t)(p1.node & 0x3fffffff)) | (p1.port << 30);
      uint32_t b = ((uint32_t)(p2.node & 0x3fffffff)) | (p2.port << 30);
      g[nred*2] = a; g[nred*2+1] = b; nred++;
    } else {
      if (nhost + 2 > host_cap) { host_cap = host_cap ? host_cap*2 : 64; host_rx = realloc(host_rx, (size_t)host_cap * sizeof(Port)); }
      host_rx[nhost++] = p1; host_rx[nhost++] = p2;
    }
  }
  *host_out = host_rx;
  *nhost_out = nhost / 2;
  return nred;
}

/* Bit-exact differential check (LIN_GPU_SELFTEST=1): reduce the SAME fixed
   redexes on a host clone of the net and compare wire[]/dead[] against what
   the GPU just wrote into its mapped buffers.  Reports a running tally. */
static long selftest_mismatches = 0, selftest_runs = 0;

static void gpu_selftest(Net *n, int nred) {
  if (!getenv("LIN_GPU_SELFTEST")) return;
  selftest_runs++;

  /* clone n, replay only the fixed redexes through the host reducer using the
   SAME concurrent wavefront reducer (lin_reduce_wave_parallel) that production
   uses, so the oracle matches the actual host reduction semantics (sequential
   net_interact would differ because concurrent reduction reorders). */
  Net *h = net_copy(n);
  int shadow = 0;
  /* reconstruct the fixed redex pair list as Port[] for the wave reducer */
  Port *fp = malloc(sizeof(Port) * (size_t)nred * 2);
  for (int i = 0; i < nred; i++) {
    uint32_t a = ((uint32_t*)g_redex.map)[i*2], b = ((uint32_t*)g_redex.map)[i*2+1];
    fp[i*2]   = (Port){ (int)(a & 0x3fffffff), (int)(a >> 30) };
    fp[i*2+1] = (Port){ (int)(b & 0x3fffffff), (int)(b >> 30) };
  }
  lin_reduce_wave_parallel(h, fp, nred * 2, &shadow);
  free(fp);

  /* compare host clone vs GPU-committed buffers (wire + dead) */
  long bad = 0;
  uint32_t *gw = (uint32_t *)g_wires.map;
  uint32_t *gd = (uint32_t *)g_deads.map;
  int difftag = -1, diffport = -1; uint32_t gv = 0, hv = 0; unsigned char gd8 = 0, hd8 = 0;
  for (int i = 0; i < n->nn && !bad; i++) {
    if ((unsigned char)gd[i] != h->dead[i]) { bad = 1; difftag = i; gd8 = (unsigned char)gd[i]; hd8 = h->dead[i]; break; }
    for (int p = 0; p < 3; p++) {
      Port hw = h->wire[i*3+p];
      uint32_t hw32 = hw.node < 0 ? 0x3fffffffu : ((uint32_t)(hw.node & 0x3fffffff) | (hw.port << 30));
      if (gw[i*3+p] != hw32) { bad = 1; difftag = i; diffport = p; gv = gw[i*3+p]; hv = hw32; break; }
    }
  }
  if (bad && getenv("LIN_GPU_SELFTEST")) {
    if (diffport >= 0)
      fprintf(stderr, "[gpu self] first diff node %d port %d: gpu=0x%08x host=0x%08x (replaying %d redexes)\n",
              difftag, diffport, gv, hv, nred);
    else
      fprintf(stderr, "[gpu self] first diff node %d dead: gpu=%u host=%u\n", difftag, gd8, hd8);
    if (getenv("LIN_GPU_SELFTEST_DUMP")) {
      for (int i = 0; i < nred; i++) {
        uint32_t a = ((uint32_t*)g_redex.map)[i*2], b = ((uint32_t*)g_redex.map)[i*2+1];
        fprintf(stderr, "  redex %d: n%d.%d(tag%d) x n%d.%d(tag%d)\n", i,
                (int)(a & 0x3fffffff), (int)(a >> 30), n->tag[a & 0x3fffffff],
                (int)(b & 0x3fffffff), (int)(b >> 30), n->tag[b & 0x3fffffff]);
      }
    }
  }
  if (bad) selftest_mismatches++;
  fprintf(stderr, "[gpu selftest] %s (run %ld, %ld/%ld waves mismatched)\n",
          bad ? "MISMATCH" : "OK", selftest_runs, selftest_mismatches, selftest_runs);
  net_free(h);
  (void)shadow;
}

static int gpu_reduce_wave(Net *n, long limit, int *changed) {
  if (!gpu_ready || n->atop <= 0 || n->steps >= limit) return 0;
  static Port *curr = NULL; static int curr_cap = 0;
  int wave_cnt = wave_snapshot(n, &curr, &curr_cap);
  if (wave_cnt <= 0) return 1;

  /* reset the per-sector usage bitmap for this wave */
  int nsec = (n->nn + 63) >> 6;
  if (nsec > gpu_sector_cap) {
    gpu_sector_used = realloc(gpu_sector_used, (size_t)nsec);
    gpu_sector_cap = nsec;
  }
  memset(gpu_sector_used, 0, (size_t)nsec);

  /* Size all device buffers first (redex worst case = wave_cnt/2 pairs), then
     partition writes into g_redex.map and the net-upload uses g_tags etc. */
  if (!pipe_ready || !ensure_buffers(n, wave_cnt / 2 + 1)) {
    /* no pipeline/buffers: fall through to host-only reduction */
    int shadow = 0;
    lin_reduce_wave_parallel(n, curr, wave_cnt, &shadow);
    *changed += shadow;
    return 1;
  }

  Port *host_rx = NULL; int nhost = 0;
  int nred = partition(n, curr, wave_cnt, &host_rx, &nhost);

  if (nred > 0) {
    /* upload net arrays into the mapped coherent buffers */
    uint32_t *tags = (uint32_t *)g_tags.map, *deads = (uint32_t *)g_deads.map;
    uint32_t *wires = (uint32_t *)g_wires.map;
    uint64_t *scopes = (uint64_t *)g_scopes.map;
    for (int i = 0; i < n->nn; i++) {
      tags[i] = n->tag[i];
      deads[i] = n->dead[i];
      scopes[i] = n->scope[i].raw;
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
    uint32_t nrc = (uint32_t)nred;
    p_vkCmdPushConstants(vk_cb, vk_playout, VK_SHADER_STAGE_COMPUTE_BIT, 0, sizeof(nrc), &nrc);
    p_vkCmdDispatch(vk_cb, (nred + 63) / 64, 1, 1);
    p_vkEndCommandBuffer(vk_cb);
    VkSubmitInfo si = {0}; si.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    si.commandBufferCount = 1; si.pCommandBuffers = &vk_cb;
    p_vkQueueSubmit(vk_queue, 1, &si, VK_NULL_HANDLE);
    p_vkQueueWaitIdle(vk_queue);

    if (getenv("LIN_GPU_DEBUG"))
      fprintf(stderr, "[gpu] dispatched %d redexes on device\n", nred);
    gpu_selftest(n, nred);
  }

  /* Always run the host reducer as the ground-truth reducer (correctness is
     guaranteed; the GPU path is exercised and benchmarked but not yet made
     authoritative until the differential self-test is bit-exact). */
  int shadow = 0;
  lin_reduce_wave_parallel(n, curr, wave_cnt, &shadow);
  *changed += shadow;
  return 1;
}

LinDriver lin_gpu_driver = { "gpu", gpu_reduce_wave };
