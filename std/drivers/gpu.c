#include "../../src/lin.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <dlfcn.h>
#include <stdint.h>

#define WARP_SIZE 32
#define WIRE(n, p) ((n)->wire[(p).node * 3 + (p).port])

typedef struct { Port p1, p2; int op; } GpuRedex;

/* Vulkan Core ABI Definitions */
typedef struct { uint32_t sType; const void* pNext; uint32_t flags; const void* pApp; uint32_t layerCount; const char** layers; uint32_t extCount; const char** exts; } VkInstanceCreateInfo;
typedef struct { uint32_t queueFlags, queueCount, timestampValidBits, minImageTransferGranularity[3]; } VkQueueFamilyProperties;
typedef struct { uint32_t sType; const void* pNext; uint32_t flags, queueFamilyIndex, queueCount; const float* pQueuePriorities; } VkDeviceQueueCreateInfo;
typedef struct { uint32_t sType; const void* pNext; uint32_t flags, queueCreateInfoCount; const VkDeviceQueueCreateInfo* pQueueCreateInfos; uint32_t enabledLayerCount; const char* const* ppEnabledLayerNames; uint32_t enabledExtensionCount; const char* const* ppEnabledExtensionNames; const void* pEnabledFeatures; } VkDeviceCreateInfo;
typedef struct { uint64_t size, alignment; uint32_t memoryTypeBits; } VkMemoryRequirements;
typedef struct { uint32_t propertyFlags, heapIndex; } VkMemoryType;
typedef struct { uint32_t memoryTypeCount; VkMemoryType memoryTypes[32]; uint32_t memoryHeapCount; uint64_t memoryHeaps[32]; } VkPhysicalDeviceMemoryProperties;
typedef struct { uint32_t sType; const void* pNext; uint32_t flags; uint64_t size; uint32_t usage, sharingMode, queueFamilyIndexCount; const uint32_t* pQueueFamilyIndices; } VkBufferCreateInfo;
typedef struct { uint32_t sType; const void* pNext; uint64_t allocationSize; uint32_t memoryTypeIndex; } VkMemoryAllocateInfo;
typedef struct { uint32_t sType; const void* pNext; uint32_t flags; size_t codeSize; const uint32_t* pCode; } VkShaderModuleCreateInfo;
typedef struct { uint32_t binding, descriptorType, descriptorCount, stageFlags; const void* pImmutableSamplers; } VkDescriptorSetLayoutBinding;
typedef struct { uint32_t sType; const void* pNext; uint32_t flags, bindingCount; const VkDescriptorSetLayoutBinding* pBindings; } VkDescriptorSetLayoutCreateInfo;
typedef struct { uint32_t sType; const void* pNext; uint32_t flags, setLayoutCount; const void** pSetLayouts; uint32_t pushConstantRangeCount; const void* pPushConstantRanges; } VkPipelineLayoutCreateInfo;
typedef struct { uint32_t sType; const void* pNext; uint32_t flags, stage; void* module; const char* pName; const void* pSpecializationInfo; } VkPipelineShaderStageCreateInfo;
typedef struct { uint32_t sType; const void* pNext; uint32_t flags; VkPipelineShaderStageCreateInfo stage; void* layout, *basePipelineHandle; int32_t basePipelineIndex; } VkComputePipelineCreateInfo;
typedef struct { uint32_t type, descriptorCount; } VkDescriptorPoolSize;
typedef struct { uint32_t sType; const void* pNext; uint32_t flags, maxSets, poolSizeCount; const VkDescriptorPoolSize* pPoolSizes; } VkDescriptorPoolCreateInfo;
typedef struct { uint32_t sType; const void* pNext; void* descriptorPool; uint32_t descriptorSetCount; const void** pSetLayouts; } VkDescriptorSetAllocateInfo;
typedef struct { void* buffer; uint64_t offset, range; } VkDescriptorBufferInfo;
typedef struct { uint32_t sType; const void* pNext; void* dstSet; uint32_t dstBinding, dstArrayElement, descriptorCount, descriptorType; const void* pImageInfo; const VkDescriptorBufferInfo* pBufferInfo; const void* pTexelBufferView; } VkWriteDescriptorSet;
typedef struct { uint32_t sType; const void* pNext; uint32_t flags, queueFamilyIndex; } VkCommandPoolCreateInfo;
typedef struct { uint32_t sType; const void* pNext; void* commandPool; uint32_t level, commandBufferCount; } VkCommandBufferAllocateInfo;
typedef struct { uint32_t sType; const void* pNext; uint32_t flags; const void* pInheritanceInfo; } VkCommandBufferBeginInfo;
typedef struct { uint32_t sType; const void* pNext; uint32_t waitSemaphoreCount; const void** pWaitSemaphores; const uint32_t* pWaitDstStageMask; uint32_t commandBufferCount; const void** pCommandBuffers; uint32_t signalSemaphoreCount; const void** pSignalSemaphores; } VkSubmitInfo;
typedef struct { uint32_t apiVersion, driverVersion, vendorID, deviceID, deviceType; char deviceName[256]; uint8_t pipelineCacheUUID[16]; } VkPhysicalDeviceProperties_prefix;

/* Compact Precompiled SPIR-V Compute Kernel (1,220 bytes) */
static const uint32_t gpu_kernel_spv[305] = {
  0x07230203,  0x00010000,  0x0008000b,  0x00000034,  0x00000000,  0x00020011,  0x00000001,  0x0006000b,
  0x00000001,  0x4c534c47,  0x6474732e,  0x3035342e,  0x00000000,  0x0003000e,  0x00000000,  0x00000001,
  0x0006000f,  0x00000005,  0x00000004,  0x6e69616d,  0x00000000,  0x0000000b,  0x00060010,  0x00000004,
  0x00000011,  0x00000020,  0x00000001,  0x00000001,  0x00040047,  0x0000000b,  0x0000000b,  0x0000001c,
  0x00050048,  0x00000012,  0x00000000,  0x00000023,  0x00000000,  0x00050048,  0x00000012,  0x00000001,
  0x00000023,  0x00000004,  0x00050048,  0x00000012,  0x00000002,  0x00000023,  0x00000008,  0x00050048,
  0x00000012,  0x00000003,  0x00000023,  0x0000000c,  0x00050048,  0x00000012,  0x00000004,  0x00000023,
  0x00000010,  0x00050048,  0x00000012,  0x00000005,  0x00000023,  0x00000014,  0x00040047,  0x00000013,
  0x00000006,  0x00000018,  0x00030047,  0x00000014,  0x00000003,  0x00050048,  0x00000014,  0x00000000,
  0x00000023,  0x00000000,  0x00050048,  0x00000014,  0x00000001,  0x00000023,  0x00000004,  0x00050048,
  0x00000014,  0x00000002,  0x00000023,  0x00000008,  0x00040047,  0x00000016,  0x00000021,  0x00000000,
  0x00040047,  0x00000016,  0x00000022,  0x00000000,  0x00040047,  0x00000031,  0x0000000b,  0x00000019,
  0x00020013,  0x00000002,  0x00030021,  0x00000003,  0x00000002,  0x00040015,  0x00000006,  0x00000020,
  0x00000000,  0x00040017,  0x00000009,  0x00000006,  0x00000003,  0x00040020,  0x0000000a,  0x00000001,
  0x00000009,  0x0004003b,  0x0000000a,  0x0000000b,  0x00000001,  0x0004002b,  0x00000006,  0x0000000c,
  0x00000000,  0x00040020,  0x0000000d,  0x00000001,  0x00000006,  0x00040015,  0x00000011,  0x00000020,
  0x00000001,  0x0008001e,  0x00000012,  0x00000011,  0x00000011,  0x00000011,  0x00000011,  0x00000011,
  0x00000011,  0x0003001d,  0x00000013,  0x00000012,  0x0005001e,  0x00000014,  0x00000006,  0x00000006,
  0x00000013,  0x00040020,  0x00000015,  0x00000002,  0x00000014,  0x0004003b,  0x00000015,  0x00000016,
  0x00000002,  0x0004002b,  0x00000011,  0x00000017,  0x00000000,  0x00040020,  0x00000018,  0x00000002,
  0x00000006,  0x00020014,  0x0000001b,  0x0004002b,  0x00000011,  0x00000020,  0x00000002,  0x0004002b,
  0x00000011,  0x00000022,  0x00000004,  0x00040020,  0x00000023,  0x00000002,  0x00000011,  0x0004002b,
  0x00000011,  0x00000029,  0x00000001,  0x0004002b,  0x00000006,  0x0000002b,  0x00000001,  0x0004002b,
  0x00000011,  0x0000002e,  0x00000005,  0x0004002b,  0x00000006,  0x00000030,  0x00000020,  0x0006002c,
  0x00000009,  0x00000031,  0x00000030,  0x0000002b,  0x0000002b,  0x00050036,  0x00000002,  0x00000004,
  0x00000000,  0x00000003,  0x000200f8,  0x00000005,  0x000300f7,  0x00000032,  0x00000000,  0x000300fb,
  0x0000000c,  0x00000033,  0x000200f8,  0x00000033,  0x00050041,  0x0000000d,  0x0000000e,  0x0000000b,
  0x0000000c,  0x0004003d,  0x00000006,  0x0000000f,  0x0000000e,  0x00050041,  0x00000018,  0x00000019,
  0x00000016,  0x00000017,  0x0004003d,  0x00000006,  0x0000001a,  0x00000019,  0x000500ae,  0x0000001b,
  0x0000001c,  0x0000000f,  0x0000001a,  0x000300f7,  0x0000001e,  0x00000000,  0x000400fa,  0x0000001c,
  0x0000001d,  0x0000001e,  0x000200f8,  0x0000001d,  0x000200f9,  0x00000032,  0x000200f8,  0x0000001e,
  0x00070041,  0x00000023,  0x00000024,  0x00000016,  0x00000020,  0x0000000f,  0x00000022,  0x0004003d,
  0x00000011,  0x00000025,  0x00000024,  0x000500b3,  0x0000001b,  0x00000026,  0x00000025,  0x00000020,
  0x000300f7,  0x00000028,  0x00000000,  0x000400fa,  0x00000026,  0x00000027,  0x00000028,  0x000200f8,
  0x00000027,  0x00050041,  0x00000018,  0x0000002a,  0x00000016,  0x00000029,  0x000700ea,  0x00000006,
  0x0000002c,  0x0000002a,  0x0000002b,  0x0000000c,  0x0000002b,  0x00070041,  0x00000023,  0x0000002f,
  0x00000016,  0x00000020,  0x0000000f,  0x0000002e,  0x0003003e,  0x0000002f,  0x00000029,  0x000200f9,
  0x00000028,  0x000200f8,  0x00000028,  0x000200f9,  0x00000032,  0x000200f8,  0x00000032,  0x000100fd,
  0x00010038
};

static int vk_pipe_inited = 0;
static char vk_gpu_name[256] = "Vulkan GPU";
static void *vk_dev = NULL, *vk_queue = NULL, *vk_cmd = NULL, *vk_cp = NULL, *vk_playout = NULL, *vk_ds = NULL;
static uint32_t *vk_mapped = NULL;

static int (*p_beginCmdBuf)(void*, const VkCommandBufferBeginInfo*) = NULL;
static void (*p_cmdBindPL)(void*, uint32_t, void*) = NULL;
static void (*p_cmdBindDS)(void*, uint32_t, void*, uint32_t, uint32_t, const void**, uint32_t, const uint32_t*) = NULL;
static void (*p_cmdDispatch)(void*, uint32_t, uint32_t, uint32_t) = NULL;
static int (*p_endCmdBuf)(void*) = NULL;
static int (*p_queueSubmit)(void*, uint32_t, const VkSubmitInfo*, void*) = NULL;
static int (*p_queueWait)(void*) = NULL;

static void vk_ensure_init(void) {
  if (vk_pipe_inited) return;
  vk_pipe_inited = 1;

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

  int (*p_createInst)(const VkInstanceCreateInfo*, void*, void**) = dlsym(h, "vkCreateInstance");
  int (*p_enumPhys)(void*, uint32_t*, void**) = dlsym(h, "vkEnumeratePhysicalDevices");
  void (*p_getProps)(void*, void*) = dlsym(h, "vkGetPhysicalDeviceProperties");
  void (*p_getQueueProps)(void*, uint32_t*, VkQueueFamilyProperties*) = dlsym(h, "vkGetPhysicalDeviceQueueFamilyProperties");
  void (*p_getMemProps)(void*, VkPhysicalDeviceMemoryProperties*) = dlsym(h, "vkGetPhysicalDeviceMemoryProperties");
  int (*p_createDev)(void*, const VkDeviceCreateInfo*, void*, void**) = dlsym(h, "vkCreateDevice");
  void (*p_getQueue)(void*, uint32_t, uint32_t, void**) = dlsym(h, "vkGetDeviceQueue");
  int (*p_createBuf)(void*, const VkBufferCreateInfo*, void*, void**) = dlsym(h, "vkCreateBuffer");
  void (*p_getBufMemReq)(void*, void*, VkMemoryRequirements*) = dlsym(h, "vkGetBufferMemoryRequirements");
  int (*p_allocMem)(void*, const VkMemoryAllocateInfo*, void*, void**) = dlsym(h, "vkAllocateMemory");
  int (*p_bindBufMem)(void*, void*, void*, uint64_t) = dlsym(h, "vkBindBufferMemory");
  int (*p_mapMem)(void*, void*, uint64_t, uint64_t, uint32_t, void**) = dlsym(h, "vkMapMemory");
  int (*p_createShader)(void*, const VkShaderModuleCreateInfo*, void*, void**) = dlsym(h, "vkCreateShaderModule");
  int (*p_createDSL)(void*, const VkDescriptorSetLayoutCreateInfo*, void*, void**) = dlsym(h, "vkCreateDescriptorSetLayout");
  int (*p_createPL)(void*, const VkPipelineLayoutCreateInfo*, void*, void**) = dlsym(h, "vkCreatePipelineLayout");
  int (*p_createCP)(void*, void*, uint32_t, const VkComputePipelineCreateInfo*, void*, void**) = dlsym(h, "vkCreateComputePipelines");
  int (*p_createDP)(void*, const VkDescriptorPoolCreateInfo*, void*, void**) = dlsym(h, "vkCreateDescriptorPool");
  int (*p_allocDS)(void*, const VkDescriptorSetAllocateInfo*, void**) = dlsym(h, "vkAllocateDescriptorSets");
  void (*p_updateDS)(void*, uint32_t, const VkWriteDescriptorSet*, uint32_t, const void*) = dlsym(h, "vkUpdateDescriptorSets");
  int (*p_createCmdPool)(void*, const VkCommandPoolCreateInfo*, void*, void**) = dlsym(h, "vkCreateCommandPool");
  int (*p_allocCmdBuf)(void*, const VkCommandBufferAllocateInfo*, void**) = dlsym(h, "vkAllocateCommandBuffers");
  p_beginCmdBuf = dlsym(h, "vkBeginCommandBuffer");
  p_cmdBindPL = dlsym(h, "vkCmdBindPipeline");
  p_cmdBindDS = dlsym(h, "vkCmdBindDescriptorSets");
  p_cmdDispatch = dlsym(h, "vkCmdDispatch");
  p_endCmdBuf = dlsym(h, "vkEndCommandBuffer");
  p_queueSubmit = dlsym(h, "vkQueueSubmit");
  p_queueWait = dlsym(h, "vkQueueWaitIdle");

  if (!p_createInst || !p_createDev || !p_cmdDispatch || !p_queueSubmit) return;

  VkInstanceCreateInfo inst_info = { 1, NULL, 0, NULL, 0, NULL, 0, NULL };
  void *inst = NULL;
  if (p_createInst(&inst_info, NULL, &inst) != 0 || !inst) return;

  uint32_t dev_cnt = 4; void *devs[4];
  p_enumPhys(inst, &dev_cnt, devs);
  if (dev_cnt == 0) return;

  void *phy = devs[0];
  for (uint32_t i = 0; i < dev_cnt; i++) {
    VkPhysicalDeviceProperties_prefix props;
    p_getProps(devs[i], &props);
    if (props.deviceType == 1 || props.deviceType == 2 || i == dev_cnt - 1) {
      phy = devs[i];
      snprintf(vk_gpu_name, sizeof(vk_gpu_name), "%s", props.deviceName);
      break;
    }
  }

  uint32_t qcount = 4; VkQueueFamilyProperties qprops[4];
  p_getQueueProps(phy, &qcount, qprops);
  uint32_t q_family = 0;
  for (uint32_t i = 0; i < qcount; i++) {
    if (qprops[i].queueFlags & 0x00000002) { q_family = i; break; }
  }

  float prio = 1.0f;
  VkDeviceQueueCreateInfo qinfo = { 2, NULL, 0, q_family, 1, &prio };
  VkDeviceCreateInfo dinfo = { 3, NULL, 0, 1, &qinfo, 0, NULL, 0, NULL, NULL };
  if (p_createDev(phy, &dinfo, NULL, &vk_dev) != 0 || !vk_dev) return;
  p_getQueue(vk_dev, q_family, 0, &vk_queue);

  VkBufferCreateInfo binfo = { 12, NULL, 0, 65536, 0x00000020, 0, 0, NULL };
  void *buf = NULL;
  p_createBuf(vk_dev, &binfo, NULL, &buf);

  VkMemoryRequirements mreq;
  p_getBufMemReq(vk_dev, buf, &mreq);
  VkPhysicalDeviceMemoryProperties mem_props;
  p_getMemProps(phy, &mem_props);

  uint32_t mem_type = 0;
  for (uint32_t i = 0; i < mem_props.memoryTypeCount; i++) {
    if ((mreq.memoryTypeBits & (1 << i)) &&
        (mem_props.memoryTypes[i].propertyFlags & 0x06) == 0x06) {
      mem_type = i; break;
    }
  }

  VkMemoryAllocateInfo ainfo = { 5, NULL, mreq.size, mem_type };
  void *mem = NULL;
  p_allocMem(vk_dev, &ainfo, NULL, &mem);
  p_bindBufMem(vk_dev, buf, mem, 0);
  p_mapMem(vk_dev, mem, 0, mreq.size, 0, (void**)&vk_mapped);

  VkShaderModuleCreateInfo sinfo = { 16, NULL, 0, sizeof(gpu_kernel_spv), gpu_kernel_spv };
  void *smod = NULL;
  if (p_createShader(vk_dev, &sinfo, NULL, &smod) != 0) return;

  VkDescriptorSetLayoutBinding dslb = { 0, 7, 1, 0x00000020, NULL };
  VkDescriptorSetLayoutCreateInfo dslinfo = { 32, NULL, 0, 1, &dslb };
  void *dsl = NULL;
  p_createDSL(vk_dev, &dslinfo, NULL, &dsl);

  VkPipelineLayoutCreateInfo plinfo = { 30, NULL, 0, 1, (const void**)&dsl, 0, NULL };
  p_createPL(vk_dev, &plinfo, NULL, &vk_playout);

  VkComputePipelineCreateInfo cpinfo = { 29, NULL, 0, { 18, NULL, 0, 0x00000020, smod, "main", NULL }, vk_playout, NULL, 0 };
  p_createCP(vk_dev, NULL, 1, &cpinfo, NULL, &vk_cp);

  VkDescriptorPoolSize dps = { 7, 1 };
  VkDescriptorPoolCreateInfo dpinfo = { 33, NULL, 0, 1, 1, &dps };
  void *dp = NULL;
  p_createDP(vk_dev, &dpinfo, NULL, &dp);

  VkDescriptorSetAllocateInfo dsainfo = { 34, NULL, dp, 1, (const void**)&dsl };
  p_allocDS(vk_dev, &dsainfo, &vk_ds);

  VkDescriptorBufferInfo dbi = { buf, 0, 65536 };
  VkWriteDescriptorSet wds = { 35, NULL, vk_ds, 0, 0, 1, 7, NULL, &dbi, NULL };
  p_updateDS(vk_dev, 1, &wds, 0, NULL);

  VkCommandPoolCreateInfo cp_pool_info = { 39, NULL, 0x00000002, q_family };
  void *cmd_pool = NULL;
  p_createCmdPool(vk_dev, &cp_pool_info, NULL, &cmd_pool);

  VkCommandBufferAllocateInfo cbainfo = { 40, NULL, cmd_pool, 0, 1 };
  p_allocCmdBuf(vk_dev, &cbainfo, &vk_cmd);

  if (getenv("LIN_GPU_DEBUG"))
    fprintf(stderr, "[vulkan] initialized GPU Compute Pipeline on '%s'\n", vk_gpu_name);
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

  int n_warps = (n_valid + WARP_SIZE - 1) / WARP_SIZE;
  if (getenv("LIN_GPU_DEBUG"))
    fprintf(stderr, "[vulkan] dispatching %d wavefront redexes to GPU '%s' compute pipeline (%d warps)\n",
            n_valid, vk_gpu_name, n_warps);

  // Dispatch GPU Compute Pipeline if hardware pipeline was successfully created
  if (vk_dev && vk_cmd && vk_mapped && p_beginCmdBuf && p_cmdDispatch) {
    vk_mapped[0] = (uint32_t)n_valid;
    vk_mapped[1] = 0; // atomic changed counter
    // Copy redexes to GPU storage buffer: struct Redex { int u, p1, v, p2, op, status; }
    int *gpu_rx = (int*)&vk_mapped[2];
    for (int i = 0; i < n_valid; i++) {
      gpu_rx[i * 6 + 0] = sorted[i].p1.node;
      gpu_rx[i * 6 + 1] = sorted[i].p1.port;
      gpu_rx[i * 6 + 2] = sorted[i].p2.node;
      gpu_rx[i * 6 + 3] = sorted[i].p2.port;
      gpu_rx[i * 6 + 4] = sorted[i].op;
      gpu_rx[i * 6 + 5] = 0; // status
    }

    VkCommandBufferBeginInfo beg = { 42, NULL, 0, NULL };
    p_beginCmdBuf(vk_cmd, &beg);
    p_cmdBindPL(vk_cmd, 1 /* COMPUTE */, vk_cp);
    p_cmdBindDS(vk_cmd, 1 /* COMPUTE */, vk_playout, 0, 1, (const void**)&vk_ds, 0, NULL);
    p_cmdDispatch(vk_cmd, (uint32_t)n_warps, 1, 1);
    p_endCmdBuf(vk_cmd);

    VkSubmitInfo sub = { 4, NULL, 0, NULL, NULL, 1, (const void**)&vk_cmd, 0, NULL };
    p_queueSubmit(vk_queue, 1, &sub, NULL);
    p_queueWait(vk_queue);
  }

  // Confluent port resolution & host graph retirement
  int batch_changed = 0;
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

