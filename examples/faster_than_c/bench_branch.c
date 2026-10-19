/* ==============================================================================
 * Benchmark 1: Tree Recursion / Overlapping Subcomputations
 * C reference implementation (compiled with -O3).
 *
 * In standard C, evaluating a recursive branching tree without manual memoization
 * requires O(2^N) function calls, re-evaluating subcomputations exponentially.
 * ============================================================================== */
#include <stdio.h>
#include <stdint.h>
#include <time.h>

uint64_t branch(int d) {
    if (d <= 0) return 1;
    return branch(d - 1) + branch(d - 1);
}

int main(void) {
    int depth = 35;
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    uint64_t val = branch(depth);
    clock_gettime(CLOCK_MONOTONIC, &end);
    double elapsed = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    printf("[C -O3] branch(%d) = %lu in %.4f s\n", depth, val, elapsed);
    return 0;
}
