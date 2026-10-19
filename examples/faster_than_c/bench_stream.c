/* ==============================================================================
 * Benchmark 2: Lazy Observation / Demand-Driven Execution
 * C reference implementation (compiled with -O3).
 *
 * In C, generating a sequence eagerly allocates and transforms all N elements
 * even if a downstream consumer only observes the first few items.
 * ============================================================================== */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>

long *generate_sequence(int n) {
    long *arr = malloc(n * sizeof(long));
    for (int i = 0; i < n; i++) {
        arr[i] = (long)i * (long)i + 3 * (long)i + 7;
    }
    return arr;
}

long take_prefix(const long *arr, int k) {
    long sum = 0;
    for (int i = 0; i < k; i++) sum += arr[i];
    return sum;
}

int main(void) {
    int N = 10000000;
    int k = 5;
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    long *arr = generate_sequence(N);
    long res = take_prefix(arr, k);
    clock_gettime(CLOCK_MONOTONIC, &end);
    free(arr);
    double elapsed = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    printf("[C -O3] eager stream (%d elements, take %d) = %ld in %.4f s\n", N, k, res, elapsed);
    return 0;
}
