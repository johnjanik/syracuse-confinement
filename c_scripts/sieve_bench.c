/* sieve_bench.c — Proof-of-concept benchmark: sieved vs unsieved Collatz
 *
 * Demonstrates the fast-forward optimization for branch_locus-style workloads.
 * Processes n from 1 to N, computing total (odd_steps, even_steps, trajectory_steps)
 * with and without the sieve fast-forward.
 *
 * The sieve replaces the first (a+k) Collatz steps with:
 *   n_new = (A_num * n + B_num) >> k
 * and advances (v2, v3) counters by (k, a) directly.
 *
 * Compile: gcc -O3 -march=native -fopenmp -o sieve_bench sieve_bench.c -lm
 * Usage:   ./sieve_bench [-N <max>] [-k <bits>]
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>

typedef struct {
    uint16_t class_odd;
    uint8_t  class_dead;
    uint8_t  exact_dead;
    uint32_t exact_steps;
    uint64_t A_num;
    uint64_t B_num;
} precomp_t;

int main(int argc, char **argv) {
    int64_t N = 10000000;  /* default 10M */
    int k = 16;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-N") == 0 && i + 1 < argc) N = atoll(argv[++i]);
        if (strcmp(argv[i], "-k") == 0 && i + 1 < argc) k = atoi(argv[++i]);
    }

    uint64_t mod = 1ULL << k;
    uint64_t mask = mod - 1;
    uint64_t n_odd = mod / 2;

    /* Load precomp data */
    char fname[256];
    snprintf(fname, sizeof(fname), "sieve_k%d_precomp.bin", k);
    FILE *f = fopen(fname, "rb");
    if (!f) { fprintf(stderr, "Cannot open %s — run gen_sieve -k %d first\n", fname, k); return 1; }

    int k_file;
    uint64_t n_odd_file;
    fread(&k_file, sizeof(int), 1, f);
    fread(&n_odd_file, sizeof(uint64_t), 1, f);

    precomp_t *sieve = malloc(n_odd * sizeof(precomp_t));
    if (!sieve) { fprintf(stderr, "OOM\n"); return 1; }
    fread(sieve, sizeof(precomp_t), n_odd, f);
    fclose(f);

    printf("=== Sieve Benchmark ===\n");
    printf("N = %ld, k = %d, threads = %d\n\n", N, k, omp_get_max_threads());

    /* ── UNSIEVED RUN ── */
    double t0 = omp_get_wtime();
    uint64_t total_steps_unsieved = 0;

    #pragma omp parallel reduction(+:total_steps_unsieved)
    {
        #pragma omp for schedule(dynamic, 4096)
        for (int64_t n = 1; n <= N; n++) {
            uint64_t x = (uint64_t)n;
            uint64_t steps = 0;
            while (x != 1) {
                if (x & 1)
                    x = 3 * x + 1;
                else
                    x >>= 1;
                steps++;
            }
            total_steps_unsieved += steps;
        }
    }

    double t_unsieved = omp_get_wtime() - t0;

    /* ── SIEVED RUN ── */
    t0 = omp_get_wtime();
    uint64_t total_steps_sieved = 0;
    uint64_t total_skipped = 0;

    #pragma omp parallel reduction(+:total_steps_sieved, total_skipped)
    {
        #pragma omp for schedule(dynamic, 4096)
        for (int64_t n = 1; n <= N; n++) {
            uint64_t x = (uint64_t)n;
            uint64_t steps = 0;

            /* Recursive fast-forward: keep applying sieve while x is
             * odd and large enough. Each application skips a+k steps.
             * For n < 2^k, trajectories can be shorter than a+k steps,
             * causing the formula to "overshoot" past the {1,4,2} cycle. */
            while ((x & 1) && x >= mod) {
                uint64_t r = x & mask;
                if (!(r & 1)) break;  /* r is even → can't look up (shouldn't happen for odd x) */
                uint64_t idx = r / 2;
                uint16_t a = sieve[idx].class_odd;
                uint64_t A = sieve[idx].A_num;
                uint64_t B = sieve[idx].B_num;

                __uint128_t prod = (__uint128_t)A * x + B;
                uint64_t x_new = (uint64_t)(prod >> k);

                if (x_new == 0 || x_new >= x) break;

                uint64_t skipped = a + k;
                total_skipped += skipped;
                steps += skipped;
                x = x_new;
                /* x_new could be odd → loop again, or even → exit loop */
            }

            /* Normal Collatz iteration for remaining steps */
            while (x != 1) {
                if (x & 1)
                    x = 3 * x + 1;
                else
                    x >>= 1;
                steps++;
            }
            total_steps_sieved += steps;
        }
    }

    double t_sieved = omp_get_wtime() - t0;

    /* ── RESULTS ── */
    printf("Unsieved:\n");
    printf("  Time: %.3f s\n", t_unsieved);
    printf("  Total steps: %lu\n", total_steps_unsieved);
    printf("  Rate: %.1f M steps/s\n", total_steps_unsieved / t_unsieved / 1e6);

    printf("\nSieved (k=%d):\n", k);
    printf("  Time: %.3f s\n", t_sieved);
    printf("  Total steps: %lu (should match unsieved)\n", total_steps_sieved);
    printf("  Steps skipped by sieve: %lu (%.1f%%)\n",
           total_skipped, 100.0 * total_skipped / total_steps_sieved);
    printf("  Rate: %.1f M steps/s\n", total_steps_sieved / t_sieved / 1e6);

    if (total_steps_unsieved != total_steps_sieved) {
        printf("\n*** WARNING: step counts don't match! ***\n");
        printf("  Difference: %ld\n", (int64_t)total_steps_sieved - (int64_t)total_steps_unsieved);
    } else {
        printf("\n  CORRECTNESS VERIFIED: step counts match.\n");
    }

    printf("\nSpeedup: %.2fx (%.1f%% faster)\n",
           t_unsieved / t_sieved,
           100.0 * (1.0 - t_sieved / t_unsieved));

    printf("\nNote: This benchmark measures pure Collatz iteration speedup.\n");
    printf("branch_locus also does grid updates per step, so the speedup from\n");
    printf("skipping steps is LARGER in branch_locus (saves grid work too).\n");

    free(sieve);
    return 0;
}
