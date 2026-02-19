/* gen_sieve.c — Collatz sieve generator for branch_locus acceleration
 *
 * Two analyses per odd residue r mod 2^k:
 *
 * 1. CLASS ANALYSIS: Determine the parity sequence for ALL n ≡ r (mod 2^k).
 *    Track transformation n ↦ (3^a · n + B) / 2^k where a = odd steps, k = even steps.
 *    If 3^a < 2^k (α < 1), the class is "dead" — all sufficiently large n shrink.
 *
 *    Method: simulate mod 2^k. At each step, check bit b of x:
 *      - bit b = 1 (odd): x ← (3x + 2^b) mod 2^k, a++
 *      - bit b = 0 (even): b++
 *    Stop when b = k (all k bits consumed). Total determined steps = a + k.
 *
 * 2. EXACT ANALYSIS: Simulate Collatz(r) with full precision for the small value r.
 *    If r drops below r, it's "exact-dead."
 *
 * Output files:
 *   sieve_k{K}_exact.bin   — bitmap, bit[r]=1 if exact-dead
 *   sieve_k{K}_class.bin   — bitmap, bit[r]=1 if class-dead (α < 1)
 *   sieve_k{K}_precomp.bin — per-odd-residue binary data for branch_locus integration
 *   sieve_k{K}_stats.csv   — per-residue CSV (k ≤ 20 only)
 *
 * Compile: gcc -O3 -march=native -fopenmp -o gen_sieve gen_sieve.c -lm
 * Usage:   ./gen_sieve -k 16 [-v]
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>

#define MAX_EXACT_STEPS 10000

/* Per-residue precomputed data */
typedef struct {
    uint16_t class_odd;    /* a: odd steps in determined sequence              */
    uint8_t  class_dead;   /* 1 if 3^a < 2^k (α < 1)                         */
    uint8_t  exact_dead;   /* 1 if exact Collatz(r) drops below r             */
    uint32_t exact_steps;  /* steps for exact drop (0 if didn't drop)         */
    uint64_t A_num;        /* 3^a (multiplier numerator)                      */
    uint64_t B_num;        /* additive constant numerator                     */
    /* For any n ≡ r (mod 2^k), after the determined steps:                    */
    /*   n_new = (A_num * n + B_num) >> k                                      */
} precomp_t;

int main(int argc, char **argv) {
    int k = 16;
    int verbose = 0;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-k") == 0 && i + 1 < argc)
            k = atoi(argv[++i]);
        else if (strcmp(argv[i], "-v") == 0)
            verbose = 1;
        else {
            fprintf(stderr, "Usage: %s -k <bits> [-v]\n", argv[0]);
            fprintf(stderr, "  -k <bits>  Sieve modulus 2^k (4 <= k <= 32)\n");
            return 1;
        }
    }

    if (k < 4 || k > 32) {
        fprintf(stderr, "Error: k=%d out of range [4,32]\n", k);
        return 1;
    }

    uint64_t mod = 1ULL << k;
    uint64_t mask = mod - 1;
    uint64_t n_odd = mod / 2;

    printf("=== Collatz Sieve Generator ===\n");
    printf("k = %d, modulus = 2^%d = %lu\n", k, k, mod);
    printf("Odd residues: %lu\n", n_odd);
    printf("Threads: %d\n", omp_get_max_threads());

    /* Class-dead threshold: a <= floor(k * log2/log3) means 3^a < 2^k */
    double log2_log3 = log(2.0) / log(3.0);
    int a_threshold = (int)(k * log2_log3);
    printf("Class-dead when a <= %d (k * log2/log3 = %.3f)\n\n", a_threshold, k * log2_log3);

    /* Allocate */
    precomp_t *data = calloc(n_odd, sizeof(precomp_t));
    if (!data) {
        fprintf(stderr, "Failed to allocate precomp (%lu bytes)\n",
                n_odd * sizeof(precomp_t));
        return 1;
    }

    uint64_t bitmap_bytes = mod / 8;
    uint8_t *exact_bmp = calloc(bitmap_bytes, 1);
    uint8_t *class_bmp = calloc(bitmap_bytes, 1);
    if (!exact_bmp || !class_bmp) {
        fprintf(stderr, "Failed to allocate bitmaps\n");
        return 1;
    }

    uint64_t class_dead_cnt = 0, exact_dead_cnt = 0;
    double t0 = omp_get_wtime();

    #pragma omp parallel reduction(+:class_dead_cnt, exact_dead_cnt)
    {
        #pragma omp for schedule(dynamic, 4096)
        for (uint64_t r = 1; r < mod; r += 2) {
            uint64_t idx = r / 2;

            /* ── CLASS ANALYSIS ──
             * Simulate mod 2^k.  Track (A, B) where value = (A*n + B) / 2^k.
             * Parity at each step = bit b of x, where x tracks (A*r + B) mod 2^k.
             * b counts even steps consumed.  Stop at b = k.
             */
            uint64_t x = r;
            int b = 0, a = 0;
            uint64_t A = 1, B = 0;

            while (b < k) {
                if ((x >> b) & 1) {
                    /* Odd step */
                    uint64_t shift = 1ULL << b;
                    x = (3 * x + shift) & mask;
                    A *= 3;
                    B = 3 * B + shift;
                    a++;
                } else {
                    /* Even step */
                    b++;
                }
            }

            int is_class_dead = (a <= a_threshold) ? 1 : 0;
            data[idx].class_odd   = (uint16_t)a;
            data[idx].class_dead  = is_class_dead;
            data[idx].A_num       = A;
            data[idx].B_num       = B;
            if (is_class_dead) class_dead_cnt++;

            /* ── EXACT ANALYSIS ──
             * Simulate Collatz(r) with full uint64 precision.
             */
            uint64_t val = r;
            uint32_t steps = 0;
            int dropped = 0;

            while (steps < MAX_EXACT_STEPS && val >= r) {
                if (val & 1)
                    val = 3 * val + 1;
                else
                    val >>= 1;
                steps++;
                if (val < r || (val == 1 && r > 1)) {
                    dropped = 1;
                    break;
                }
            }

            data[idx].exact_dead  = dropped ? 1 : 0;
            data[idx].exact_steps = dropped ? steps : 0;
            if (dropped) exact_dead_cnt++;
        }
    }

    double elapsed = omp_get_wtime() - t0;
    printf("Computation: %.2f seconds\n\n", elapsed);

    /* ── SUMMARY ── */
    printf("=== Results ===\n");
    printf("Class-dead (alpha < 1): %lu / %lu = %.4f%%\n",
           class_dead_cnt, n_odd, 100.0 * class_dead_cnt / n_odd);
    printf("Exact-dead (drops):     %lu / %lu = %.4f%%\n",
           exact_dead_cnt, n_odd, 100.0 * exact_dead_cnt / n_odd);

    uint64_t both = 0;
    for (uint64_t i = 0; i < n_odd; i++)
        if (data[i].class_dead && data[i].exact_dead) both++;
    printf("Both dead:              %lu / %lu = %.4f%%\n\n",
           both, n_odd, 100.0 * both / n_odd);

    /* ── ODD STEP DISTRIBUTION ── */
    printf("=== Odd Step Count (a) Distribution ===\n");
    int max_a = 0;
    for (uint64_t i = 0; i < n_odd; i++)
        if (data[i].class_odd > max_a) max_a = data[i].class_odd;

    uint64_t *a_hist = calloc(max_a + 1, sizeof(uint64_t));
    for (uint64_t i = 0; i < n_odd; i++)
        a_hist[data[i].class_odd]++;

    printf("  a    Count      %%     Cumul%%   alpha=3^a/2^%d\n", k);
    uint64_t cumul = 0;
    for (int av = 0; av <= max_a; av++) {
        if (a_hist[av] == 0) continue;
        cumul += a_hist[av];
        double alpha = pow(3.0, av) / pow(2.0, k);
        printf("  %-4d %8lu  %6.2f  %6.2f   %.6f%s\n",
               av, a_hist[av],
               100.0 * a_hist[av] / n_odd,
               100.0 * cumul / n_odd,
               alpha,
               (av == a_threshold) ? "  <-- threshold" : "");
    }
    free(a_hist);

    /* ── MOD-9 CROSS-REFERENCE ── */
    printf("\n=== Mod-9 Cross-Reference ===\n");
    uint64_t m9_tot[9] = {0}, m9_cd[9] = {0}, m9_ed[9] = {0};
    double m9_avg_a[9] = {0};
    for (uint64_t r = 1; r < mod; r += 2) {
        int m9 = r % 9;
        uint64_t idx = r / 2;
        m9_tot[m9]++;
        if (data[idx].class_dead) m9_cd[m9]++;
        if (data[idx].exact_dead) m9_ed[m9]++;
        m9_avg_a[m9] += data[idx].class_odd;
    }
    printf("Mod9  Total    ClassDead%%  ExactDead%%  Avg_a   Barina\n");
    for (int m = 0; m < 9; m++) {
        if (m9_tot[m] == 0) continue;
        const char *barina = "";
        if (m == 2 || m == 4 || m == 5 || m == 8) barina = "DEAD";
        printf("  %d   %6lu   %7.2f    %7.2f    %5.2f   %s\n",
               m, m9_tot[m],
               100.0 * m9_cd[m] / m9_tot[m],
               100.0 * m9_ed[m] / m9_tot[m],
               m9_avg_a[m] / m9_tot[m],
               barina);
    }

    /* ── MOD-3 SUMMARY ── */
    printf("\n=== Mod-3 Summary ===\n");
    for (int m3 = 0; m3 < 3; m3++) {
        uint64_t tot = 0, cd = 0;
        for (uint64_t r = 1; r < mod; r += 2) {
            if ((r % 3) == (uint64_t)m3) {
                tot++;
                if (data[r / 2].class_dead) cd++;
            }
        }
        if (tot > 0)
            printf("  n mod 3 = %d: %lu total, %.2f%% class-dead\n",
                   m3, tot, 100.0 * cd / tot);
    }

    /* ── DETERMINED STEPS & SPEEDUP ESTIMATE ── */
    printf("\n=== Branch_locus Speedup Estimate ===\n");
    double avg_det = 0, avg_a_all = 0;
    for (uint64_t i = 0; i < n_odd; i++) {
        avg_det += data[i].class_odd + k;
        avg_a_all += data[i].class_odd;
    }
    avg_det /= n_odd;
    avg_a_all /= n_odd;

    double avg_traj = 70.0;  /* typical for N ~ 100B */
    double skip_frac = avg_det / avg_traj;
    if (skip_frac > 1.0) skip_frac = 1.0;

    printf("Average odd steps (a): %.2f\n", avg_a_all);
    printf("Average determined steps (a + k): %.1f\n", avg_det);
    printf("Typical trajectory length: ~%.0f steps\n", avg_traj);
    printf("Pre-computable fraction: %.1f%%\n", 100.0 * skip_frac);
    printf("\nFor class-dead residues (%.1f%%), trajectory is guaranteed to shrink.\n",
           100.0 * class_dead_cnt / n_odd);
    printf("Integration: replace first %d+ Collatz steps with:\n", k);
    printf("  n_new = (A_num * n + B_num) >> %d\n", k);
    printf("  (one multiply + one add + one shift per trajectory)\n");

    /* ── WRITE BITMAPS (serial, since bits in same byte) ── */
    for (uint64_t r = 1; r < mod; r += 2) {
        uint64_t idx = r / 2;
        uint8_t bit = 1 << (r & 7);
        uint64_t byte_idx = r >> 3;
        if (data[idx].exact_dead) exact_bmp[byte_idx] |= bit;
        if (data[idx].class_dead) class_bmp[byte_idx] |= bit;
    }

    char fname[256];

    snprintf(fname, sizeof(fname), "sieve_k%d_exact.bin", k);
    FILE *f = fopen(fname, "wb");
    if (f) { fwrite(exact_bmp, 1, bitmap_bytes, f); fclose(f); }
    printf("\nWrote %s (%lu bytes)\n", fname, bitmap_bytes);

    snprintf(fname, sizeof(fname), "sieve_k%d_class.bin", k);
    f = fopen(fname, "wb");
    if (f) { fwrite(class_bmp, 1, bitmap_bytes, f); fclose(f); }
    printf("Wrote %s (%lu bytes)\n", fname, bitmap_bytes);

    snprintf(fname, sizeof(fname), "sieve_k%d_precomp.bin", k);
    f = fopen(fname, "wb");
    if (f) {
        fwrite(&k, sizeof(int), 1, f);
        fwrite(&n_odd, sizeof(uint64_t), 1, f);
        fwrite(data, sizeof(precomp_t), n_odd, f);
        fclose(f);
    }
    printf("Wrote %s (%lu bytes)\n", fname,
           (uint64_t)sizeof(int) + sizeof(uint64_t) + n_odd * sizeof(precomp_t));

    /* Per-residue CSV for small k */
    if (k <= 20) {
        snprintf(fname, sizeof(fname), "sieve_k%d_stats.csv", k);
        f = fopen(fname, "w");
        if (f) {
            fprintf(f, "residue,class_odd,class_dead,exact_dead,exact_steps,"
                       "alpha,mod9,mod3\n");
            for (uint64_t r = 1; r < mod; r += 2) {
                uint64_t idx = r / 2;
                double alpha = (double)data[idx].A_num / (double)mod;
                fprintf(f, "%lu,%u,%u,%u,%u,%.8f,%lu,%lu\n",
                        r, data[idx].class_odd,
                        data[idx].class_dead, data[idx].exact_dead,
                        data[idx].exact_steps, alpha, r % 9, r % 3);
            }
            fclose(f);
            printf("Wrote %s\n", fname);
        }
    }

    free(data);
    free(exact_bmp);
    free(class_bmp);

    printf("\nDone.\n");
    return 0;
}
