/*
 * profinite_compat.c
 *
 * Profinite Compatibility Test for Collatz Winding Numbers
 *
 * Computes torus residue distributions mu_k(a,b) for all levels
 * k = 2^a * 3^b (0 <= a,b <= 4), verifies the inverse limit
 * compatibility condition, and reports entropy/forbidden-cell
 * diagnostics supporting the solenoid formulation Sigma_{2,3}.
 *
 * Architecture: streaming accumulation.  For each n in [2,N],
 * compute (nu2, nu3) via Collatz iteration, then immediately
 * increment all 25 distribution grids.  No per-trajectory storage.
 *
 * Usage: ./profinite_compat [N]   (default N = 10000000)
 *
 * Compile: gcc -O3 -march=native -o profinite_compat profinite_compat.c -lm
 */

#define _DEFAULT_SOURCE
#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>

/* ── Constants ──────────────────────────────────────────────────────── */

#define MAX_EXP      4
#define NUM_LEVELS   ((MAX_EXP + 1) * (MAX_EXP + 1))   /* 25 */
#define MAX_PAIRS    300
#define NUM_CHKPTS   4

/* ── Structures ─────────────────────────────────────────────────────── */

typedef struct {
    int k, a, b;
    int64_t *grid;          /* k × k flat array of counts */
} level_t;

typedef struct {
    int idx_lo, idx_hi;     /* indices into levels[] */
    int k_lo, k_hi;
} pair_t;

typedef struct {
    int k, a, b;
    int64_t cells, nonzero, zero_cells, suppressed;
    double  zero_frac, H, H_max, H_ratio;
    double  max_dens, min_dens;
} diag_t;

/* ── Global state ──────────────────────────────────────────────────── */

static int64_t  N;
static int      num_levels, num_pairs;
static level_t  levels[NUM_LEVELS];
static pair_t   pairs[MAX_PAIRS];
static diag_t   diagnostics[NUM_LEVELS];

static int64_t  total_trajs, total_steps;
static int32_t  nu2_max, nu3_max;
static double   mean_traj_len;

/* Compatibility results */
static int64_t  compat_errors[MAX_PAIRS];
static int      compat_pass[MAX_PAIRS];

/* Index of the k=3 level (for mu_3(1,1) tracking) */
static int      lev3_idx = -1;

/* Checkpoints: snapshot mu_3(1,1) at powers of 10 */
static int64_t  chk_N[NUM_CHKPTS]     = {1000000, 10000000, 100000000, 1000000000};
static int64_t  chk_mu3_11[NUM_CHKPTS];
static int64_t  chk_total[NUM_CHKPTS];
static int      num_chk_hit;

/* ── Timer utility ─────────────────────────────────────────────────── */

static struct timespec _ts;
static void tic(void) { clock_gettime(CLOCK_MONOTONIC, &_ts); }
static double toc(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (now.tv_sec - _ts.tv_sec) + 1e-9 * (now.tv_nsec - _ts.tv_nsec);
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 1: Initialise levels  k = 2^a * 3^b
 * ═══════════════════════════════════════════════════════════════════════ */

static void init_levels(void)
{
    num_levels = 0;
    for (int b = 0; b <= MAX_EXP; b++) {
        for (int a = 0; a <= MAX_EXP; a++) {
            int k = 1;
            for (int i = 0; i < a; i++) k *= 2;
            for (int i = 0; i < b; i++) k *= 3;
            levels[num_levels].k = k;
            levels[num_levels].a = a;
            levels[num_levels].b = b;
            levels[num_levels].grid = NULL;
            num_levels++;
        }
    }

    /* Sort by k (bubble sort, only 25 elements) */
    for (int i = 0; i < num_levels - 1; i++)
        for (int j = i + 1; j < num_levels; j++)
            if (levels[i].k > levels[j].k) {
                level_t tmp = levels[i];
                levels[i] = levels[j];
                levels[j] = tmp;
            }

    /* Allocate grids */
    int64_t total_cells = 0;
    for (int i = 0; i < num_levels; i++) {
        int k = levels[i].k;
        int64_t sz = (int64_t)k * k;
        levels[i].grid = (int64_t *)calloc(sz, sizeof(int64_t));
        if (!levels[i].grid) {
            fprintf(stderr, "Failed to allocate grid for k=%d (%ld cells)\n",
                    k, (long)sz);
            exit(1);
        }
        total_cells += sz;
        if (k == 3) lev3_idx = i;
    }

    printf("  %d levels, total grid cells: %ld (%.1f MB)\n",
           num_levels, (long)total_cells,
           total_cells * 8.0 / (1024 * 1024));

    printf("\n  %-6s  %-8s  %-10s\n", "k", "(a,b)", "cells");
    printf("  ─────────────────────────────\n");
    for (int i = 0; i < num_levels; i++)
        printf("  %-6d  (2^%d*3^%d)  %-10ld\n",
               levels[i].k, levels[i].a, levels[i].b,
               (long)levels[i].k * levels[i].k);
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 2: Initialise divisibility pairs
 * ═══════════════════════════════════════════════════════════════════════ */

static void init_pairs(void)
{
    num_pairs = 0;
    for (int i = 0; i < num_levels; i++)
        for (int j = i + 1; j < num_levels; j++)
            if (levels[i].a <= levels[j].a && levels[i].b <= levels[j].b) {
                pairs[num_pairs].idx_lo = i;
                pairs[num_pairs].idx_hi = j;
                pairs[num_pairs].k_lo   = levels[i].k;
                pairs[num_pairs].k_hi   = levels[j].k;
                num_pairs++;
            }

    printf("  %d divisibility pairs\n", num_pairs);
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 3: Compute trajectories (streaming accumulation)
 * ═══════════════════════════════════════════════════════════════════════ */

static void compute_trajectories(void)
{
    printf("\nComputing winding pairs for n in [2, %ld]...\n", (long)N);
    tic();

    total_trajs = 0;
    total_steps = 0;
    nu2_max = 0;
    nu3_max = 0;
    num_chk_hit = 0;

    int64_t progress_interval = N / 10;
    if (progress_interval < 10000) progress_interval = 10000;
    int64_t next_progress = progress_interval;
    int     next_chk = 0;

    /* Skip checkpoints larger than N */
    while (next_chk < NUM_CHKPTS && chk_N[next_chk] < 2)
        next_chk++;

    for (int64_t n = 2; n <= N; n++) {
        uint64_t x = (uint64_t)n;
        int32_t nu2 = 0, nu3 = 0;

        while (x != 1) {
            if (x & 1) {
                x = 3 * x + 1;
                nu3++;
            } else {
                x >>= 1;
                nu2++;
            }
        }

        if (nu2 > nu2_max) nu2_max = nu2;
        if (nu3 > nu3_max) nu3_max = nu3;
        total_steps += nu2 + nu3;

        /* Accumulate into all 25 grids */
        for (int lev = 0; lev < num_levels; lev++) {
            int k = levels[lev].k;
            int r2 = nu2 % k;
            int r3 = nu3 % k;
            levels[lev].grid[r2 * k + r3]++;
        }

        total_trajs++;

        /* Checkpoint */
        if (next_chk < NUM_CHKPTS && n == chk_N[next_chk]) {
            chk_total[next_chk] = total_trajs;
            chk_mu3_11[next_chk] = (lev3_idx >= 0)
                ? levels[lev3_idx].grid[1 * 3 + 1] : -1;
            printf("  Checkpoint N = %ld:  mu_3(1,1) = %ld\n",
                   (long)chk_N[next_chk], (long)chk_mu3_11[next_chk]);
            num_chk_hit++;
            next_chk++;
        }

        /* Progress */
        if (n >= next_progress) {
            double dt = toc();
            printf("  n = %ld (%.0f%%)  %.1fs\n",
                   (long)n, 100.0 * n / N, dt);
            next_progress += progress_interval;
        }
    }

    mean_traj_len = (double)total_steps / total_trajs;
    double dt = toc();
    printf("  Done in %.1fs.  (%ld trajectories)\n", dt, (long)total_trajs);
    printf("  nu2 range: [0, %d],  nu3 range: [0, %d]\n", nu2_max, nu3_max);
    printf("  Mean trajectory length: %.1f steps\n", mean_traj_len);
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 4: Verify profinite compatibility
 *
 * For each pair k | k', compute the marginal of mu_{k'} at level k
 * and check that it equals mu_k exactly.
 * ═══════════════════════════════════════════════════════════════════════ */

static int verify_compatibility(void)
{
    printf("\n========================================================================\n");
    printf("PROFINITE COMPATIBILITY TEST\n");
    printf("========================================================================\n");
    printf("For each pair k | k', verify:\n");
    printf("  mu_k(a,b) = Sum_{a'=a, b'=b mod k} mu_{k'}(a',b')\n\n");
    tic();

    int all_pass = 1;

    for (int p = 0; p < num_pairs; p++) {
        int lo = pairs[p].idx_lo;
        int hi = pairs[p].idx_hi;
        int k  = levels[lo].k;
        int kp = levels[hi].k;

        /* Compute marginal of mu_{k'} projected to level k */
        int64_t *marginal = (int64_t *)calloc((size_t)k * k, sizeof(int64_t));
        if (!marginal) { fprintf(stderr, "alloc failed\n"); exit(1); }

        for (int ap = 0; ap < kp; ap++) {
            int a_mod = ap % k;
            for (int bp = 0; bp < kp; bp++) {
                marginal[a_mod * k + (bp % k)] +=
                    levels[hi].grid[ap * kp + bp];
            }
        }

        /* Compare with mu_k */
        int64_t max_err = 0;
        for (int c = 0; c < k * k; c++) {
            int64_t diff = levels[lo].grid[c] - marginal[c];
            if (diff < 0) diff = -diff;
            if (diff > max_err) max_err = diff;
        }

        compat_errors[p] = max_err;
        compat_pass[p]   = (max_err == 0);
        if (max_err != 0) all_pass = 0;

        free(marginal);
    }

    double dt = toc();

    /* Print results */
    int n_pass = 0, n_fail = 0;
    for (int p = 0; p < num_pairs; p++) {
        if (compat_pass[p]) n_pass++; else n_fail++;
    }

    /* Print a sample of pairs */
    printf("  Sample pairs (showing k <= 27):\n");
    for (int p = 0; p < num_pairs; p++) {
        if (pairs[p].k_lo <= 27 && pairs[p].k_hi <= 81) {
            int lo = pairs[p].idx_lo;
            int hi = pairs[p].idx_hi;
            printf("    %4d (2^%d*3^%d) | %4d (2^%d*3^%d)  "
                   "ratio=%4d  max|D|=%ld  [%s]\n",
                   pairs[p].k_lo, levels[lo].a, levels[lo].b,
                   pairs[p].k_hi, levels[hi].a, levels[hi].b,
                   pairs[p].k_hi / pairs[p].k_lo,
                   (long)compat_errors[p],
                   compat_pass[p] ? "PASS" : "FAIL");
        }
    }

    /* Print any failures */
    if (!all_pass) {
        printf("\n  *** FAILURES ***\n");
        for (int p = 0; p < num_pairs; p++)
            if (!compat_pass[p])
                printf("    FAILED: %d | %d, max error = %ld\n",
                       pairs[p].k_lo, pairs[p].k_hi,
                       (long)compat_errors[p]);
    }

    printf("\n  Done in %.2fs.\n", dt);
    printf("  Results: %d PASS, %d FAIL (out of %d pairs)\n",
           n_pass, n_fail, num_pairs);

    if (all_pass)
        printf("\n  *** ALL %d COMPATIBILITY CONDITIONS SATISFIED ***\n",
               num_pairs);

    return all_pass;
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 5: Compute per-level diagnostics
 * ═══════════════════════════════════════════════════════════════════════ */

static void compute_diagnostics(void)
{
    for (int lev = 0; lev < num_levels; lev++) {
        int k = levels[lev].k;
        int64_t ncells = (int64_t)k * k;
        int64_t *grid  = levels[lev].grid;
        diag_t  *d     = &diagnostics[lev];

        d->k = k;
        d->a = levels[lev].a;
        d->b = levels[lev].b;
        d->cells = ncells;

        /* Count nonzero and total */
        int64_t nz = 0, total = 0;
        for (int64_t c = 0; c < ncells; c++) {
            if (grid[c] > 0) nz++;
            total += grid[c];
        }
        d->nonzero    = nz;
        d->zero_cells = ncells - nz;
        d->zero_frac  = (double)(ncells - nz) / ncells;

        /* Density extremes */
        double max_d = 0, min_d = 1.0;
        for (int64_t c = 0; c < ncells; c++) {
            double dens = (double)grid[c] / total;
            if (dens > max_d) max_d = dens;
            if (grid[c] > 0 && dens < min_d) min_d = dens;
        }
        d->max_dens = max_d;
        d->min_dens = (nz > 0) ? min_d : 0;

        /* Shannon entropy */
        double H = 0;
        for (int64_t c = 0; c < ncells; c++) {
            if (grid[c] > 0) {
                double p = (double)grid[c] / total;
                H -= p * log2(p);
            }
        }
        d->H     = H;
        d->H_max = (ncells > 1) ? log2((double)ncells) : 0;
        d->H_ratio = (d->H_max > 0) ? H / d->H_max : 1.0;

        /* Suppressed cells: 0 < count < expected/100 */
        double expected = (double)total / ncells;
        int64_t supp = 0;
        for (int64_t c = 0; c < ncells; c++)
            if (grid[c] > 0 && (double)grid[c] < expected / 100.0)
                supp++;
        d->suppressed = supp;
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 6: Print diagnostics and forbidden cell report
 * ═══════════════════════════════════════════════════════════════════════ */

static void print_diagnostics(void)
{
    printf("\n========================================================================\n");
    printf("DETAILED DIAGNOSTICS\n");
    printf("========================================================================\n");

    printf("\n  %-6s  %-10s  %8s  %8s  %8s  %9s  %10s\n",
           "k", "(a,b)", "cells", "nonzero", "zero", "zero_frac", "H/H_max");
    printf("  ────────────────────────────────────────────────────────────────────\n");

    for (int lev = 0; lev < num_levels; lev++) {
        diag_t *d = &diagnostics[lev];
        if (d->k == 1) continue;
        printf("  %-6d  (2^%d*3^%d)   %8ld  %8ld  %8ld  %8.4f%%  %10.6f\n",
               d->k, d->a, d->b,
               (long)d->cells, (long)d->nonzero, (long)d->zero_cells,
               d->zero_frac * 100.0, d->H_ratio);
    }
}

static void report_forbidden_cells(void)
{
    printf("\n========================================================================\n");
    printf("FORBIDDEN / SUPPRESSED CELLS\n");
    printf("========================================================================\n");

    /* Highlight mu_3(1,1) */
    if (lev3_idx >= 0) {
        int64_t val = levels[lev3_idx].grid[1 * 3 + 1];
        int64_t total = 0;
        for (int c = 0; c < 9; c++) total += levels[lev3_idx].grid[c];
        double expected = (double)total / 9.0;
        printf("\n  *** mu_3(1,1) = %ld  (expected ~%.0f under uniformity) ***\n",
               (long)val, expected);
        if (val == 0)
            printf("  Confirmed: (nu2, nu3) = (1,1) mod 3 is FORBIDDEN.\n");
    }

    /* Per-level forbidden/suppressed summary */
    printf("\n  %-6s  %-10s  %10s  %10s  %10s  %10s\n",
           "k", "(a,b)", "cells", "zero", "supp(<1%%)", "zero_frac");
    printf("  ─────────────────────────────────────────────────────────────────\n");

    for (int lev = 0; lev < num_levels; lev++) {
        diag_t *d = &diagnostics[lev];
        if (d->k == 1) continue;
        printf("  %-6d  (2^%d*3^%d)   %10ld  %10ld  %10ld  %9.4f%%\n",
               d->k, d->a, d->b,
               (long)d->cells, (long)d->zero_cells,
               (long)d->suppressed, d->zero_frac * 100.0);
    }

    /* List specific forbidden cells for small k where expected >> 1 */
    printf("\n  Forbidden cells at levels with expected count > 100:\n");
    for (int lev = 0; lev < num_levels; lev++) {
        int k = levels[lev].k;
        if (k == 1) continue;
        int64_t ncells = (int64_t)k * k;
        int64_t total = 0;
        for (int64_t c = 0; c < ncells; c++) total += levels[lev].grid[c];
        double expected = (double)total / ncells;

        if (expected < 100.0) continue;

        int printed_header = 0;
        int count = 0;
        for (int i = 0; i < k; i++) {
            for (int j = 0; j < k; j++) {
                if (levels[lev].grid[i * k + j] == 0) {
                    if (!printed_header) {
                        printf("\n    k = %d (2^%d*3^%d), expected = %.0f:\n",
                               k, levels[lev].a, levels[lev].b, expected);
                        printed_header = 1;
                    }
                    if (count < 20)
                        printf("      (%d, %d)\n", i, j);
                    count++;
                }
            }
        }
        if (count > 20)
            printf("      ... and %d more\n", count - 20);
        if (printed_header)
            printf("      Total zero cells: %d\n", count);
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 7: Write CSV files
 * ═══════════════════════════════════════════════════════════════════════ */

static void write_csv_files(int all_pass)
{
    printf("\n========================================================================\n");
    printf("WRITING CSV FILES\n");
    printf("========================================================================\n");

    /* 1. profinite_params.csv */
    {
        FILE *f = fopen("profinite_params.csv", "w");
        if (!f) { perror("profinite_params.csv"); return; }
        fprintf(f, "key,value\n");
        fprintf(f, "N,%ld\n", (long)N);
        fprintf(f, "nu2_max,%d\n", nu2_max);
        fprintf(f, "nu3_max,%d\n", nu3_max);
        fprintf(f, "mean_traj_len,%.2f\n", mean_traj_len);
        fprintf(f, "num_levels,%d\n", num_levels);
        fprintf(f, "num_pairs,%d\n", num_pairs);
        fprintf(f, "total_trajs,%ld\n", (long)total_trajs);
        fprintf(f, "all_pass,%d\n", all_pass);
        fclose(f);
        printf("  Saved profinite_params.csv\n");
    }

    /* 2. profinite_diagnostics.csv */
    {
        FILE *f = fopen("profinite_diagnostics.csv", "w");
        if (!f) { perror("profinite_diagnostics.csv"); return; }
        fprintf(f, "k,a,b,cells,nonzero,zero_cells,zero_frac,"
                   "H,H_max,H_ratio,max_dens,min_dens,suppressed\n");
        for (int lev = 0; lev < num_levels; lev++) {
            diag_t *d = &diagnostics[lev];
            fprintf(f, "%d,%d,%d,%ld,%ld,%ld,%.9f,%.9f,%.9f,%.9f,"
                       "%.9f,%.9f,%ld\n",
                    d->k, d->a, d->b,
                    (long)d->cells, (long)d->nonzero, (long)d->zero_cells,
                    d->zero_frac, d->H, d->H_max, d->H_ratio,
                    d->max_dens, d->min_dens, (long)d->suppressed);
        }
        fclose(f);
        printf("  Saved profinite_diagnostics.csv\n");
    }

    /* 3. profinite_compat_results.csv */
    {
        FILE *f = fopen("profinite_compat_results.csv", "w");
        if (!f) { perror("profinite_compat_results.csv"); return; }
        fprintf(f, "k,kp,max_error,pass\n");
        for (int p = 0; p < num_pairs; p++)
            fprintf(f, "%d,%d,%ld,%d\n",
                    pairs[p].k_lo, pairs[p].k_hi,
                    (long)compat_errors[p], compat_pass[p]);
        fclose(f);
        printf("  Saved profinite_compat_results.csv\n");
    }

    /* 4. profinite_mu_k.csv — full grids for k <= 36 */
    {
        FILE *f = fopen("profinite_mu_k.csv", "w");
        if (!f) { perror("profinite_mu_k.csv"); return; }
        fprintf(f, "k,i,j,count\n");
        for (int lev = 0; lev < num_levels; lev++) {
            int k = levels[lev].k;
            if (k > 36) continue;
            for (int i = 0; i < k; i++)
                for (int j = 0; j < k; j++)
                    fprintf(f, "%d,%d,%d,%ld\n",
                            k, i, j,
                            (long)levels[lev].grid[i * k + j]);
        }
        fclose(f);
        printf("  Saved profinite_mu_k.csv\n");
    }

    /* 5. profinite_forbidden.csv */
    {
        FILE *f = fopen("profinite_forbidden.csv", "w");
        if (!f) { perror("profinite_forbidden.csv"); return; }
        fprintf(f, "k,a,b,i,j,count,expected,type\n");
        for (int lev = 0; lev < num_levels; lev++) {
            int k = levels[lev].k;
            if (k == 1) continue;
            int64_t ncells = (int64_t)k * k;
            int64_t total = 0;
            for (int64_t c = 0; c < ncells; c++)
                total += levels[lev].grid[c];
            double expected = (double)total / ncells;

            /* Only include levels where expected > 1 */
            if (expected < 1.0) continue;

            for (int i = 0; i < k; i++)
                for (int j = 0; j < k; j++) {
                    int64_t cnt = levels[lev].grid[i * k + j];
                    if (cnt == 0)
                        fprintf(f, "%d,%d,%d,%d,%d,%ld,%.1f,zero\n",
                                k, levels[lev].a, levels[lev].b,
                                i, j, (long)cnt, expected);
                    else if ((double)cnt < expected / 100.0)
                        fprintf(f, "%d,%d,%d,%d,%d,%ld,%.1f,suppressed\n",
                                k, levels[lev].a, levels[lev].b,
                                i, j, (long)cnt, expected);
                }
        }
        fclose(f);
        printf("  Saved profinite_forbidden.csv\n");
    }

    /* 6. profinite_checkpoints.csv */
    {
        FILE *f = fopen("profinite_checkpoints.csv", "w");
        if (!f) { perror("profinite_checkpoints.csv"); return; }
        fprintf(f, "checkpoint_N,total_trajs,mu3_11\n");
        for (int c = 0; c < num_chk_hit; c++)
            fprintf(f, "%ld,%ld,%ld\n",
                    (long)chk_N[c], (long)chk_total[c],
                    (long)chk_mu3_11[c]);
        fclose(f);
        printf("  Saved profinite_checkpoints.csv\n");
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * main
 * ═══════════════════════════════════════════════════════════════════════ */

int main(int argc, char **argv)
{
    N = (argc > 1) ? atol(argv[1]) : 10000000;
    if (N < 3) { fprintf(stderr, "N must be >= 3\n"); return 1; }

    struct timespec wall_start;
    clock_gettime(CLOCK_MONOTONIC, &wall_start);

    printf("========================================================================\n");
    printf("PROFINITE COMPATIBILITY TEST FOR COLLATZ WINDING NUMBERS\n");
    printf("========================================================================\n");
    printf("N = %ld\n", (long)N);
    printf("Levels: k = 2^a * 3^b  (0 <= a,b <= %d)\n\n", MAX_EXP);

    printf("Initialising levels...\n");
    init_levels();

    printf("\nInitialising divisibility pairs...\n");
    init_pairs();

    compute_trajectories();

    int all_pass = verify_compatibility();
    compute_diagnostics();
    print_diagnostics();
    report_forbidden_cells();
    write_csv_files(all_pass);

    /* Checkpoint summary */
    if (num_chk_hit > 0) {
        printf("\n========================================================================\n");
        printf("CHECKPOINT SUMMARY: mu_3(1,1)\n");
        printf("========================================================================\n");
        for (int c = 0; c < num_chk_hit; c++)
            printf("  N = %12ld:  mu_3(1,1) = %ld\n",
                   (long)chk_N[c], (long)chk_mu3_11[c]);
        if (lev3_idx >= 0 && levels[lev3_idx].grid[1 * 3 + 1] == 0)
            printf("\n  mu_3(1,1) = 0 persists at all checkpoints.\n");
    }

    /* Cleanup */
    for (int i = 0; i < num_levels; i++)
        free(levels[i].grid);

    struct timespec wall_end;
    clock_gettime(CLOCK_MONOTONIC, &wall_end);
    double wall = (wall_end.tv_sec - wall_start.tv_sec)
                + 1e-9 * (wall_end.tv_nsec - wall_start.tv_nsec);
    printf("\nTotal wall time: %.2fs\n", wall);

    return 0;
}
