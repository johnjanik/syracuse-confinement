/*
 * branch_locus_sieved.c — Proof-of-concept: sieve-accelerated branch_locus
 *
 * Demonstrates the sieve fast-forward optimization on branch_locus workloads.
 * Runs TWO passes:
 *   1. UNSIEVED: standard branch_locus inner loop (reference)
 *   2. SIEVED:   fast-forward the first (a+k) determined steps via precomputed
 *                sieve, then iterate normally for the remaining steps
 *
 * After both passes, compares all grid cells for exact match.
 *
 * Uses a subset of branch_locus levels (k up to 81) for speed.
 * No checkpointing, no CSV output — just correctness + timing.
 *
 * Compile: gcc -O3 -march=native -fopenmp -o branch_locus_sieved branch_locus_sieved.c -lm
 * Usage:   ./branch_locus_sieved [N] [-k sieve_bits]
 *          Default: N=10000000, sieve_bits=16
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <omp.h>

/* ── Sieve data ────────────────────────────────────────────────────── */

typedef struct {
    uint16_t class_odd;
    uint8_t  class_dead;
    uint8_t  exact_dead;
    uint32_t exact_steps;
    uint64_t A_num;
    uint64_t B_num;
} precomp_t;

static precomp_t *sieve_data;
static int SIEVE_K;
static uint64_t SIEVE_MOD, SIEVE_MASK;

static int load_sieve(int k) {
    char fname[256];
    snprintf(fname, sizeof(fname), "sieve_k%d_precomp.bin", k);
    FILE *f = fopen(fname, "rb");
    if (!f) { fprintf(stderr, "Cannot open %s\n", fname); return 0; }

    int k_file;
    uint64_t n_odd;
    if (fread(&k_file, sizeof(int), 1, f) != 1 ||
        fread(&n_odd, sizeof(uint64_t), 1, f) != 1) {
        fclose(f); return 0;
    }
    if (k_file != k) { fprintf(stderr, "Sieve k mismatch\n"); fclose(f); return 0; }

    sieve_data = malloc(n_odd * sizeof(precomp_t));
    if (!sieve_data) { fprintf(stderr, "OOM for sieve\n"); fclose(f); return 0; }
    if (fread(sieve_data, sizeof(precomp_t), n_odd, f) != n_odd) {
        fclose(f); free(sieve_data); return 0;
    }
    fclose(f);

    SIEVE_K = k;
    SIEVE_MOD = 1ULL << k;
    SIEVE_MASK = SIEVE_MOD - 1;
    return 1;
}

/* ── Level configuration ───────────────────────────────────────────── */

#define MAX_LEVELS 32
#define PRIVATE_K_THRESHOLD 162

typedef struct {
    int k;
    int64_t *even_grid;
    int64_t *odd_grid;
} level_t;

static int num_levels;
static level_t levels_ref[MAX_LEVELS];   /* reference (unsieved) */
static level_t levels_siev[MAX_LEVELS];  /* sieved */

/* Generate levels: k = 2^a * 3^b for 0 <= a,b <= 4, plus k=729 */
static void init_levels(level_t lvls[]) {
    num_levels = 0;
    for (int b = 0; b <= 4; b++) {
        for (int a = 0; a <= 4; a++) {
            int k = 1;
            for (int i = 0; i < a; i++) k *= 2;
            for (int i = 0; i < b; i++) k *= 3;
            lvls[num_levels].k = k;
            num_levels++;
        }
    }
    /* Add k=729 (Diophantine level) */
    int has729 = 0;
    for (int i = 0; i < num_levels; i++)
        if (lvls[i].k == 729) has729 = 1;
    if (!has729) {
        lvls[num_levels].k = 729;
        num_levels++;
    }

    /* Sort by k */
    for (int i = 0; i < num_levels - 1; i++)
        for (int j = i + 1; j < num_levels; j++)
            if (lvls[i].k > lvls[j].k) {
                level_t tmp = lvls[i]; lvls[i] = lvls[j]; lvls[j] = tmp;
            }

    /* Allocate grids */
    for (int i = 0; i < num_levels; i++) {
        int64_t sz = (int64_t)lvls[i].k * lvls[i].k;
        lvls[i].even_grid = calloc(sz, sizeof(int64_t));
        lvls[i].odd_grid  = calloc(sz, sizeof(int64_t));
    }
}

/* ── Precomputed parity sequences for sieve fast-forward ──────────── */

/* For each odd residue r mod 2^SIEVE_K, the first (a+k) Collatz steps have
 * a known parity sequence. We need this to update the (r2, r3) residues and
 * grid cells correctly during the fast-forward.
 *
 * We precompute: for each residue, the number of even steps (= SIEVE_K)
 * and the number of odd steps (= class_odd). The running residues after
 * the determined steps are r2_after = SIEVE_K mod level_k, r3_after = class_odd mod level_k.
 *
 * For grid updates during the fast-forward: we need to know which cells are
 * visited. Since all trajectories start at (r2=0, r3=0), and the parity
 * sequence for the first (a+k) steps is known per residue class, we can
 * precompute the cell visit pattern once per class.
 *
 * Strategy: precompute per-residue, per-level grid increment arrays.
 * For k=16 with 32K residues and 26 levels, this is ~26 * 32K * sizeof(pair) ≈ small.
 * But actually we need the FULL visit pattern, not just endpoints.
 *
 * Simpler approach: replay the determined parity sequence per-trajectory.
 * This avoids precomputing large tables and is still faster than full Collatz
 * because we skip the expensive 3x+1 arithmetic and just walk the known parities.
 */

/* Per-residue parity bitmap: bit i = 1 means step i is odd.
 * Max determined steps = SIEVE_K + max_a ≈ 2*SIEVE_K.
 * For k=16: max 32 steps → 1 uint32_t per residue.
 * For k=24: max 48 steps → 1 uint64_t per residue.
 * For k=32: max 64 steps → 1 uint64_t per residue.
 */
static uint64_t *parity_bitmaps;  /* one per odd residue */
static uint16_t *total_det_steps; /* a + SIEVE_K per residue */

static void precompute_parity_bitmaps(void) {
    uint64_t n_odd = SIEVE_MOD / 2;
    parity_bitmaps = calloc(n_odd, sizeof(uint64_t));
    total_det_steps = calloc(n_odd, sizeof(uint16_t));

    #pragma omp parallel for schedule(dynamic, 4096)
    for (uint64_t r = 1; r < SIEVE_MOD; r += 2) {
        uint64_t idx = r / 2;
        uint64_t x = r;
        int b = 0, a = 0, step = 0;
        uint64_t bitmap = 0;

        while (b < SIEVE_K) {
            if ((x >> b) & 1) {
                /* Odd step */
                bitmap |= (1ULL << step);
                uint64_t shift = 1ULL << b;
                x = (3 * x + shift) & SIEVE_MASK;
                a++;
            } else {
                /* Even step */
                b++;
            }
            step++;
        }

        parity_bitmaps[idx] = bitmap;
        total_det_steps[idx] = (uint16_t)step;
    }
}

/* ── Unsieved pass ─────────────────────────────────────────────────── */

static void run_unsieved(int64_t N) {
    int split = 0;
    int ks[MAX_LEVELS];
    for (int i = 0; i < num_levels; i++) {
        ks[i] = levels_ref[i].k;
        if (ks[i] <= PRIVATE_K_THRESHOLD) split = i + 1;
    }

    int nthreads = omp_get_max_threads();

    /* Per-thread private grids */
    int64_t **thr_pe = calloc(nthreads * split, sizeof(int64_t *));
    int64_t **thr_po = calloc(nthreads * split, sizeof(int64_t *));
    for (int t = 0; t < nthreads; t++)
        for (int lev = 0; lev < split; lev++) {
            int64_t sz = (int64_t)ks[lev] * ks[lev];
            thr_pe[t * split + lev] = calloc(sz, sizeof(int64_t));
            thr_po[t * split + lev] = calloc(sz, sizeof(int64_t));
        }

    int64_t *eg[MAX_LEVELS], *og[MAX_LEVELS];
    for (int i = 0; i < num_levels; i++) {
        eg[i] = levels_ref[i].even_grid;
        og[i] = levels_ref[i].odd_grid;
    }

    int64_t total_steps = 0;

    #pragma omp parallel reduction(+:total_steps)
    {
        int tid = omp_get_thread_num();
        int64_t *pe[MAX_LEVELS], *po[MAX_LEVELS];
        for (int lev = 0; lev < split; lev++) {
            pe[lev] = thr_pe[tid * split + lev];
            po[lev] = thr_po[tid * split + lev];
        }

        #pragma omp for schedule(dynamic, 256)
        for (int64_t n = 2; n <= N; n++) {
            int r2[MAX_LEVELS], r3[MAX_LEVELS];
            for (int lev = 0; lev < num_levels; lev++) {
                r2[lev] = 0; r3[lev] = 0;
            }

            uint64_t x = (uint64_t)n;
            while (x != 1) {
                int is_odd = x & 1;
                for (int lev = 0; lev < split; lev++) {
                    int idx = r2[lev] * ks[lev] + r3[lev];
                    if (is_odd) {
                        po[lev][idx]++;
                        if (++r3[lev] == ks[lev]) r3[lev] = 0;
                    } else {
                        pe[lev][idx]++;
                        if (++r2[lev] == ks[lev]) r2[lev] = 0;
                    }
                }
                for (int lev = split; lev < num_levels; lev++) {
                    int idx = r2[lev] * ks[lev] + r3[lev];
                    if (is_odd) {
                        __atomic_fetch_add(&og[lev][idx], 1, __ATOMIC_RELAXED);
                        if (++r3[lev] == ks[lev]) r3[lev] = 0;
                    } else {
                        __atomic_fetch_add(&eg[lev][idx], 1, __ATOMIC_RELAXED);
                        if (++r2[lev] == ks[lev]) r2[lev] = 0;
                    }
                }
                if (is_odd) x = 3 * x + 1;
                else        x >>= 1;
                total_steps++;
            }
        }

        /* Merge private grids */
        #pragma omp critical
        {
            for (int lev = 0; lev < split; lev++) {
                int64_t sz = (int64_t)ks[lev] * ks[lev];
                for (int64_t c = 0; c < sz; c++) {
                    eg[lev][c] += pe[lev][c];
                    og[lev][c] += po[lev][c];
                }
            }
        }
    }

    printf("  Unsieved: %ld total steps\n", (long)total_steps);

    for (int t = 0; t < nthreads; t++)
        for (int lev = 0; lev < split; lev++) {
            free(thr_pe[t * split + lev]);
            free(thr_po[t * split + lev]);
        }
    free(thr_pe); free(thr_po);
}

/* ── Sieved pass ───────────────────────────────────────────────────── */

static void run_sieved(int64_t N) {
    int split = 0;
    int ks[MAX_LEVELS];
    for (int i = 0; i < num_levels; i++) {
        ks[i] = levels_siev[i].k;
        if (ks[i] <= PRIVATE_K_THRESHOLD) split = i + 1;
    }

    int nthreads = omp_get_max_threads();

    int64_t **thr_pe = calloc(nthreads * split, sizeof(int64_t *));
    int64_t **thr_po = calloc(nthreads * split, sizeof(int64_t *));
    for (int t = 0; t < nthreads; t++)
        for (int lev = 0; lev < split; lev++) {
            int64_t sz = (int64_t)ks[lev] * ks[lev];
            thr_pe[t * split + lev] = calloc(sz, sizeof(int64_t));
            thr_po[t * split + lev] = calloc(sz, sizeof(int64_t));
        }

    int64_t *eg[MAX_LEVELS], *og[MAX_LEVELS];
    for (int i = 0; i < num_levels; i++) {
        eg[i] = levels_siev[i].even_grid;
        og[i] = levels_siev[i].odd_grid;
    }

    int64_t total_steps = 0, sieve_skipped = 0;

    #pragma omp parallel reduction(+:total_steps, sieve_skipped)
    {
        int tid = omp_get_thread_num();
        int64_t *pe[MAX_LEVELS], *po[MAX_LEVELS];
        for (int lev = 0; lev < split; lev++) {
            pe[lev] = thr_pe[tid * split + lev];
            po[lev] = thr_po[tid * split + lev];
        }

        #pragma omp for schedule(dynamic, 256)
        for (int64_t n = 2; n <= N; n++) {
            int r2[MAX_LEVELS], r3[MAX_LEVELS];
            for (int lev = 0; lev < num_levels; lev++) {
                r2[lev] = 0; r3[lev] = 0;
            }

            uint64_t x = (uint64_t)n;

            /* ── SIEVE FAST-FORWARD ──
             * For odd n >= 2^SIEVE_K: replay the known parity sequence
             * to update grid cells, then jump to the post-sieve value.
             */
            if ((x & 1) && x >= SIEVE_MOD) {
                uint64_t r = x & SIEVE_MASK;
                uint64_t sidx = r / 2;
                uint16_t det = total_det_steps[sidx];
                uint64_t pbm = parity_bitmaps[sidx];
                uint16_t a = sieve_data[sidx].class_odd;
                uint64_t A = sieve_data[sidx].A_num;
                uint64_t B = sieve_data[sidx].B_num;

                /* Compute post-sieve value */
                __uint128_t prod = (__uint128_t)A * x + B;
                uint64_t x_new = (uint64_t)(prod >> SIEVE_K);

                if (x_new > 0 && x_new < x) {
                    /* Batch replay: process per-level (better cache locality).
                     * Each level's grid is accessed contiguously rather than
                     * interleaved with other levels' grids. */
                    for (int lev = 0; lev < split; lev++) {
                        int kl = ks[lev];
                        int r2l = 0, r3l = 0;
                        int64_t *pel = pe[lev], *pol = po[lev];
                        for (int s = 0; s < det; s++) {
                            int idx = r2l * kl + r3l;
                            if ((pbm >> s) & 1) {
                                pol[idx]++;
                                if (++r3l == kl) r3l = 0;
                            } else {
                                pel[idx]++;
                                if (++r2l == kl) r2l = 0;
                            }
                        }
                        r2[lev] = r2l;
                        r3[lev] = r3l;
                    }
                    for (int lev = split; lev < num_levels; lev++) {
                        int kl = ks[lev];
                        int r2l = 0, r3l = 0;
                        int64_t *egl = eg[lev], *ogl = og[lev];
                        for (int s = 0; s < det; s++) {
                            int idx = r2l * kl + r3l;
                            if ((pbm >> s) & 1) {
                                __atomic_fetch_add(&ogl[idx], 1,
                                                   __ATOMIC_RELAXED);
                                if (++r3l == kl) r3l = 0;
                            } else {
                                __atomic_fetch_add(&egl[idx], 1,
                                                   __ATOMIC_RELAXED);
                                if (++r2l == kl) r2l = 0;
                            }
                        }
                        r2[lev] = r2l;
                        r3[lev] = r3l;
                    }

                    total_steps += det;
                    sieve_skipped += det;
                    x = x_new;
                }
            }

            /* ── Normal Collatz iteration for remaining steps ── */
            while (x != 1) {
                int is_odd = x & 1;
                for (int lev = 0; lev < split; lev++) {
                    int idx = r2[lev] * ks[lev] + r3[lev];
                    if (is_odd) {
                        po[lev][idx]++;
                        if (++r3[lev] == ks[lev]) r3[lev] = 0;
                    } else {
                        pe[lev][idx]++;
                        if (++r2[lev] == ks[lev]) r2[lev] = 0;
                    }
                }
                for (int lev = split; lev < num_levels; lev++) {
                    int idx = r2[lev] * ks[lev] + r3[lev];
                    if (is_odd) {
                        __atomic_fetch_add(&og[lev][idx], 1, __ATOMIC_RELAXED);
                        if (++r3[lev] == ks[lev]) r3[lev] = 0;
                    } else {
                        __atomic_fetch_add(&eg[lev][idx], 1, __ATOMIC_RELAXED);
                        if (++r2[lev] == ks[lev]) r2[lev] = 0;
                    }
                }
                if (is_odd) x = 3 * x + 1;
                else        x >>= 1;
                total_steps++;
            }
        }

        /* Merge private grids */
        #pragma omp critical
        {
            for (int lev = 0; lev < split; lev++) {
                int64_t sz = (int64_t)ks[lev] * ks[lev];
                for (int64_t c = 0; c < sz; c++) {
                    eg[lev][c] += pe[lev][c];
                    og[lev][c] += po[lev][c];
                }
            }
        }
    }

    printf("  Sieved:   %ld total steps (%ld sieve-replayed, %.1f%%)\n",
           (long)total_steps, (long)sieve_skipped,
           100.0 * sieve_skipped / total_steps);

    for (int t = 0; t < nthreads; t++)
        for (int lev = 0; lev < split; lev++) {
            free(thr_pe[t * split + lev]);
            free(thr_po[t * split + lev]);
        }
    free(thr_pe); free(thr_po);
}

/* ── Grid comparison ───────────────────────────────────────────────── */

static int compare_grids(void) {
    int64_t total_cells = 0, mismatches = 0;
    for (int lev = 0; lev < num_levels; lev++) {
        int k = levels_ref[lev].k;
        int64_t sz = (int64_t)k * k;
        total_cells += 2 * sz;
        for (int64_t c = 0; c < sz; c++) {
            if (levels_ref[lev].even_grid[c] != levels_siev[lev].even_grid[c]) {
                if (mismatches < 10)
                    printf("  MISMATCH k=%d even_grid[%ld]: ref=%ld siev=%ld\n",
                           k, (long)c,
                           (long)levels_ref[lev].even_grid[c],
                           (long)levels_siev[lev].even_grid[c]);
                mismatches++;
            }
            if (levels_ref[lev].odd_grid[c] != levels_siev[lev].odd_grid[c]) {
                if (mismatches < 10)
                    printf("  MISMATCH k=%d odd_grid[%ld]: ref=%ld siev=%ld\n",
                           k, (long)c,
                           (long)levels_ref[lev].odd_grid[c],
                           (long)levels_siev[lev].odd_grid[c]);
                mismatches++;
            }
        }
    }
    printf("\n  Grid comparison: %ld cells checked, %ld mismatches\n",
           (long)total_cells, (long)mismatches);
    return (mismatches == 0);
}

/* ── Main ──────────────────────────────────────────────────────────── */

int main(int argc, char **argv) {
    int64_t N = 10000000;
    int sk = 16;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-k") == 0 && i + 1 < argc)
            sk = atoi(argv[++i]);
        else if (argv[i][0] != '-')
            N = atoll(argv[i]);
    }

    printf("=== Branch Locus Sieved Proof-of-Concept ===\n");
    printf("N = %ld, sieve k = %d, threads = %d\n\n", (long)N, sk,
           omp_get_max_threads());

    /* Load sieve */
    printf("Loading sieve...\n");
    if (!load_sieve(sk)) {
        fprintf(stderr, "Failed to load sieve. Run: ./gen_sieve -k %d\n", sk);
        return 1;
    }
    printf("  Loaded sieve_k%d_precomp.bin (%lu odd residues)\n",
           sk, SIEVE_MOD / 2);

    /* Precompute parity bitmaps */
    printf("Precomputing parity bitmaps...\n");
    double t0 = omp_get_wtime();
    precompute_parity_bitmaps();
    printf("  Done in %.3f s\n\n", omp_get_wtime() - t0);

    /* Initialize two copies of levels */
    printf("Initialising levels...\n");
    init_levels(levels_ref);
    int save_nl = num_levels;
    num_levels = 0;
    init_levels(levels_siev);
    num_levels = save_nl;

    int64_t total_grid_mem = 0;
    for (int i = 0; i < num_levels; i++)
        total_grid_mem += 2 * (int64_t)levels_ref[i].k * levels_ref[i].k * 8;
    printf("  %d levels (k = %d .. %d), %.1f MB per grid set\n",
           num_levels, levels_ref[0].k, levels_ref[num_levels - 1].k,
           total_grid_mem / (1024.0 * 1024));

    /* Run unsieved */
    printf("\n── Pass 1: Unsieved ──\n");
    t0 = omp_get_wtime();
    run_unsieved(N);
    double t_unsieved = omp_get_wtime() - t0;
    printf("  Time: %.3f s\n", t_unsieved);

    /* Run sieved */
    printf("\n── Pass 2: Sieved (k=%d) ──\n", sk);
    t0 = omp_get_wtime();
    run_sieved(N);
    double t_sieved = omp_get_wtime() - t0;
    printf("  Time: %.3f s\n", t_sieved);

    /* Compare */
    printf("\n── Verification ──\n");
    int ok = compare_grids();

    printf("\n── Results ──\n");
    printf("  Unsieved: %.3f s\n", t_unsieved);
    printf("  Sieved:   %.3f s\n", t_sieved);
    printf("  Speedup:  %.2fx (%.1f%% faster)\n",
           t_unsieved / t_sieved,
           100.0 * (1.0 - t_sieved / t_unsieved));
    printf("  Grids:    %s\n", ok ? "EXACT MATCH" : "*** MISMATCH ***");

    if (!ok) {
        printf("\n*** SIEVE INTEGRATION HAS BUGS — investigate mismatches ***\n");
        return 1;
    }

    /* Cleanup */
    for (int i = 0; i < num_levels; i++) {
        free(levels_ref[i].even_grid); free(levels_ref[i].odd_grid);
        free(levels_siev[i].even_grid); free(levels_siev[i].odd_grid);
    }
    free(sieve_data);
    free(parity_bitmaps);
    free(total_det_steps);

    return 0;
}
