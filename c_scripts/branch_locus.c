/*
 * branch_locus.c
 *
 * Branch Locus on Finite Tori for Collatz Winding Numbers
 *
 * Tracks per-step dynamics: at each Collatz step, the running residues
 * (nu2(t) mod k, nu3(t) mod k) identify a cell on (Z/kZ)^2, and the
 * parity of x(t) determines which branch was taken (even -> divide by 2,
 * odd -> 3x+1).  A cell is a "branch cell" if both parities are observed.
 *
 * Extended with per-cell parity transition tracking for target levels
 * (k in {81, 108, 144, 729, 19683}) and shadow offset computation
 * for Diophantine levels k=729 and k=19683.
 *
 * Mathematical motivation (Remark 3.7, collatz_winding_notes.tex):
 * "The branch locus introduces singularities in the stable and unstable
 * foliations... the foliations are measured foliations with finitely many
 * singularities (the prong-type singularities at parity transitions)."
 *
 * Foliation slopes (comparison table, lines 275-283):
 *   Unstable: slope log_2(3)  ~ 1.585  in (nu2, nu3) coordinates
 *   Stable:   slope -1/log_2(3) ~ -0.631
 *
 * Usage: ./branch_locus [N]   (default N = 10000000)
 *
 * Compile: gcc -O3 -march=native -o branch_locus branch_locus.c -lm
 */

#define _DEFAULT_SOURCE
#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>
#include <unistd.h>
#include <omp.h>

/* ── Constants ──────────────────────────────────────────────────────── */

#define MAX_EXP      4
#define BASE_LEVELS  ((MAX_EXP + 1) * (MAX_EXP + 1))   /* 25 */
#define MAX_LEVELS   32     /* room for extra Diophantine levels */
#define LOG2_3       1.58496250072115618
#define INV_LOG2_3   (1.0 / LOG2_3)   /* ~ 0.63093 */

/* Levels with k <= this threshold use per-thread private grids (no atomics).
 * Levels above use shared grids with atomic updates.
 * Threshold=162: per-thread ~2.3 MB (fits in L2 cache ~3.3 MB/core).
 * Atomic levels k>=216 benefit from shared L3 cache (36 MB).
 * Transition targets k=81,108,144 are private (no atomics). */
#define PRIVATE_K_THRESHOLD 162

/* Diophantine best-approximant levels: 3^k where p/3^k is a record
 * approximation to log_3(2).  See docs/diophantine_terms.md.
 *   k=6:  460/729     err 7.2e-5   (18x better than 17/27)
 *   k=9:  12419/19683 err 2.1e-5   (3.4x better than 460/729)
 */
static const struct { int b; long k; long numer; } dioph_levels[] = {
    { 6,   729,    460   },
    { 9, 19683,  12419   },
};
#define N_DIOPH  (sizeof(dioph_levels)/sizeof(dioph_levels[0]))

/* Target levels for parity transition tracking.
 * k=19683 excluded: SFT "11" already verified at k=729 (2.27T steps, 0 oo).
 * Including k=19683 here adds ~9.3 GB + ~2 days for N=10^11. */
static const int trans_targets[] = {81, 108, 144, 729};
#define N_TRANS_TARGETS  (sizeof(trans_targets)/sizeof(trans_targets[0]))

/* ── Structures ─────────────────────────────────────────────────────── */

typedef struct {
    int k, a, b;
    int64_t *even_grid;    /* k x k: even-step visit counts */
    int64_t *odd_grid;     /* k x k: odd-step visit counts  */
    int64_t *trans_ee;     /* k x k: even->even transitions  */
    int64_t *trans_eo;     /* k x k: even->odd transitions   */
    int64_t *trans_oe;     /* k x k: odd->even transitions   */
    int      track_trans;  /* 1 if this level tracks transitions */
} level_t;

typedef struct {
    int k, a, b;
    int64_t total_visits, branch_cells, pure_even, pure_odd, empty_cells;
    double  branch_fraction, mean_p_odd, std_p_odd;
    double  mean_H_branch, mean_slope_dev, std_slope_dev;
    int64_t singular_cells;
    int64_t total_ee, total_eo, total_oe, total_oo;  /* transition aggregates */
} summary_t;

/* ── Global state ──────────────────────────────────────────────────── */

static int64_t  N;
static int      num_levels;
static level_t  levels[MAX_LEVELS];
static summary_t summaries[MAX_LEVELS];

static int64_t  total_trajs, total_steps;
static int64_t  total_even_steps, total_odd_steps;
static double   global_p_odd, mean_traj_len;

/* ── Checkpoint system ────────────────────────────────────────────── */

#define MAX_CHECKPOINTS 200

static int64_t  ckpt_Ns[MAX_CHECKPOINTS];
static int      n_ckpts;
static int      next_ckpt;
static FILE    *ckpt_fp;

/* ── Binary state checkpoint (resume support) ─────────────────────── */

#define STATE_MAGIC    0x4B4C5242   /* "BRLK" */
#define STATE_VERSION  1
#define STATE_FILE     "branch_state.bin"
#define STATE_TMP      "branch_state.bin.tmp"

static int resume_mode = 0;

/* ── Timer utility ─────────────────────────────────────────────────── */

static struct timespec _ts;
static void tic(void) { clock_gettime(CLOCK_MONOTONIC, &_ts); }
static double toc(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (now.tv_sec - _ts.tv_sec) + 1e-9 * (now.tv_nsec - _ts.tv_nsec);
}

static void fmt_time(double s, char *buf, size_t len)
{
    if (s < 60)
        snprintf(buf, len, "%5.1fs", s);
    else if (s < 3600)
        snprintf(buf, len, "%dm%02ds", (int)(s / 60), (int)s % 60);
    else
        snprintf(buf, len, "%dh%02dm%02ds",
                 (int)(s / 3600), ((int)s % 3600) / 60, (int)s % 60);
}

/* ── Checkpoint: periodic snapshot of cell counts ──────────────────── */

static void checkpoint_init(int64_t max_N)
{
    n_ckpts = 0;

    /* Generate geometrically spaced checkpoints: 10 per decade */
    double log_start = (max_N >= 1000000) ? 6.0 : log10(3.0);
    double log_end = log10((double)max_N);

    for (double logn = log_start; logn <= log_end + 0.001; logn += 0.1) {
        int64_t n = (int64_t)(pow(10.0, logn) + 0.5);
        if (n < 2) n = 2;
        if (n > max_N) n = max_N;
        if (n_ckpts < MAX_CHECKPOINTS) {
            if (n_ckpts == 0 || n > ckpt_Ns[n_ckpts - 1])
                ckpt_Ns[n_ckpts++] = n;
        }
    }
    /* Ensure max_N is included */
    if (n_ckpts == 0 || ckpt_Ns[n_ckpts - 1] != max_N) {
        if (n_ckpts < MAX_CHECKPOINTS)
            ckpt_Ns[n_ckpts++] = max_N;
    }

    if (resume_mode) {
        /* In resume mode, next_ckpt was set by load_binary_state().
         * Open CSV in append mode to preserve existing checkpoint data. */
        ckpt_fp = fopen("branch_checkpoints.csv", "a");
        if (!ckpt_fp) {
            perror("branch_checkpoints.csv (append)");
            return;
        }
        printf("  Checkpoints: %d total, resuming from index %d\n",
               n_ckpts, next_ckpt);
    } else {
        next_ckpt = 0;

        ckpt_fp = fopen("branch_checkpoints.csv", "w");
        if (!ckpt_fp) {
            perror("branch_checkpoints.csv");
            return;
        }
        fprintf(ckpt_fp,
                "checkpoint_N,k,a,b,branch,pure_even,pure_odd,empty\n");
        fflush(ckpt_fp);

        printf("  Checkpoints: %d snapshots from N=%ld to N=%ld\n",
               n_ckpts, (long)ckpt_Ns[0], (long)ckpt_Ns[n_ckpts - 1]);
    }
}

static void checkpoint_snapshot(int64_t current_n)
{
    if (!ckpt_fp) return;

    for (int lev = 0; lev < num_levels; lev++) {
        int k = levels[lev].k;
        int64_t ncells = (int64_t)k * k;

        int64_t branch = 0, pe = 0, po = 0, empty = 0;

        for (int64_t c = 0; c < ncells; c++) {
            int64_t ne = levels[lev].even_grid[c];
            int64_t no = levels[lev].odd_grid[c];

            if (ne == 0 && no == 0)    empty++;
            else if (ne > 0 && no > 0) branch++;
            else if (no == 0)          pe++;
            else                       po++;
        }

        fprintf(ckpt_fp, "%ld,%d,%d,%d,%ld,%ld,%ld,%ld\n",
                (long)current_n, k, levels[lev].a, levels[lev].b,
                (long)branch, (long)pe, (long)po, (long)empty);
    }

    fflush(ckpt_fp);
}

/* ── Binary state save/load for crash recovery ─────────────────────── */

static void save_binary_state(int64_t current_n)
{
    struct timespec t0;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    FILE *f = fopen(STATE_TMP, "wb");
    if (!f) { perror("save_binary_state: open"); return; }

    uint32_t magic = STATE_MAGIC, version = STATE_VERSION;
    fwrite(&magic, 4, 1, f);
    fwrite(&version, 4, 1, f);
    fwrite(&N, 8, 1, f);
    fwrite(&current_n, 8, 1, f);

    int32_t nc = next_ckpt, nl = num_levels;
    fwrite(&nc, 4, 1, f);
    fwrite(&nl, 4, 1, f);
    fwrite(&total_trajs, 8, 1, f);
    fwrite(&total_even_steps, 8, 1, f);
    fwrite(&total_odd_steps, 8, 1, f);

    for (int lev = 0; lev < num_levels; lev++) {
        int32_t k  = levels[lev].k;
        int32_t a  = levels[lev].a;
        int32_t b  = levels[lev].b;
        int32_t tt = levels[lev].track_trans;
        fwrite(&k, 4, 1, f);
        fwrite(&a, 4, 1, f);
        fwrite(&b, 4, 1, f);
        fwrite(&tt, 4, 1, f);

        int64_t sz = (int64_t)k * k;
        fwrite(levels[lev].even_grid, 8, sz, f);
        fwrite(levels[lev].odd_grid,  8, sz, f);
        if (tt) {
            fwrite(levels[lev].trans_ee,  8, sz, f);
            fwrite(levels[lev].trans_eo,  8, sz, f);
            fwrite(levels[lev].trans_oe,  8, sz, f);
        }
    }

    fflush(f);
    fsync(fileno(f));
    fclose(f);

    /* Atomic replace */
    if (rename(STATE_TMP, STATE_FILE) != 0)
        perror("save_binary_state: rename");

    struct timespec t1;
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double dt = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
    printf("\n  [checkpoint] saved binary state at n=%ld (%.1fs)\n",
           (long)current_n, dt);
}

static int load_binary_state(int64_t *resume_n)
{
    FILE *f = fopen(STATE_FILE, "rb");
    if (!f) {
        printf("  No state file found (%s)\n", STATE_FILE);
        return 0;
    }

    /* Helper: abort on short read */
    #define RD(ptr, sz, n, fp) do { \
        if (fread((ptr), (sz), (n), (fp)) != (size_t)(n)) { \
            fprintf(stderr, "  State file: unexpected EOF\n"); \
            fclose(fp); return 0; \
        } \
    } while (0)

    uint32_t magic, version;
    RD(&magic, 4, 1, f);
    RD(&version, 4, 1, f);
    if (magic != STATE_MAGIC) {
        fprintf(stderr, "  State file: bad magic (0x%08X)\n", magic);
        fclose(f); return 0;
    }
    if (version != STATE_VERSION) {
        fprintf(stderr, "  State file: unknown version %u\n", version);
        fclose(f); return 0;
    }

    int64_t saved_N;
    RD(&saved_N, 8, 1, f);
    RD(resume_n, 8, 1, f);

    int32_t nc, nl;
    RD(&nc, 4, 1, f);
    RD(&nl, 4, 1, f);
    RD(&total_trajs, 8, 1, f);
    RD(&total_even_steps, 8, 1, f);
    RD(&total_odd_steps, 8, 1, f);

    if (saved_N != N) {
        fprintf(stderr, "  State file: N mismatch (state=%ld, expected=%ld)\n",
                (long)saved_N, (long)N);
        fclose(f); return 0;
    }
    if (nl != num_levels) {
        fprintf(stderr, "  State file: level count mismatch (%d vs %d)\n",
                nl, num_levels);
        fclose(f); return 0;
    }

    for (int lev = 0; lev < num_levels; lev++) {
        int32_t k, a, b, tt;
        RD(&k, 4, 1, f);
        RD(&a, 4, 1, f);
        RD(&b, 4, 1, f);
        RD(&tt, 4, 1, f);

        if (k != levels[lev].k || a != levels[lev].a || b != levels[lev].b) {
            fprintf(stderr, "  State file: level mismatch at index %d "
                    "(k=%d vs %d)\n", lev, k, levels[lev].k);
            fclose(f); return 0;
        }

        int64_t sz = (int64_t)k * k;
        RD(levels[lev].even_grid, 8, sz, f);
        RD(levels[lev].odd_grid,  8, sz, f);
        if (tt) {
            RD(levels[lev].trans_ee, 8, sz, f);
            RD(levels[lev].trans_eo, 8, sz, f);
            RD(levels[lev].trans_oe, 8, sz, f);
        }
    }

    #undef RD

    next_ckpt = nc;
    fclose(f);

    total_steps = total_even_steps + total_odd_steps;

    printf("  Restored state from n=%ld (%ld trajectories, %ld steps)\n",
           (long)*resume_n, (long)total_trajs, (long)total_steps);

    return 1;
}

/* ── Helper: check if k is a transition-tracking target ────────────── */

static int is_trans_target(int k)
{
    for (int i = 0; i < (int)N_TRANS_TARGETS; i++)
        if (trans_targets[i] == k) return 1;
    return 0;
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
            levels[num_levels].even_grid = NULL;
            levels[num_levels].odd_grid  = NULL;
            levels[num_levels].trans_ee  = NULL;
            levels[num_levels].trans_eo  = NULL;
            levels[num_levels].trans_oe  = NULL;
            levels[num_levels].track_trans = 0;
            num_levels++;
        }
    }

    /* Add Diophantine best-approximant levels (pure 3-adic) */
    for (int d = 0; d < (int)N_DIOPH; d++) {
        /* Check not already present */
        int dup = 0;
        for (int i = 0; i < num_levels; i++)
            if (levels[i].k == dioph_levels[d].k) { dup = 1; break; }
        if (dup) continue;
        if (num_levels >= MAX_LEVELS) {
            fprintf(stderr, "Too many levels (max %d)\n", MAX_LEVELS);
            exit(1);
        }
        levels[num_levels].k = (int)dioph_levels[d].k;
        levels[num_levels].a = 0;
        levels[num_levels].b = dioph_levels[d].b;
        levels[num_levels].even_grid = NULL;
        levels[num_levels].odd_grid  = NULL;
        levels[num_levels].trans_ee  = NULL;
        levels[num_levels].trans_eo  = NULL;
        levels[num_levels].trans_oe  = NULL;
        levels[num_levels].track_trans = 0;
        num_levels++;
    }

    /* Sort by k (bubble sort, small array) */
    for (int i = 0; i < num_levels - 1; i++)
        for (int j = i + 1; j < num_levels; j++)
            if (levels[i].k > levels[j].k) {
                level_t tmp = levels[i];
                levels[i] = levels[j];
                levels[j] = tmp;
            }

    /* Allocate grids and transition grids */
    int64_t total_cells = 0;
    int64_t trans_cells = 0;
    for (int i = 0; i < num_levels; i++) {
        int k = levels[i].k;
        int64_t sz = (int64_t)k * k;
        levels[i].even_grid = (int64_t *)calloc(sz, sizeof(int64_t));
        levels[i].odd_grid  = (int64_t *)calloc(sz, sizeof(int64_t));
        if (!levels[i].even_grid || !levels[i].odd_grid) {
            fprintf(stderr, "Failed to allocate grids for k=%d (%ld cells)\n",
                    k, (long)sz);
            exit(1);
        }
        total_cells += 2 * sz;

        /* Allocate transition grids for target levels */
        if (is_trans_target(k)) {
            levels[i].track_trans = 1;
            levels[i].trans_ee = (int64_t *)calloc(sz, sizeof(int64_t));
            levels[i].trans_eo = (int64_t *)calloc(sz, sizeof(int64_t));
            levels[i].trans_oe = (int64_t *)calloc(sz, sizeof(int64_t));
            if (!levels[i].trans_ee || !levels[i].trans_eo ||
                !levels[i].trans_oe) {
                fprintf(stderr,
                        "Failed to allocate transition grids for k=%d\n", k);
                exit(1);
            }
            trans_cells += 3 * sz;
        }
    }

    printf("  %d levels, total grid cells: %ld (%.1f MB)\n",
           num_levels, (long)(total_cells + trans_cells),
           (total_cells + trans_cells) * 8.0 / (1024 * 1024));

    printf("\n  %-6s  %-8s  %-10s  %-6s\n", "k", "(a,b)", "cells", "trans");
    printf("  ──────────────────────────────────────\n");
    for (int i = 0; i < num_levels; i++)
        printf("  %-6d  (2^%d*3^%d)  %-10ld  %s\n",
               levels[i].k, levels[i].a, levels[i].b,
               (long)levels[i].k * levels[i].k,
               levels[i].track_trans ? "YES" : "");
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 2: Compute branch data (OpenMP parallel, per-step accumulation)
 *
 * For each trajectory n, at each Collatz step:
 *   - the running residues (r2 mod k, r3 mod k) identify a torus cell
 *   - the parity of x determines which grid to increment
 *   - the appropriate running residue advances by 1 (mod k)
 *   - for target levels, track parity transitions (prev -> current)
 *
 * Parallelism strategy:
 *   - Levels with k <= PRIVATE_K_THRESHOLD (72): per-thread private grids,
 *     merged into global grids at each checkpoint boundary.  No atomics.
 *   - Levels with k > PRIVATE_K_THRESHOLD (81+): shared grids with relaxed
 *     atomic increments.  Contention is negligible (6561+ cells, 24 threads).
 *   - Work is chunked between checkpoints; implicit barrier at each boundary
 *     ensures global grids are consistent before snapshot + binary save.
 * ═══════════════════════════════════════════════════════════════════════ */

static void compute_branch_data(int64_t start_n)
{
    printf("\nComputing per-step branch data for n in [%ld, %ld]...\n",
           (long)start_n, (long)N);
    tic();

    if (start_n <= 2) {
        total_trajs = 0;
        total_steps = 0;
        total_even_steps = 0;
        total_odd_steps  = 0;
        start_n = 2;
    }
    /* else: counters already loaded from binary state */

    /* Determine split: levels[0..split-1] are private, [split..num_levels-1] atomic */
    int split = 0;
    while (split < num_levels && levels[split].k <= PRIVATE_K_THRESHOLD)
        split++;

    /* Cache grid pointers and k values for inner-loop performance */
    int64_t *eg[MAX_LEVELS], *og[MAX_LEVELS];
    int64_t *te[MAX_LEVELS], *teo_arr[MAX_LEVELS], *toe_arr[MAX_LEVELS];
    int      ks[MAX_LEVELS];
    int      tt[MAX_LEVELS];
    for (int lev = 0; lev < num_levels; lev++) {
        eg[lev]      = levels[lev].even_grid;
        og[lev]      = levels[lev].odd_grid;
        te[lev]      = levels[lev].trans_ee;
        teo_arr[lev] = levels[lev].trans_eo;
        toe_arr[lev] = levels[lev].trans_oe;
        ks[lev]      = levels[lev].k;
        tt[lev]      = levels[lev].track_trans;
    }

    int nthreads = omp_get_max_threads();
    printf("  OpenMP: %d threads, %d private levels (k<=%d), "
           "%d atomic levels (k>=%d)\n",
           nthreads, split, PRIVATE_K_THRESHOLD,
           num_levels - split,
           split < num_levels ? ks[split] : 0);

    /* Compute total private grid cells per thread (for reporting) */
    int64_t priv_cells = 0;
    for (int lev = 0; lev < split; lev++)
        priv_cells += (int64_t)ks[lev] * ks[lev];

    /* Count transition cells in private levels */
    int64_t priv_trans_cells = 0;
    for (int lev = 0; lev < split; lev++)
        if (tt[lev])
            priv_trans_cells += (int64_t)ks[lev] * ks[lev];

    int64_t per_thread_bytes = (2 * priv_cells + 3 * priv_trans_cells) * 8;
    printf("  Per-thread private grids: %.1f MB (%d threads = %.1f MB total)\n",
           per_thread_bytes / (1024.0 * 1024),
           nthreads,
           (double)per_thread_bytes * nthreads / (1024.0 * 1024));

    /* ── Pre-allocate per-thread private grids ─────────────────────── */

    int64_t **thr_pe, **thr_po;           /* [thread][level] */
    int64_t **thr_te, **thr_teo, **thr_toe;
    thr_pe  = (int64_t **)calloc(nthreads * split, sizeof(int64_t *));
    thr_po  = (int64_t **)calloc(nthreads * split, sizeof(int64_t *));
    thr_te  = (int64_t **)calloc(nthreads * split, sizeof(int64_t *));
    thr_teo = (int64_t **)calloc(nthreads * split, sizeof(int64_t *));
    thr_toe = (int64_t **)calloc(nthreads * split, sizeof(int64_t *));

    for (int t = 0; t < nthreads; t++) {
        for (int lev = 0; lev < split; lev++) {
            int64_t sz = (int64_t)ks[lev] * ks[lev];
            thr_pe[t * split + lev] = (int64_t *)calloc(sz, sizeof(int64_t));
            thr_po[t * split + lev] = (int64_t *)calloc(sz, sizeof(int64_t));
            if (tt[lev]) {
                thr_te [t * split + lev] = (int64_t *)calloc(sz, sizeof(int64_t));
                thr_teo[t * split + lev] = (int64_t *)calloc(sz, sizeof(int64_t));
                thr_toe[t * split + lev] = (int64_t *)calloc(sz, sizeof(int64_t));
            }
        }
    }
    printf("  Private grids allocated.\n");

    /* ── Process in checkpoint-delimited chunks ────────────────────── */
    int64_t chunk_start = start_n;
    int64_t overall_start = start_n;

    for (int ci = 0; ci < n_ckpts; ci++) {
        int64_t chunk_end = ckpt_Ns[ci];
        if (chunk_end < chunk_start) continue;

        int64_t chunk_size = chunk_end - chunk_start + 1;
        if (chunk_size <= 0) { chunk_start = chunk_end + 1; continue; }

        #pragma omp parallel
        {
            int tid = omp_get_thread_num();

            /* Per-thread grid pointers for this thread */
            int64_t *pe[MAX_LEVELS], *po[MAX_LEVELS];
            int64_t *pte[MAX_LEVELS], *pteo[MAX_LEVELS], *ptoe[MAX_LEVELS];
            for (int lev = 0; lev < split; lev++) {
                pe[lev]   = thr_pe [tid * split + lev];
                po[lev]   = thr_po [tid * split + lev];
                pte[lev]  = thr_te [tid * split + lev];
                pteo[lev] = thr_teo[tid * split + lev];
                ptoe[lev] = thr_toe[tid * split + lev];
            }

            int64_t my_trajs = 0, my_even = 0, my_odd = 0;

            #pragma omp for schedule(dynamic, 256)
            for (int64_t n = chunk_start; n <= chunk_end; n++) {
                int r2[MAX_LEVELS], r3[MAX_LEVELS];
                int pp[MAX_LEVELS];
                for (int lev = 0; lev < num_levels; lev++) {
                    r2[lev] = 0; r3[lev] = 0; pp[lev] = -1;
                }

                uint64_t x = (uint64_t)n;

                while (x != 1) {
                    int is_odd = x & 1;

                    /* Private levels: thread-local, no atomics */
                    for (int lev = 0; lev < split; lev++) {
                        int k = ks[lev];
                        int idx = r2[lev] * k + r3[lev];
                        if (is_odd) {
                            po[lev][idx]++;
                            if (++r3[lev] == k) r3[lev] = 0;
                        } else {
                            pe[lev][idx]++;
                            if (++r2[lev] == k) r2[lev] = 0;
                        }
                        if (tt[lev] && pp[lev] >= 0) {
                            if (pp[lev] == 0) {
                                if (!is_odd) pte[lev][idx]++;
                                else         pteo[lev][idx]++;
                            } else {
                                ptoe[lev][idx]++;
                            }
                        }
                        pp[lev] = is_odd;
                    }

                    /* Atomic levels: shared grids, relaxed atomics */
                    for (int lev = split; lev < num_levels; lev++) {
                        int k = ks[lev];
                        int idx = r2[lev] * k + r3[lev];
                        if (is_odd) {
                            __atomic_fetch_add(&og[lev][idx], 1,
                                               __ATOMIC_RELAXED);
                            if (++r3[lev] == k) r3[lev] = 0;
                        } else {
                            __atomic_fetch_add(&eg[lev][idx], 1,
                                               __ATOMIC_RELAXED);
                            if (++r2[lev] == k) r2[lev] = 0;
                        }
                        if (tt[lev] && pp[lev] >= 0) {
                            if (pp[lev] == 0) {
                                if (!is_odd)
                                    __atomic_fetch_add(&te[lev][idx], 1,
                                                       __ATOMIC_RELAXED);
                                else
                                    __atomic_fetch_add(&teo_arr[lev][idx], 1,
                                                       __ATOMIC_RELAXED);
                            } else {
                                __atomic_fetch_add(&toe_arr[lev][idx], 1,
                                                   __ATOMIC_RELAXED);
                            }
                        }
                        pp[lev] = is_odd;
                    }

                    if (is_odd) { x = 3 * x + 1; my_odd++; }
                    else        { x >>= 1;        my_even++; }
                }
                my_trajs++;
            }
            /* implicit barrier: all threads finished this chunk */

            /* Merge private grids into global and zero for next chunk */
            #pragma omp critical
            {
                for (int lev = 0; lev < split; lev++) {
                    int64_t sz = (int64_t)ks[lev] * ks[lev];
                    for (int64_t c = 0; c < sz; c++) {
                        eg[lev][c] += pe[lev][c];
                        og[lev][c] += po[lev][c];
                    }
                    memset(pe[lev], 0, sz * sizeof(int64_t));
                    memset(po[lev], 0, sz * sizeof(int64_t));
                    if (tt[lev]) {
                        for (int64_t c = 0; c < sz; c++) {
                            te[lev][c]      += pte[lev][c];
                            teo_arr[lev][c] += pteo[lev][c];
                            toe_arr[lev][c] += ptoe[lev][c];
                        }
                        memset(pte[lev],  0, sz * sizeof(int64_t));
                        memset(pteo[lev], 0, sz * sizeof(int64_t));
                        memset(ptoe[lev], 0, sz * sizeof(int64_t));
                    }
                }
                total_trajs      += my_trajs;
                total_even_steps += my_even;
                total_odd_steps  += my_odd;
            }
        }
        /* end parallel region */

        total_steps = total_even_steps + total_odd_steps;

        /* Checkpoint */
        checkpoint_snapshot(chunk_end);
        next_ckpt = ci + 1;
        save_binary_state(chunk_end);

        /* Progress report at each checkpoint */
        double dt = toc();
        double frac = (double)(chunk_end - overall_start + 1)
                    / (double)(N - overall_start + 1);
        double eta = (frac > 0.001) ? dt * (1.0 - frac) / frac : 0;
        double p_now = (total_steps > 0)
            ? (double)total_odd_steps / total_steps : 0;

        char el[32], et[32];
        fmt_time(dt, el, sizeof(el));
        fmt_time(eta, et, sizeof(et));

        int bw = 30;
        int filled = (int)(frac * bw + 0.5);
        char bar[32];
        for (int i = 0; i < bw; i++)
            bar[i] = (i < filled) ? '#' : '.';
        bar[bw] = '\0';

        printf("  [%s] %5.1f%% | %s elapsed | ETA %s | "
               "%.2fM traj/s | %.0fM step/s | p_odd %.4f\n",
               bar, 100.0 * frac, el, et,
               total_trajs / dt / 1e6,
               total_steps / dt / 1e6,
               p_now);
        fflush(stdout);

        chunk_start = chunk_end + 1;
    }

    /* Free per-thread grids */
    for (int t = 0; t < nthreads; t++)
        for (int lev = 0; lev < split; lev++) {
            free(thr_pe[t * split + lev]);
            free(thr_po[t * split + lev]);
            free(thr_te[t * split + lev]);
            free(thr_teo[t * split + lev]);
            free(thr_toe[t * split + lev]);
        }
    free(thr_pe); free(thr_po);
    free(thr_te); free(thr_teo); free(thr_toe);

    total_steps = total_even_steps + total_odd_steps;
    mean_traj_len = (double)total_steps / total_trajs;
    global_p_odd = (double)total_odd_steps / total_steps;

    /* Final summary */
    double dt = toc();
    char el[32];
    fmt_time(dt, el, sizeof(el));
    printf("  [##############################] 100.0%% | %s elapsed\n", el);
    printf("  %ld trajectories, %ld steps\n",
           (long)total_trajs, (long)total_steps);
    printf("  Mean trajectory length: %.1f steps\n", mean_traj_len);
    printf("  Global p_odd = %.6f  (expected: %.6f = 1/(1+log_2(3)))\n",
           global_p_odd, 1.0 / (1.0 + LOG2_3));
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 3: Compute per-level summaries
 * ═══════════════════════════════════════════════════════════════════════ */

static double binary_entropy(double p)
{
    if (p <= 0.0 || p >= 1.0) return 0.0;
    return -p * log2(p) - (1.0 - p) * log2(1.0 - p);
}

static void compute_summaries(void)
{
    for (int lev = 0; lev < num_levels; lev++) {
        int k = levels[lev].k;
        int64_t ncells = (int64_t)k * k;
        summary_t *s = &summaries[lev];

        s->k = k;
        s->a = levels[lev].a;
        s->b = levels[lev].b;

        /* First pass: classify cells, accumulate statistics */
        s->total_visits = 0;
        s->branch_cells = 0;
        s->pure_even    = 0;
        s->pure_odd     = 0;
        s->empty_cells  = 0;

        double sum_p = 0, sum_p2 = 0;
        double sum_H = 0;
        double sum_sdev = 0, sum_sdev2 = 0;
        int64_t n_branch = 0;

        for (int64_t c = 0; c < ncells; c++) {
            int64_t ne = levels[lev].even_grid[c];
            int64_t no = levels[lev].odd_grid[c];
            int64_t tot = ne + no;
            s->total_visits += tot;

            if (tot == 0) {
                s->empty_cells++;
            } else if (ne > 0 && no > 0) {
                s->branch_cells++;
                double p = (double)no / tot;
                double slope = p / (1.0 - p);
                double dev = fabs(slope - INV_LOG2_3);
                double H = binary_entropy(p);

                sum_p    += p;
                sum_p2   += p * p;
                sum_H    += H;
                sum_sdev += dev;
                sum_sdev2 += dev * dev;
                n_branch++;
            } else if (no == 0) {
                s->pure_even++;
            } else {
                s->pure_odd++;
            }
        }

        s->branch_fraction = (ncells > 0)
            ? (double)s->branch_cells / ncells : 0;

        if (n_branch > 0) {
            s->mean_p_odd = sum_p / n_branch;
            double var_p = sum_p2 / n_branch - s->mean_p_odd * s->mean_p_odd;
            s->std_p_odd = (var_p > 0) ? sqrt(var_p) : 0;

            s->mean_H_branch = sum_H / n_branch;

            s->mean_slope_dev = sum_sdev / n_branch;
            double var_sd = sum_sdev2 / n_branch
                          - s->mean_slope_dev * s->mean_slope_dev;
            s->std_slope_dev = (var_sd > 0) ? sqrt(var_sd) : 0;
        } else {
            s->mean_p_odd = 0;
            s->std_p_odd = 0;
            s->mean_H_branch = 0;
            s->mean_slope_dev = 0;
            s->std_slope_dev = 0;
        }

        /* Second pass: count singular cells (slope_dev > mean + 2*sigma) */
        double threshold = s->mean_slope_dev + 2.0 * s->std_slope_dev;
        s->singular_cells = 0;
        if (n_branch > 0) {
            for (int64_t c = 0; c < ncells; c++) {
                int64_t ne = levels[lev].even_grid[c];
                int64_t no = levels[lev].odd_grid[c];
                if (ne > 0 && no > 0) {
                    double p = (double)no / (ne + no);
                    double slope = p / (1.0 - p);
                    double dev = fabs(slope - INV_LOG2_3);
                    if (dev > threshold)
                        s->singular_cells++;
                }
            }
        }

        /* Transition aggregates for target levels */
        s->total_ee = 0;
        s->total_eo = 0;
        s->total_oe = 0;
        s->total_oo = 0;
        if (levels[lev].track_trans) {
            for (int64_t c = 0; c < ncells; c++) {
                s->total_ee += levels[lev].trans_ee[c];
                s->total_eo += levels[lev].trans_eo[c];
                s->total_oe += levels[lev].trans_oe[c];
            }
            /* total_oo stays 0: odd->odd is impossible (3x+1 is always even) */
        }
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 4: Print report
 * ═══════════════════════════════════════════════════════════════════════ */

static void print_report(void)
{
    printf("\n========================================================================\n");
    printf("BRANCH LOCUS SUMMARY\n");
    printf("========================================================================\n");

    printf("\n  %-6s  %-10s  %10s  %8s  %8s  %8s  %8s  %8s\n",
           "k", "(a,b)", "visits", "branch", "p_even", "p_odd", "empty",
           "br_frac");
    printf("  ────────────────────────────────────────────────────────"
           "────────────────\n");

    for (int lev = 0; lev < num_levels; lev++) {
        summary_t *s = &summaries[lev];
        printf("  %-6d  (2^%d*3^%d)   %10ld  %8ld  %8ld  %8ld  %8ld  %7.4f\n",
               s->k, s->a, s->b,
               (long)s->total_visits, (long)s->branch_cells,
               (long)s->pure_even, (long)s->pure_odd,
               (long)s->empty_cells, s->branch_fraction);
    }

    printf("\n  %-6s  %-10s  %10s  %10s  %10s  %10s  %10s  %8s\n",
           "k", "(a,b)", "mean_p_odd", "std_p_odd", "mean_H_br",
           "mean_Sdev", "std_Sdev", "singular");
    printf("  ────────────────────────────────────────────────────────"
           "──────────────────────\n");

    for (int lev = 0; lev < num_levels; lev++) {
        summary_t *s = &summaries[lev];
        printf("  %-6d  (2^%d*3^%d)   %10.6f  %10.6f  %10.6f  "
               "%10.6f  %10.6f  %8ld\n",
               s->k, s->a, s->b,
               s->mean_p_odd, s->std_p_odd, s->mean_H_branch,
               s->mean_slope_dev, s->std_slope_dev,
               (long)s->singular_cells);
    }

    /* Detailed k=6 cell-by-cell breakdown */
    printf("\n========================================================================\n");
    printf("DETAILED CELL BREAKDOWN: k = 6\n");
    printf("========================================================================\n");

    int lev6 = -1;
    for (int lev = 0; lev < num_levels; lev++)
        if (levels[lev].k == 6) { lev6 = lev; break; }

    if (lev6 >= 0) {
        int k = 6;
        printf("\n  %-4s  %-4s  %12s  %12s  %12s  %8s  %8s  %8s  %-10s\n",
               "r2", "r3", "even", "odd", "total",
               "p_odd", "slope", "entropy", "type");
        printf("  ────────────────────────────────────────────────"
               "──────────────────────────────────\n");

        for (int i = 0; i < k; i++) {
            for (int j = 0; j < k; j++) {
                int idx = i * k + j;
                int64_t ne = levels[lev6].even_grid[idx];
                int64_t no = levels[lev6].odd_grid[idx];
                int64_t tot = ne + no;

                const char *type;
                double p = 0, slope = 0, H = 0;

                if (tot == 0) {
                    type = "empty";
                } else if (ne > 0 && no > 0) {
                    type = "BRANCH";
                    p = (double)no / tot;
                    slope = p / (1.0 - p);
                    H = binary_entropy(p);
                } else if (no == 0) {
                    type = "pure_even";
                    p = 0;
                } else {
                    type = "pure_odd";
                    p = 1.0;
                }

                printf("  %-4d  %-4d  %12ld  %12ld  %12ld  "
                       "%8.5f  %8.5f  %8.5f  %-10s\n",
                       i, j, (long)ne, (long)no, (long)tot,
                       p, slope, H, type);
            }
        }
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 5: Foliation analysis
 *
 * For k in {6, 12, 24, 36, 72}: identify cells near foliation lines
 * and report overlap with the branch set.
 *
 * Perpendicular distance from (r2, r3) to foliation line with slope m:
 *   delta = r3 - m * r2,  wrapped to [-k/2, k/2)
 *   dist  = |delta| / sqrt(1 + m^2)
 * ═══════════════════════════════════════════════════════════════════════ */

static double torus_dist(double r2, double r3, double slope, int k)
{
    double delta = r3 - slope * r2;
    delta = fmod(delta, (double)k);
    if (delta >  k / 2.0) delta -= k;
    if (delta < -k / 2.0) delta += k;
    return fabs(delta) / sqrt(1.0 + slope * slope);
}

static void print_foliation_analysis(void)
{
    printf("\n========================================================================\n");
    printf("FOLIATION ANALYSIS\n");
    printf("========================================================================\n");
    printf("  Unstable slope: log_2(3) = %.6f\n", LOG2_3);
    printf("  Stable slope:  -1/log_2(3) = %.6f\n", -INV_LOG2_3);
    printf("  Distance threshold: 0.5 (perpendicular cell units)\n\n");

    int target_ks[] = {6, 12, 24, 36, 72, 729};
    int n_targets = 6;

    printf("  %-6s  %8s  %8s  %8s  %10s  %10s  %10s  %10s\n",
           "k", "branch", "on_unst", "on_stab",
           "br&unst", "br&stab", "enrich_U", "enrich_S");
    printf("  ────────────────────────────────────────────────"
           "──────────────────────────────────\n");

    for (int t = 0; t < n_targets; t++) {
        int target_k = target_ks[t];
        int lev = -1;
        for (int i = 0; i < num_levels; i++)
            if (levels[i].k == target_k) { lev = i; break; }
        if (lev < 0) continue;

        int k = target_k;
        int64_t ncells = (int64_t)k * k;
        int64_t branch = 0, on_unstable = 0, on_stable = 0;
        int64_t branch_on_unstable = 0, branch_on_stable = 0;

        for (int i = 0; i < k; i++) {
            for (int j = 0; j < k; j++) {
                int idx = i * k + j;
                int64_t ne = levels[lev].even_grid[idx];
                int64_t no = levels[lev].odd_grid[idx];
                int is_branch = (ne > 0 && no > 0);

                double du = torus_dist(i, j, LOG2_3, k);
                double ds = torus_dist(i, j, -INV_LOG2_3, k);
                int on_u = (du < 0.5);
                int on_s = (ds < 0.5);

                if (is_branch) branch++;
                if (on_u) on_unstable++;
                if (on_s) on_stable++;
                if (is_branch && on_u) branch_on_unstable++;
                if (is_branch && on_s) branch_on_stable++;
            }
        }

        double exp_bu = (double)branch * on_unstable / ncells;
        double exp_bs = (double)branch * on_stable   / ncells;
        double enrich_u = (exp_bu > 0) ? branch_on_unstable / exp_bu : 0;
        double enrich_s = (exp_bs > 0) ? branch_on_stable   / exp_bs : 0;

        printf("  %-6d  %8ld  %8ld  %8ld  %10ld  %10ld  %10.3f  %10.3f\n",
               k, (long)branch, (long)on_unstable, (long)on_stable,
               (long)branch_on_unstable, (long)branch_on_stable,
               enrich_u, enrich_s);
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 6: Transition verification ("11" forbidden bigram / SFT check)
 *
 * For each target level:
 *   1. Verify ee + eo + oe == total_steps - total_trajs (no oo gaps)
 *   2. For odd-visited cells, classify successor cell types
 * ═══════════════════════════════════════════════════════════════════════ */

static void verify_transitions(void)
{
    printf("\n========================================================================\n");
    printf("TRANSITION VERIFICATION (SFT \"11\" FORBIDDEN BIGRAM)\n");
    printf("========================================================================\n");

    int all_pass = 1;

    for (int lev = 0; lev < num_levels; lev++) {
        if (!levels[lev].track_trans) continue;

        int k = levels[lev].k;
        summary_t *s = &summaries[lev];

        /* Expected transitions: each trajectory of length L has L-1
         * transitions; sum over all trajectories = total_steps - total_trajs */
        int64_t expected_trans = total_steps - total_trajs;
        int64_t actual_trans = s->total_ee + s->total_eo + s->total_oe;
        int sum_ok = (actual_trans == expected_trans);

        printf("\n  Level k=%d (2^%d*3^%d):\n",
               k, levels[lev].a, levels[lev].b);
        printf("    Transition sums: ee=%ld  eo=%ld  oe=%ld\n",
               (long)s->total_ee, (long)s->total_eo, (long)s->total_oe);
        printf("    Total: %ld  expected: %ld  %s\n",
               (long)actual_trans, (long)expected_trans,
               sum_ok ? "PASS" : "FAIL");
        if (!sum_ok) all_pass = 0;

        /* Implied oo = expected - actual (should be 0) */
        int64_t implied_oo = expected_trans - actual_trans;
        printf("    Implied oo transitions: %ld  %s\n",
               (long)implied_oo, implied_oo == 0 ? "PASS" : "FAIL");
        if (implied_oo != 0) all_pass = 0;

        /* Successor cell analysis for odd-visited cells:
         * After an odd step at (r2, r3), trajectory moves to (r2, (r3+1)%k).
         * The "11" constraint says that next step there is ALWAYS even. */
        int64_t n_odd_cells = 0;
        int64_t succ_branch = 0, succ_pure_even = 0;
        int64_t succ_pure_odd = 0, succ_empty = 0;

        for (int r2 = 0; r2 < k; r2++) {
            for (int r3 = 0; r3 < k; r3++) {
                int idx = r2 * k + r3;
                if (levels[lev].odd_grid[idx] > 0) {
                    n_odd_cells++;
                    /* Successor cell after odd step: r3 advances */
                    int sr3 = (r3 + 1) % k;
                    int sidx = r2 * k + sr3;
                    int64_t se = levels[lev].even_grid[sidx];
                    int64_t so = levels[lev].odd_grid[sidx];

                    if (se > 0 && so > 0)      succ_branch++;
                    else if (se > 0)            succ_pure_even++;
                    else if (so > 0)            succ_pure_odd++;
                    else                        succ_empty++;
                }
            }
        }

        printf("    Odd-visited cells: %ld\n", (long)n_odd_cells);
        printf("    Successor types: branch=%ld  pure_even=%ld  "
               "pure_odd=%ld  empty=%ld\n",
               (long)succ_branch, (long)succ_pure_even,
               (long)succ_pure_odd, (long)succ_empty);

        /* Transition fractions */
        if (actual_trans > 0) {
            printf("    Fractions: ee=%.4f  eo=%.4f  oe=%.4f\n",
                   (double)s->total_ee / actual_trans,
                   (double)s->total_eo / actual_trans,
                   (double)s->total_oe / actual_trans);
        }
    }

    printf("\n  Overall: %s\n", all_pass ? "ALL PASS" : "FAILURES DETECTED");
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 7: Write CSV files
 * ═══════════════════════════════════════════════════════════════════════ */

static void write_csv_files(void)
{
    printf("\n========================================================================\n");
    printf("WRITING CSV FILES\n");
    printf("========================================================================\n");

    /* 1. branch_params.csv */
    {
        FILE *f = fopen("branch_params.csv", "w");
        if (!f) { perror("branch_params.csv"); return; }
        fprintf(f, "key,value\n");
        fprintf(f, "N,%ld\n", (long)N);
        fprintf(f, "num_levels,%d\n", num_levels);
        fprintf(f, "total_trajs,%ld\n", (long)total_trajs);
        fprintf(f, "total_steps,%ld\n", (long)total_steps);
        fprintf(f, "total_even_steps,%ld\n", (long)total_even_steps);
        fprintf(f, "total_odd_steps,%ld\n", (long)total_odd_steps);
        fprintf(f, "mean_traj_len,%.2f\n", mean_traj_len);
        fprintf(f, "global_p_odd,%.9f\n", global_p_odd);
        fclose(f);
        printf("  Saved branch_params.csv\n");
    }

    /* 2. branch_summary.csv (with transition columns) */
    {
        FILE *f = fopen("branch_summary.csv", "w");
        if (!f) { perror("branch_summary.csv"); return; }
        fprintf(f, "k,a,b,total_visits,branch_cells,pure_even,pure_odd,"
                   "empty,branch_fraction,mean_p_odd,std_p_odd,"
                   "mean_H_branch,mean_slope_dev,std_slope_dev,"
                   "singular_cells,total_ee,total_eo,total_oe,total_oo\n");
        for (int lev = 0; lev < num_levels; lev++) {
            summary_t *s = &summaries[lev];
            fprintf(f, "%d,%d,%d,%ld,%ld,%ld,%ld,%ld,"
                       "%.9f,%.9f,%.9f,%.9f,%.9f,%.9f,%ld,"
                       "%ld,%ld,%ld,%ld\n",
                    s->k, s->a, s->b,
                    (long)s->total_visits, (long)s->branch_cells,
                    (long)s->pure_even, (long)s->pure_odd,
                    (long)s->empty_cells, s->branch_fraction,
                    s->mean_p_odd, s->std_p_odd, s->mean_H_branch,
                    s->mean_slope_dev, s->std_slope_dev,
                    (long)s->singular_cells,
                    (long)s->total_ee, (long)s->total_eo,
                    (long)s->total_oe, (long)s->total_oo);
        }
        fclose(f);
        printf("  Saved branch_summary.csv\n");
    }

    /* 3. branch_cells.csv — per-cell for k <= 729 */
    {
        FILE *f = fopen("branch_cells.csv", "w");
        if (!f) { perror("branch_cells.csv"); return; }
        fprintf(f, "k,r2,r3,even_count,odd_count,total,p_odd,"
                   "local_slope,slope_dev,entropy,cell_type\n");
        for (int lev = 0; lev < num_levels; lev++) {
            int k = levels[lev].k;
            if (k > 729) continue;  /* skip huge levels */
            for (int i = 0; i < k; i++) {
                for (int j = 0; j < k; j++) {
                    int idx = i * k + j;
                    int64_t ne = levels[lev].even_grid[idx];
                    int64_t no = levels[lev].odd_grid[idx];
                    int64_t tot = ne + no;

                    const char *type;
                    double p = 0, slope = 0, dev = 0, H = 0;

                    if (tot == 0) {
                        type = "empty";
                    } else if (ne > 0 && no > 0) {
                        type = "branch";
                        p = (double)no / tot;
                        slope = p / (1.0 - p);
                        dev = fabs(slope - INV_LOG2_3);
                        H = binary_entropy(p);
                    } else if (no == 0) {
                        type = "pure_even";
                    } else {
                        type = "pure_odd";
                        p = 1.0;
                    }

                    fprintf(f, "%d,%d,%d,%ld,%ld,%ld,%.9f,"
                               "%.9f,%.9f,%.9f,%s\n",
                            k, i, j, (long)ne, (long)no, (long)tot,
                            p, slope, dev, H, type);
                }
            }
        }
        fclose(f);
        printf("  Saved branch_cells.csv\n");
    }

    /* 4. branch_foliation.csv — per-cell for k <= 729 */
    {
        FILE *f = fopen("branch_foliation.csv", "w");
        if (!f) { perror("branch_foliation.csv"); return; }
        fprintf(f, "k,r2,r3,dist_unstable,dist_stable,on_unstable,on_stable\n");
        for (int lev = 0; lev < num_levels; lev++) {
            int k = levels[lev].k;
            if (k > 729) continue;  /* skip huge levels */
            for (int i = 0; i < k; i++) {
                for (int j = 0; j < k; j++) {
                    double du = torus_dist(i, j, LOG2_3, k);
                    double ds = torus_dist(i, j, -INV_LOG2_3, k);
                    fprintf(f, "%d,%d,%d,%.9f,%.9f,%d,%d\n",
                            k, i, j, du, ds,
                            (du < 0.5) ? 1 : 0,
                            (ds < 0.5) ? 1 : 0);
                }
            }
        }
        fclose(f);
        printf("  Saved branch_foliation.csv\n");
    }

    /* 5. branch_transitions.csv — per-cell for target levels
     *    For k > 729, only write non-empty cells (too many cells otherwise) */
    {
        FILE *f = fopen("branch_transitions.csv", "w");
        if (!f) { perror("branch_transitions.csv"); return; }
        fprintf(f, "k,r2,r3,ee,eo,oe,oo,valence,entry_type\n");
        for (int lev = 0; lev < num_levels; lev++) {
            if (!levels[lev].track_trans) continue;
            int k = levels[lev].k;
            int sparse = (k > 729);  /* only non-empty cells for large k */
            int64_t rows_written = 0;

            for (int r2 = 0; r2 < k; r2++) {
                for (int r3 = 0; r3 < k; r3++) {
                    int idx = r2 * k + r3;
                    int64_t ee = levels[lev].trans_ee[idx];
                    int64_t eo = levels[lev].trans_eo[idx];
                    int64_t oe = levels[lev].trans_oe[idx];
                    int64_t oo = 0;  /* always 0 by Collatz structure */

                    int valence = (ee > 0) + (eo > 0) + (oe > 0);

                    /* Skip empty cells for large k */
                    if (sparse && valence == 0) continue;

                    const char *entry_type;
                    if (valence == 0) {
                        entry_type = "none";
                    } else if (valence == 1) {
                        if (ee > 0)      entry_type = "ee_only";
                        else if (eo > 0) entry_type = "eo_only";
                        else             entry_type = "oe_only";
                    } else if (valence == 2) {
                        if (ee > 0 && eo > 0) entry_type = "ee_eo";
                        else if (ee > 0)      entry_type = "ee_oe";
                        else                  entry_type = "eo_oe";
                    } else {
                        entry_type = "mixed";
                    }

                    fprintf(f, "%d,%d,%d,%ld,%ld,%ld,%ld,%d,%s\n",
                            k, r2, r3,
                            (long)ee, (long)eo, (long)oe, (long)oo,
                            valence, entry_type);
                    rows_written++;
                }
            }
            printf("  branch_transitions.csv: k=%d wrote %ld rows%s\n",
                   k, (long)rows_written,
                   sparse ? " (non-empty only)" : "");
        }
        fclose(f);
        printf("  Saved branch_transitions.csv\n");
    }

    /* 6. branch_shadow.csv — per-cell for Diophantine levels (Baker bound) */
    {
        FILE *f = fopen("branch_shadow.csv", "w");
        if (!f) { perror("branch_shadow.csv"); return; }
        fprintf(f, "k,r2,r3,dist_irrational,dist_rational,"
                   "shadow_offset,p_odd,cell_type\n");

        for (int d = 0; d < (int)N_DIOPH; d++) {
            int target_k = (int)dioph_levels[d].k;
            double rational_slope = (double)dioph_levels[d].numer
                                  / dioph_levels[d].k;

            int lev_d = -1;
            for (int lev = 0; lev < num_levels; lev++)
                if (levels[lev].k == target_k) { lev_d = lev; break; }
            if (lev_d < 0) continue;

            int k = target_k;
            int sparse = (k > 729);
            int64_t rows_written = 0;
            for (int r2 = 0; r2 < k; r2++) {
                for (int r3 = 0; r3 < k; r3++) {
                    int idx = r2 * k + r3;
                    int64_t ne = levels[lev_d].even_grid[idx];
                    int64_t no = levels[lev_d].odd_grid[idx];
                    int64_t tot = ne + no;

                    /* Skip empty cells for large k */
                    if (sparse && tot == 0) continue;

                    double dist_irr = torus_dist(r2, r3, INV_LOG2_3, k);
                    double dist_rat = torus_dist(r2, r3, rational_slope, k);
                    double shadow = dist_irr - dist_rat;

                    double p_odd = (tot > 0) ? (double)no / tot : 0.0;

                    const char *cell_type;
                    if (tot == 0)              cell_type = "empty";
                    else if (ne > 0 && no > 0) cell_type = "branch";
                    else if (no == 0)          cell_type = "pure_even";
                    else                       cell_type = "pure_odd";

                    fprintf(f, "%d,%d,%d,%.9f,%.9f,%.9f,%.9f,%s\n",
                            k, r2, r3,
                            dist_irr, dist_rat, shadow,
                            p_odd, cell_type);
                    rows_written++;
                }
            }
            printf("  branch_shadow.csv: k=%d wrote %ld rows%s\n",
                   k, (long)rows_written,
                   sparse ? " (non-empty only)" : "");
        }
        fclose(f);
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * main
 * ═══════════════════════════════════════════════════════════════════════ */

int main(int argc, char **argv)
{
    /* Parse arguments: ./branch_locus [N] or ./branch_locus --resume N */
    resume_mode = 0;
    int arg_idx = 1;
    if (argc > 1 && strcmp(argv[1], "--resume") == 0) {
        resume_mode = 1;
        arg_idx = 2;
    }
    N = (argc > arg_idx) ? atol(argv[arg_idx]) : 10000000;
    if (N < 3) { fprintf(stderr, "N must be >= 3\n"); return 1; }

    struct timespec wall_start;
    clock_gettime(CLOCK_MONOTONIC, &wall_start);

    printf("========================================================================\n");
    printf("BRANCH LOCUS ON FINITE TORI%s\n",
           resume_mode ? "  [RESUMING]" : "");
    printf("========================================================================\n");
    printf("N = %ld\n", (long)N);
    printf("Levels: k = 2^a * 3^b  (0 <= a,b <= %d) + Diophantine levels\n\n",
           MAX_EXP);

    printf("Initialising levels...\n");
    init_levels();

    int64_t start_n = 2;

    if (resume_mode) {
        printf("\nLoading binary state...\n");
        int64_t resume_n;
        if (!load_binary_state(&resume_n)) {
            fprintf(stderr, "Resume failed: no valid state file.\n");
            return 1;
        }
        start_n = resume_n + 1;
        printf("  Resuming computation from n=%ld\n", (long)start_n);
    }

    printf("\nInitialising checkpoints...\n");
    checkpoint_init(N);

    /* Print Diophantine approximation quality for key levels */
    printf("Diophantine best-approximant levels included:\n");
    for (int d = 0; d < (int)N_DIOPH; d++) {
        double approx = (double)dioph_levels[d].numer / dioph_levels[d].k;
        double err = fabs(approx - INV_LOG2_3);
        printf("  3^%d = %ld:  %ld/%ld = %.10f  |err| = %.2e\n",
               dioph_levels[d].b, dioph_levels[d].k,
               dioph_levels[d].numer, dioph_levels[d].k,
               approx, err);
    }
    printf("\n");

    compute_branch_data(start_n);
    compute_summaries();
    print_report();
    print_foliation_analysis();
    verify_transitions();
    write_csv_files();

    /* Consistency check: total visits per level must equal total_steps */
    printf("\n========================================================================\n");
    printf("CONSISTENCY CHECK\n");
    printf("========================================================================\n");
    int ok = 1;
    for (int lev = 0; lev < num_levels; lev++) {
        if (summaries[lev].total_visits != total_steps) {
            printf("  FAIL: level k=%d has %ld visits, expected %ld\n",
                   levels[lev].k, (long)summaries[lev].total_visits,
                   (long)total_steps);
            ok = 0;
        }
    }
    if (ok)
        printf("  PASS: all %d levels have consistent visit counts "
               "(%ld steps)\n", num_levels, (long)total_steps);

    /* Close checkpoint file */
    if (ckpt_fp) fclose(ckpt_fp);
    printf("  Saved branch_checkpoints.csv (%d snapshots)\n", n_ckpts);

    /* Cleanup */
    for (int i = 0; i < num_levels; i++) {
        free(levels[i].even_grid);
        free(levels[i].odd_grid);
        free(levels[i].trans_ee);
        free(levels[i].trans_eo);
        free(levels[i].trans_oe);
    }

    struct timespec wall_end;
    clock_gettime(CLOCK_MONOTONIC, &wall_end);
    double wall = (wall_end.tv_sec - wall_start.tv_sec)
                + 1e-9 * (wall_end.tv_nsec - wall_start.tv_nsec);
    printf("\nTotal wall time: %.2fs\n", wall);

    return 0;
}
