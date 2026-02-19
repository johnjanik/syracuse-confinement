/*
 * v2_danger.c
 *
 * Box-Counting & Residence Time Analysis for Dangerous Cells
 *
 * Identifies "dangerous" cells on the torus (Z/3^kZ)^2 where E[v₂] < log₂3,
 * then measures how long Collatz trajectories stay in those cells.
 *
 * Two-pass architecture:
 *   Pass 1 — Collect per-cell v₂ statistics + v₂ autocorrelation
 *   Post   — Identify dangerous cells, compute scale metrics
 *   Pass 2 — Replay trajectories, track consecutive danger residence
 *
 * Output files:
 *   v2_danger_summary.csv     — one row per scale k
 *   v2_danger_residence.csv   — danger residence histogram
 *   v2_danger_correlation.csv — v₂ autocorrelation by lag
 *   v2_danger_hopping.csv     — D→D/D→S/S→D/S→S transition counts + repulsion ratio
 *
 * Usage: ./v2_danger [--N <num>] [--T <steps>] [--k <max_k>] [--min-visits <n>]
 *
 * Compile: gcc -O3 -march=native -fopenmp -o v2_danger v2_danger.c -lm
 */

#define _DEFAULT_SOURCE
#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>
#include <omp.h>

/* ── Constants ──────────────────────────────────────────────────────── */

#define K_MAX_LIMIT  9       /* absolute max scale exponent */
#define MAX_RUN      256     /* max residence histogram bins */
#define MAX_LAG      20      /* autocorrelation lags */
#define LOG2_3       1.58496250072115618
#define OVERFLOW_THRESHOLD  6148914691236517204ULL  /* (UINT64_MAX-1)/3 */

/* ── Data structures ────────────────────────────────────────────────── */

typedef struct {
    uint64_t v2_sum;     /* sum of v₂(3a+1) at odd visits */
    uint64_t count;      /* number of odd visits */
} cell_t;                /* 16 bytes per cell */

typedef struct {
    int k;               /* scale exponent */
    int scale;           /* 3^k */
    cell_t *grid;        /* scale × scale (global merged, Pass 1) */
    uint8_t *danger_map; /* scale × scale (post-process) */
} level_t;

/* Per-scale results */
typedef struct {
    int64_t residence_hist[MAX_RUN + 1]; /* histogram of danger run lengths */
    int64_t n_dangerous;                 /* count of dangerous cells */
    int64_t n_occupied;                  /* cells with count >= min_visits */
    double  moat_width_abs;              /* min torus distance to equilibrium */
    double  moat_width_norm;             /* moat_abs / scale */
    double  mean_v2;                     /* overall mean v₂ at this scale */
    double  v2_variance;                 /* variance of per-cell E[v₂] */
    double  safe_fraction;               /* fraction with min_v2 >= 2 */
} scale_result_t;

/* Global autocorrelation accumulators */
typedef struct {
    double lag_product_sum[MAX_LAG + 1]; /* E[v₂(t) * v₂(t+l)] */
    int64_t lag_count[MAX_LAG + 1];      /* number of pairs at each lag */
    double v2_sum;                        /* for E[v₂] */
    double v2_sq_sum;                     /* for Var(v₂) */
    int64_t v2_count;                     /* total odd steps */
} autocorr_t;

/* Hopping correlation: consecutive odd-step transition counts */
typedef struct {
    int64_t dd;   /* danger → danger */
    int64_t ds;   /* danger → safe   */
    int64_t sd;   /* safe   → danger */
    int64_t ss;   /* safe   → safe   */
} hop_counts_t;

/* ── Global state ───────────────────────────────────────────────────── */

static int64_t  param_N    = 1000000;
static int      param_T    = 0;         /* 0 = run to x=1 */
static int      param_kmax = 7;
static int      param_min_visits = 10;

static int      num_levels;
static level_t  levels[K_MAX_LIMIT];
static int      scales[K_MAX_LIMIT];    /* cached 3^k values */
static scale_result_t results[K_MAX_LIMIT];
static autocorr_t global_autocorr;
static hop_counts_t global_hopping[K_MAX_LIMIT];

static int64_t  total_overflows = 0;
static int64_t  total_odd_steps = 0;
static int64_t  total_trajectories = 0;

/* ── Timer utility (same style as branch_locus.c) ───────────────────── */

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

/* ── Torus distance to equilibrium line ν₂ = log₂3 · ν₃ ────────────── */

static double torus_distance(int a, int b, int scale) {
    /* Distance from cell (a,b) to the line a = log₂3 · b on the torus */
    double diff = fmod((double)a - LOG2_3 * (double)b, (double)scale);
    if (diff < 0) diff += scale;
    if (diff > scale / 2.0) diff = scale - diff;
    return diff;
}

/* ── Compute 3^k ─────────────────────────────────────────────────────── */

static int pow3(int k) {
    int r = 1;
    for (int i = 0; i < k; i++) r *= 3;
    return r;
}

/* ── Initialise levels ──────────────────────────────────────────────── */

static void init_levels(void)
{
    num_levels = param_kmax;
    for (int ki = 0; ki < num_levels; ki++) {
        int k = ki + 1;
        int s = pow3(k);
        levels[ki].k = k;
        levels[ki].scale = s;
        levels[ki].grid = NULL;
        levels[ki].danger_map = NULL;
        scales[ki] = s;
    }
}

/* ══════════════════════════════════════════════════════════════════════
 * Pass 1: Collect per-cell v₂ statistics + v₂ autocorrelation
 *
 * For each n=2..N, follow Collatz trajectory (compressed odd-step form).
 * At each odd step, record v₂(3x+1) into cell grids for all scales,
 * and accumulate lag-product sums for autocorrelation.
 *
 * Strategy: all grids are per-thread private (k<=7 → 3^7=2187,
 * max grid 2187²×12B = 57MB per thread, total ~1.4GB for 24 threads).
 * ══════════════════════════════════════════════════════════════════════ */

static void pass1_collect(void)
{
    printf("\n── Pass 1: Collecting per-cell v₂ statistics ──────────────────────────\n");
    tic();

    int nthreads = omp_get_max_threads();
    printf("  OpenMP: %d threads\n", nthreads);
    printf("  N = %ld, k_max = %d (max scale = %d)\n",
           (long)param_N, param_kmax, scales[num_levels - 1]);

    /* Allocate global merged grids */
    int64_t total_cells = 0;
    for (int ki = 0; ki < num_levels; ki++) {
        int s = scales[ki];
        int64_t sz = (int64_t)s * s;
        levels[ki].grid = (cell_t *)calloc(sz, sizeof(cell_t));
        if (!levels[ki].grid) {
            fprintf(stderr, "Failed to allocate grid for k=%d (%ld cells)\n",
                    ki + 1, (long)sz);
            exit(1);
        }
        total_cells += sz;
    }
    printf("  Global grids: %ld cells (%.1f MB)\n",
           (long)total_cells,
           total_cells * sizeof(cell_t) / (1024.0 * 1024));

    /* Allocate per-thread private grids */
    cell_t **thr_grids = (cell_t **)calloc(
        (size_t)nthreads * num_levels, sizeof(cell_t *));
    for (int t = 0; t < nthreads; t++) {
        for (int ki = 0; ki < num_levels; ki++) {
            int s = scales[ki];
            int64_t sz = (int64_t)s * s;
            thr_grids[t * num_levels + ki] =
                (cell_t *)calloc(sz, sizeof(cell_t));
            if (!thr_grids[t * num_levels + ki]) {
                fprintf(stderr,
                        "Failed to allocate thread %d grid for k=%d\n",
                        t, ki + 1);
                exit(1);
            }
        }
    }

    int64_t per_thread_bytes = 0;
    for (int ki = 0; ki < num_levels; ki++)
        per_thread_bytes += (int64_t)scales[ki] * scales[ki] * sizeof(cell_t);
    printf("  Per-thread private grids: %.1f MB (%d threads = %.1f MB total)\n",
           per_thread_bytes / (1024.0 * 1024),
           nthreads,
           (double)per_thread_bytes * nthreads / (1024.0 * 1024));

    /* Allocate per-thread autocorrelation accumulators */
    double **thr_lag_sum = (double **)calloc(nthreads, sizeof(double *));
    int64_t **thr_lag_count = (int64_t **)calloc(nthreads, sizeof(int64_t *));
    double *thr_v2_sum = (double *)calloc(nthreads, sizeof(double));
    double *thr_v2_sq = (double *)calloc(nthreads, sizeof(double));
    int64_t *thr_v2_count = (int64_t *)calloc(nthreads, sizeof(int64_t));
    int64_t *thr_overflows = (int64_t *)calloc(nthreads, sizeof(int64_t));
    int64_t *thr_odd_steps = (int64_t *)calloc(nthreads, sizeof(int64_t));

    for (int t = 0; t < nthreads; t++) {
        thr_lag_sum[t] = (double *)calloc(MAX_LAG + 1, sizeof(double));
        thr_lag_count[t] = (int64_t *)calloc(MAX_LAG + 1, sizeof(int64_t));
    }

    /* Progress tracking */
    int64_t progress_done = 0;
    double last_report = 0;

    /* ── Parallel section ───────────────────────────────────────────── */

    #pragma omp parallel
    {
        int tid = omp_get_thread_num();

        /* Local grid pointers */
        cell_t *my_grids[K_MAX_LIMIT];
        for (int ki = 0; ki < num_levels; ki++)
            my_grids[ki] = thr_grids[tid * num_levels + ki];

        double *my_lag_sum   = thr_lag_sum[tid];
        int64_t *my_lag_count = thr_lag_count[tid];
        double my_v2_sum     = 0;
        double my_v2_sq_sum  = 0;
        int64_t my_v2_count  = 0;
        int64_t my_overflows = 0;
        int64_t my_odd_steps = 0;

        #pragma omp for schedule(dynamic, 256)
        for (int64_t n = 2; n <= param_N; n++) {
            uint64_t x = (uint64_t)n;
            int nu2 = 0, nu3 = 0;
            int v2_buf[MAX_LAG];
            int buf_pos = 0, buf_len = 0;
            int step_count = 0;

            while (x > 1) {
                if (param_T > 0 && step_count >= param_T) break;

                if (x & 1) {
                    /* Overflow guard */
                    if (x > OVERFLOW_THRESHOLD) {
                        my_overflows++;
                        break;
                    }

                    /* Odd step: compute v₂(3x+1) */
                    uint64_t next = 3ULL * x + 1;
                    int v = __builtin_ctzll(next);

                    /* Record in all private grids */
                    for (int ki = 0; ki < num_levels; ki++) {
                        int s = scales[ki];
                        int cell_idx = (nu2 % s) * s + (nu3 % s);
                        my_grids[ki][cell_idx].v2_sum += v;
                        my_grids[ki][cell_idx].count++;
                    }

                    /* Autocorrelation: accumulate lag products */
                    for (int l = 1; l <= buf_len && l <= MAX_LAG; l++) {
                        int prev_v = v2_buf[(buf_pos - l + MAX_LAG) % MAX_LAG];
                        my_lag_sum[l] += (double)v * prev_v;
                        my_lag_count[l]++;
                    }
                    v2_buf[buf_pos % MAX_LAG] = v;
                    buf_pos++;
                    if (buf_len < MAX_LAG) buf_len++;

                    my_v2_sum += v;
                    my_v2_sq_sum += (double)v * v;
                    my_v2_count++;
                    my_odd_steps++;

                    /* Advance: x = (3x+1) / 2^v */
                    x = next >> v;
                    nu2 += v;
                    nu3++;
                    step_count += v + 1; /* v even steps + 1 odd step */
                } else {
                    /* Even step (only at trajectory start if n is even) */
                    x >>= 1;
                    nu2++;
                    step_count++;
                }
            }

            /* Progress reporting (thread 0 only, every ~1 second) */
            if (tid == 0 && (n & 0xFFFF) == 0) {
                double now = toc();
                if (now - last_report >= 1.0) {
                    int64_t done;
                    #pragma omp atomic read
                    done = progress_done;
                    done += (n - 2); /* approximate */
                    double frac = (double)done / (double)(param_N - 1);
                    if (frac > 1.0) frac = 1.0;

                    char el[32], et[32];
                    fmt_time(now, el, sizeof(el));
                    double eta = (frac > 0.001) ? now * (1.0 - frac) / frac : 0;
                    fmt_time(eta, et, sizeof(et));

                    int bw = 30;
                    int filled = (int)(frac * bw + 0.5);
                    char bar[32];
                    for (int i = 0; i < bw; i++)
                        bar[i] = (i < filled) ? '#' : '.';
                    bar[bw] = '\0';

                    printf("\r  [%s] %5.1f%% | %s elapsed | ETA %s",
                           bar, 100.0 * frac, el, et);
                    fflush(stdout);
                    last_report = now;
                }
            }
        }

        /* Store per-thread accumulators */
        thr_v2_sum[tid]   = my_v2_sum;
        thr_v2_sq[tid]    = my_v2_sq_sum;
        thr_v2_count[tid] = my_v2_count;
        thr_overflows[tid] = my_overflows;
        thr_odd_steps[tid] = my_odd_steps;

        /* Merge private grids into global */
        #pragma omp critical
        {
            for (int ki = 0; ki < num_levels; ki++) {
                int s = scales[ki];
                int64_t sz = (int64_t)s * s;
                cell_t *global = levels[ki].grid;
                cell_t *local  = my_grids[ki];
                for (int64_t c = 0; c < sz; c++) {
                    global[c].v2_sum += local[c].v2_sum;
                    global[c].count  += local[c].count;
                }
            }
        }
    }
    /* end parallel */

    printf("\r  [##############################] 100.0%% | done                       \n");

    /* Merge autocorrelation accumulators */
    memset(&global_autocorr, 0, sizeof(global_autocorr));
    for (int t = 0; t < nthreads; t++) {
        for (int l = 1; l <= MAX_LAG; l++) {
            global_autocorr.lag_product_sum[l] += thr_lag_sum[t][l];
            global_autocorr.lag_count[l]       += thr_lag_count[t][l];
        }
        global_autocorr.v2_sum    += thr_v2_sum[t];
        global_autocorr.v2_sq_sum += thr_v2_sq[t];
        global_autocorr.v2_count  += thr_v2_count[t];
        total_overflows           += thr_overflows[t];
        total_odd_steps           += thr_odd_steps[t];
    }
    total_trajectories = param_N - 1; /* n=2..N */

    double dt = toc();
    char el[32];
    fmt_time(dt, el, sizeof(el));
    printf("  Pass 1 complete: %s, %ld trajectories, %ld odd steps",
           el, (long)total_trajectories, (long)total_odd_steps);
    if (total_overflows > 0)
        printf(", %ld overflows", (long)total_overflows);
    printf("\n");

    /* Free per-thread allocations */
    for (int t = 0; t < nthreads; t++) {
        for (int ki = 0; ki < num_levels; ki++)
            free(thr_grids[t * num_levels + ki]);
        free(thr_lag_sum[t]);
        free(thr_lag_count[t]);
    }
    free(thr_grids);
    free(thr_lag_sum);
    free(thr_lag_count);
    free(thr_v2_sum);
    free(thr_v2_sq);
    free(thr_v2_count);
    free(thr_overflows);
    free(thr_odd_steps);
}

/* ══════════════════════════════════════════════════════════════════════
 * Post-process: Identify dangerous cells and compute scale metrics
 * ══════════════════════════════════════════════════════════════════════ */

static void postprocess_danger(void)
{
    printf("\n── Post-process: Identifying dangerous cells ──────────────────────────\n");

    for (int ki = 0; ki < num_levels; ki++) {
        int s = scales[ki];
        int64_t sz = (int64_t)s * s;

        levels[ki].danger_map = (uint8_t *)calloc(sz, sizeof(uint8_t));
        if (!levels[ki].danger_map) {
            fprintf(stderr, "Failed to allocate danger map for k=%d\n", ki + 1);
            exit(1);
        }

        scale_result_t *res = &results[ki];
        memset(res, 0, sizeof(*res));

        /* Accumulate per-cell statistics */
        double sum_ev2 = 0;
        double sum_ev2_sq = 0;
        int64_t n_occupied = 0;
        int64_t n_dangerous = 0;
        int64_t n_safe = 0;       /* cells where all visits had v₂ >= 2 */
        double min_moat = 1e18;

        for (int64_t c = 0; c < sz; c++) {
            if (levels[ki].grid[c].count < (uint64_t)param_min_visits)
                continue;

            n_occupied++;
            double ev2 = (double)levels[ki].grid[c].v2_sum
                       / levels[ki].grid[c].count;
            sum_ev2 += ev2;
            sum_ev2_sq += ev2 * ev2;

            if (ev2 < LOG2_3) {
                levels[ki].danger_map[c] = 1;
                n_dangerous++;

                /* Compute torus distance of this cell to equilibrium */
                int a = (int)(c / s);
                int b = (int)(c % s);
                double d = torus_distance(a, b, s);
                if (d < min_moat) min_moat = d;
            }

            /* "Safe" = minimum possible v₂ at this cell is ≥ 2,
               approximated by E[v₂] ≥ 2.0 */
            if (ev2 >= 2.0) n_safe++;
        }

        res->n_occupied = n_occupied;
        res->n_dangerous = n_dangerous;
        if (n_occupied > 0) {
            res->mean_v2 = sum_ev2 / n_occupied;
            res->v2_variance = sum_ev2_sq / n_occupied
                             - res->mean_v2 * res->mean_v2;
        }
        res->safe_fraction = (n_occupied > 0)
            ? (double)n_safe / n_occupied : 0;
        res->moat_width_abs = (n_dangerous > 0) ? min_moat : -1;
        res->moat_width_norm = (n_dangerous > 0) ? min_moat / s : -1;

        printf("  k=%d (3^k=%d): %ld occupied, %ld dangerous (%.4f%%), "
               "E[v₂]=%.4f, safe=%.1f%%\n",
               ki + 1, s,
               (long)n_occupied, (long)n_dangerous,
               n_occupied > 0 ? 100.0 * n_dangerous / n_occupied : 0,
               res->mean_v2,
               100.0 * res->safe_fraction);
    }

    /* Print autocorrelation summary */
    printf("\n  v₂ Autocorrelation (global):\n");
    double mean_v2 = global_autocorr.v2_count > 0
        ? global_autocorr.v2_sum / global_autocorr.v2_count : 0;
    double var_v2 = global_autocorr.v2_count > 0
        ? global_autocorr.v2_sq_sum / global_autocorr.v2_count - mean_v2 * mean_v2
        : 0;
    printf("  E[v₂] = %.6f, Var(v₂) = %.6f\n", mean_v2, var_v2);
    for (int l = 1; l <= MAX_LAG && l <= 5; l++) {
        double mean_prod = global_autocorr.lag_count[l] > 0
            ? global_autocorr.lag_product_sum[l] / global_autocorr.lag_count[l]
            : 0;
        double autocorr = (var_v2 > 0)
            ? (mean_prod - mean_v2 * mean_v2) / var_v2 : 0;
        printf("  lag %2d: autocorr = %+.6f (%ld pairs)\n",
               l, autocorr, (long)global_autocorr.lag_count[l]);
    }
}

/* ══════════════════════════════════════════════════════════════════════
 * Pass 2: Replay trajectories for danger residence tracking
 *
 * Same compressed trajectory loop as Pass 1, but now look up danger
 * bitmaps and track consecutive runs of dangerous odd steps.
 * ══════════════════════════════════════════════════════════════════════ */

static void pass2_residence(void)
{
    printf("\n── Pass 2: Danger residence tracking ──────────────────────────────────\n");
    tic();

    int nthreads = omp_get_max_threads();

    /* Per-thread histograms */
    int64_t **thr_hist = (int64_t **)calloc(
        (size_t)nthreads * num_levels, sizeof(int64_t *));
    for (int t = 0; t < nthreads; t++) {
        for (int ki = 0; ki < num_levels; ki++) {
            thr_hist[t * num_levels + ki] =
                (int64_t *)calloc(MAX_RUN + 1, sizeof(int64_t));
        }
    }

    /* Per-thread hopping transition counts */
    hop_counts_t *thr_hops = (hop_counts_t *)calloc(
        (size_t)nthreads * num_levels, sizeof(hop_counts_t));

    /* Cache danger map pointers */
    uint8_t *dmaps[K_MAX_LIMIT];
    for (int ki = 0; ki < num_levels; ki++)
        dmaps[ki] = levels[ki].danger_map;

    /* Progress tracking */
    double last_report = 0;

    /* ── Parallel section ───────────────────────────────────────────── */

    #pragma omp parallel
    {
        int tid = omp_get_thread_num();

        int64_t *my_hist[K_MAX_LIMIT];
        hop_counts_t *my_hops[K_MAX_LIMIT];
        for (int ki = 0; ki < num_levels; ki++) {
            my_hist[ki] = thr_hist[tid * num_levels + ki];
            my_hops[ki] = &thr_hops[tid * num_levels + ki];
        }

        #pragma omp for schedule(dynamic, 256)
        for (int64_t n = 2; n <= param_N; n++) {
            uint64_t x = (uint64_t)n;
            int nu2 = 0, nu3 = 0;
            int run_len[K_MAX_LIMIT];
            int8_t prev_danger[K_MAX_LIMIT]; /* -1 = no prev, 0 = safe, 1 = danger */
            int step_count = 0;
            memset(run_len, 0, sizeof(int) * num_levels);
            memset(prev_danger, -1, sizeof(int8_t) * num_levels);

            while (x > 1) {
                if (param_T > 0 && step_count >= param_T) break;

                if (x & 1) {
                    if (x > OVERFLOW_THRESHOLD) break;

                    uint64_t next = 3ULL * x + 1;
                    int v = __builtin_ctzll(next);

                    for (int ki = 0; ki < num_levels; ki++) {
                        int s = scales[ki];
                        int cell_idx = (nu2 % s) * s + (nu3 % s);
                        int cur_d = dmaps[ki][cell_idx];

                        /* Hopping correlation: count transitions */
                        if (prev_danger[ki] >= 0) {
                            if (prev_danger[ki]) {
                                if (cur_d) my_hops[ki]->dd++;
                                else       my_hops[ki]->ds++;
                            } else {
                                if (cur_d) my_hops[ki]->sd++;
                                else       my_hops[ki]->ss++;
                            }
                        }
                        prev_danger[ki] = cur_d;

                        /* Residence run tracking */
                        if (cur_d) {
                            run_len[ki]++;
                        } else {
                            if (run_len[ki] > 0) {
                                int bin = run_len[ki] < MAX_RUN
                                        ? run_len[ki] : MAX_RUN;
                                my_hist[ki][bin]++;
                            }
                            run_len[ki] = 0;
                        }
                    }

                    x = next >> v;
                    nu2 += v;
                    nu3++;
                    step_count += v + 1;
                } else {
                    x >>= 1;
                    nu2++;
                    step_count++;
                }
            }
            /* Flush trailing runs */
            for (int ki = 0; ki < num_levels; ki++) {
                if (run_len[ki] > 0) {
                    int bin = run_len[ki] < MAX_RUN
                            ? run_len[ki] : MAX_RUN;
                    my_hist[ki][bin]++;
                }
            }

            /* Progress reporting (thread 0 only) */
            if (tid == 0 && (n & 0xFFFF) == 0) {
                double now = toc();
                if (now - last_report >= 1.0) {
                    double frac = (double)(n - 2) / (double)(param_N - 1);
                    if (frac > 1.0) frac = 1.0;

                    char el[32], et[32];
                    fmt_time(now, el, sizeof(el));
                    double eta = (frac > 0.001)
                        ? now * (1.0 - frac) / frac : 0;
                    fmt_time(eta, et, sizeof(et));

                    int bw = 30;
                    int filled = (int)(frac * bw + 0.5);
                    char bar[32];
                    for (int i = 0; i < bw; i++)
                        bar[i] = (i < filled) ? '#' : '.';
                    bar[bw] = '\0';

                    printf("\r  [%s] %5.1f%% | %s elapsed | ETA %s",
                           bar, 100.0 * frac, el, et);
                    fflush(stdout);
                    last_report = now;
                }
            }
        }

        /* Merge histograms and hopping counts */
        #pragma omp critical
        {
            for (int ki = 0; ki < num_levels; ki++) {
                for (int r = 0; r <= MAX_RUN; r++)
                    results[ki].residence_hist[r] += my_hist[ki][r];
                global_hopping[ki].dd += my_hops[ki]->dd;
                global_hopping[ki].ds += my_hops[ki]->ds;
                global_hopping[ki].sd += my_hops[ki]->sd;
                global_hopping[ki].ss += my_hops[ki]->ss;
            }
        }
    }
    /* end parallel */

    printf("\r  [##############################] 100.0%% | done                       \n");

    double dt = toc();
    char el[32];
    fmt_time(dt, el, sizeof(el));
    printf("  Pass 2 complete: %s\n", el);

    /* Print residence summary */
    for (int ki = 0; ki < num_levels; ki++) {
        int64_t total_runs = 0;
        int64_t max_run = 0;
        for (int r = 1; r <= MAX_RUN; r++) {
            if (results[ki].residence_hist[r] > 0) {
                total_runs += results[ki].residence_hist[r];
                max_run = r;
            }
        }
        printf("  k=%d: %ld danger runs, max length = %ld\n",
               ki + 1, (long)total_runs, (long)max_run);
    }

    /* Free per-thread histograms and hopping counts */
    for (int t = 0; t < nthreads; t++)
        for (int ki = 0; ki < num_levels; ki++)
            free(thr_hist[t * num_levels + ki]);
    free(thr_hist);
    free(thr_hops);
}

/* ══════════════════════════════════════════════════════════════════════
 * Output: Write CSV files and print summary
 * ══════════════════════════════════════════════════════════════════════ */

static void write_csvs(void)
{
    printf("\n── Writing CSV files ──────────────────────────────────────────────────\n");

    /* 1. Summary CSV */
    FILE *f = fopen("v2_danger_summary.csv", "w");
    if (!f) { perror("v2_danger_summary.csv"); return; }
    fprintf(f, "k,scale,cells_occupied,cells_dangerous,dangerous_frac,"
               "moat_abs,moat_norm,mean_v2,v2_var,safe_frac\n");
    for (int ki = 0; ki < num_levels; ki++) {
        scale_result_t *r = &results[ki];
        double dfrac = (r->n_occupied > 0)
            ? (double)r->n_dangerous / r->n_occupied : 0;
        fprintf(f, "%d,%d,%ld,%ld,%.10f,%.6f,%.10f,%.10f,%.10f,%.10f\n",
                ki + 1, scales[ki],
                (long)r->n_occupied, (long)r->n_dangerous, dfrac,
                r->moat_width_abs, r->moat_width_norm,
                r->mean_v2, r->v2_variance, r->safe_fraction);
    }
    fclose(f);
    printf("  v2_danger_summary.csv written\n");

    /* 2. Residence histogram CSV */
    f = fopen("v2_danger_residence.csv", "w");
    if (!f) { perror("v2_danger_residence.csv"); return; }
    fprintf(f, "k,run_length,count\n");
    for (int ki = 0; ki < num_levels; ki++) {
        for (int r = 1; r <= MAX_RUN; r++) {
            if (results[ki].residence_hist[r] > 0) {
                fprintf(f, "%d,%d,%ld\n",
                        ki + 1, r, (long)results[ki].residence_hist[r]);
            }
        }
    }
    fclose(f);
    printf("  v2_danger_residence.csv written\n");

    /* 3. Autocorrelation CSV */
    f = fopen("v2_danger_correlation.csv", "w");
    if (!f) { perror("v2_danger_correlation.csv"); return; }
    fprintf(f, "lag,autocorrelation,count\n");
    double mean_v2 = global_autocorr.v2_count > 0
        ? global_autocorr.v2_sum / global_autocorr.v2_count : 0;
    double var_v2 = global_autocorr.v2_count > 0
        ? global_autocorr.v2_sq_sum / global_autocorr.v2_count - mean_v2 * mean_v2
        : 0;
    for (int l = 1; l <= MAX_LAG; l++) {
        double mean_prod = global_autocorr.lag_count[l] > 0
            ? global_autocorr.lag_product_sum[l] / global_autocorr.lag_count[l]
            : 0;
        double autocorr = (var_v2 > 0)
            ? (mean_prod - mean_v2 * mean_v2) / var_v2 : 0;
        fprintf(f, "%d,%.10f,%ld\n",
                l, autocorr, (long)global_autocorr.lag_count[l]);
    }
    fclose(f);
    printf("  v2_danger_correlation.csv written\n");

    /* 4. Hopping correlation CSV */
    f = fopen("v2_danger_hopping.csv", "w");
    if (!f) { perror("v2_danger_hopping.csv"); return; }
    fprintf(f, "k,dd,ds,sd,ss,p_danger,p_danger_given_danger,"
               "p_danger_given_safe,repulsion_ratio\n");
    for (int ki = 0; ki < num_levels; ki++) {
        hop_counts_t *h = &global_hopping[ki];
        int64_t total = h->dd + h->ds + h->sd + h->ss;
        if (total == 0) continue;
        double p_d = (double)(h->dd + h->sd) / total;
        int64_t from_d = h->dd + h->ds;
        int64_t from_s = h->sd + h->ss;
        double p_d_given_d = (from_d > 0) ? (double)h->dd / from_d : 0;
        double p_d_given_s = (from_s > 0) ? (double)h->sd / from_s : 0;
        double repulsion = (p_d > 0) ? p_d_given_d / p_d : 0;
        fprintf(f, "%d,%ld,%ld,%ld,%ld,%.10f,%.10f,%.10f,%.10f\n",
                ki + 1,
                (long)h->dd, (long)h->ds, (long)h->sd, (long)h->ss,
                p_d, p_d_given_d, p_d_given_s, repulsion);
    }
    fclose(f);
    printf("  v2_danger_hopping.csv written\n");
}

/* ══════════════════════════════════════════════════════════════════════
 * Print final summary report
 * ══════════════════════════════════════════════════════════════════════ */

static void print_report(void)
{
    printf("\n========================================================================\n");
    printf("V₂ DANGER ANALYSIS — FINAL REPORT\n");
    printf("========================================================================\n");
    printf("N = %ld, k_max = %d, min_visits = %d\n",
           (long)param_N, param_kmax, param_min_visits);
    printf("Total trajectories: %ld\n", (long)total_trajectories);
    printf("Total odd steps:    %ld\n", (long)total_odd_steps);
    if (total_overflows > 0)
        printf("Overflows:          %ld\n", (long)total_overflows);

    /* Global v₂ stats */
    double mean_v2 = global_autocorr.v2_count > 0
        ? global_autocorr.v2_sum / global_autocorr.v2_count : 0;
    double var_v2 = global_autocorr.v2_count > 0
        ? global_autocorr.v2_sq_sum / global_autocorr.v2_count - mean_v2 * mean_v2
        : 0;
    printf("\nGlobal v₂: E[v₂] = %.6f (log₂3 = %.6f), Var = %.6f\n",
           mean_v2, LOG2_3, var_v2);

    /* Per-scale table */
    printf("\n  %-4s  %-6s  %-10s  %-10s  %-12s  %-8s  %-8s  %-8s\n",
           "k", "3^k", "occupied", "dangerous", "danger_frac", "moat",
           "E[v₂]", "safe%");
    printf("  ──────────────────────────────────────────────────────────────────\n");
    for (int ki = 0; ki < num_levels; ki++) {
        scale_result_t *r = &results[ki];
        double dfrac = (r->n_occupied > 0)
            ? (double)r->n_dangerous / r->n_occupied : 0;
        printf("  %-4d  %-6d  %-10ld  %-10ld  %-12.6f  %-8.3f  %-8.4f  %-7.1f%%\n",
               ki + 1, scales[ki],
               (long)r->n_occupied, (long)r->n_dangerous, dfrac,
               r->moat_width_abs >= 0 ? r->moat_width_abs : 0,
               r->mean_v2, 100.0 * r->safe_fraction);
    }

    /* Residence histogram summary */
    printf("\n  Danger Residence (consecutive dangerous odd steps):\n");
    printf("  %-4s  %-10s  %-10s  %-10s  %-12s\n",
           "k", "runs", "max_len", "mean_len", "tail_frac");
    printf("  ────────────────────────────────────────────────────\n");
    for (int ki = 0; ki < num_levels; ki++) {
        int64_t total_runs = 0;
        int64_t total_steps_in_runs = 0;
        int64_t max_run = 0;
        int64_t tail_runs = 0; /* runs of length >= 5 */
        for (int r = 1; r <= MAX_RUN; r++) {
            int64_t cnt = results[ki].residence_hist[r];
            if (cnt > 0) {
                total_runs += cnt;
                total_steps_in_runs += cnt * r;
                max_run = r;
                if (r >= 5) tail_runs += cnt;
            }
        }
        double mean_len = (total_runs > 0)
            ? (double)total_steps_in_runs / total_runs : 0;
        double tail_frac = (total_runs > 0)
            ? (double)tail_runs / total_runs : 0;
        printf("  %-4d  %-10ld  %-10ld  %-10.3f  %-12.6f\n",
               ki + 1, (long)total_runs, (long)max_run, mean_len, tail_frac);
    }

    /* Hopping correlation summary */
    printf("\n  Hopping Correlation (consecutive odd-step transitions):\n");
    printf("  %-4s  %10s  %10s  %-10s  %-10s  %-10s  %-10s\n",
           "k", "D→D", "D→S", "P(D)", "P(D|D)", "P(D|S)", "Repulsion");
    printf("  ──────────────────────────────────────────────────────────────────\n");
    for (int ki = 0; ki < num_levels; ki++) {
        hop_counts_t *h = &global_hopping[ki];
        int64_t total = h->dd + h->ds + h->sd + h->ss;
        if (total == 0) continue;
        double p_d = (double)(h->dd + h->sd) / total;
        int64_t from_d = h->dd + h->ds;
        int64_t from_s = h->sd + h->ss;
        double p_d_given_d = (from_d > 0) ? (double)h->dd / from_d : 0;
        double p_d_given_s = (from_s > 0) ? (double)h->sd / from_s : 0;
        double repulsion = (p_d > 0) ? p_d_given_d / p_d : 0;
        printf("  %-4d  %10ld  %10ld  %-10.6f  %-10.6f  %-10.6f  %-10.4f\n",
               ki + 1,
               (long)h->dd, (long)h->ds,
               p_d, p_d_given_d, p_d_given_s, repulsion);
    }
    printf("\n  Interpretation: Repulsion < 1 = active repulsion from danger.\n");
    printf("  Repulsion ≈ 1 = random (sparsity alone kills long runs).\n");
    printf("  Repulsion > 1 = clustering (stone-skipping, bad for proof).\n");

    /* Autocorrelation summary */
    printf("\n  v₂ Autocorrelation:\n");
    printf("  %-6s  %-14s  %-14s\n", "lag", "autocorr", "pairs");
    printf("  ──────────────────────────────────\n");
    for (int l = 1; l <= MAX_LAG; l++) {
        double mean_prod = global_autocorr.lag_count[l] > 0
            ? global_autocorr.lag_product_sum[l] / global_autocorr.lag_count[l]
            : 0;
        double autocorr = (var_v2 > 0)
            ? (mean_prod - mean_v2 * mean_v2) / var_v2 : 0;
        printf("  %-6d  %+.10f  %ld\n",
               l, autocorr, (long)global_autocorr.lag_count[l]);
    }
}

/* ══════════════════════════════════════════════════════════════════════
 * Command-line parsing
 * ══════════════════════════════════════════════════════════════════════ */

static void parse_args(int argc, char **argv)
{
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--N") == 0 && i + 1 < argc) {
            param_N = atol(argv[++i]);
        } else if (strcmp(argv[i], "--T") == 0 && i + 1 < argc) {
            param_T = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--k") == 0 && i + 1 < argc) {
            param_kmax = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--min-visits") == 0 && i + 1 < argc) {
            param_min_visits = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            printf("Usage: %s [--N <num>] [--T <steps>] [--k <max_k>] "
                   "[--min-visits <n>]\n", argv[0]);
            printf("  --N <num>         Number of starting values (default: 1000000)\n");
            printf("  --T <steps>       Max steps per trajectory, 0=unlimited "
                   "(default: 0)\n");
            printf("  --k <max_k>       Maximum scale exponent 3^k "
                   "(default: 7, max: %d)\n", K_MAX_LIMIT);
            printf("  --min-visits <n>  Min odd visits to classify a cell "
                   "(default: 10)\n");
            exit(0);
        } else {
            fprintf(stderr, "Unknown argument: %s\n", argv[i]);
            fprintf(stderr, "Use --help for usage information.\n");
            exit(1);
        }
    }

    if (param_N < 3) {
        fprintf(stderr, "N must be >= 3\n");
        exit(1);
    }
    if (param_kmax < 1 || param_kmax > K_MAX_LIMIT) {
        fprintf(stderr, "k must be 1..%d\n", K_MAX_LIMIT);
        exit(1);
    }
    if (param_min_visits < 1) {
        fprintf(stderr, "min-visits must be >= 1\n");
        exit(1);
    }
}

/* ══════════════════════════════════════════════════════════════════════
 * Main
 * ══════════════════════════════════════════════════════════════════════ */

int main(int argc, char **argv)
{
    parse_args(argc, argv);

    printf("========================================================================\n");
    printf("V₂ DANGER ANALYSIS: BOX-COUNTING & RESIDENCE TIME\n");
    printf("========================================================================\n");
    printf("N = %ld, T = %s, k_max = %d (max scale = 3^%d = %d)\n",
           (long)param_N,
           param_T > 0 ? "limited" : "unlimited",
           param_kmax, param_kmax, pow3(param_kmax));
    printf("min_visits = %d, log₂3 = %.15f\n", param_min_visits, LOG2_3);
    printf("OpenMP threads: %d\n", omp_get_max_threads());

    init_levels();

    /* Print level table */
    printf("\n  %-4s  %-8s  %-12s\n", "k", "3^k", "grid_cells");
    printf("  ──────────────────────────\n");
    int64_t total_grid_mem = 0;
    for (int ki = 0; ki < num_levels; ki++) {
        int s = scales[ki];
        int64_t sz = (int64_t)s * s;
        printf("  %-4d  %-8d  %-12ld\n", ki + 1, s, (long)sz);
        total_grid_mem += sz * sizeof(cell_t);
    }
    printf("  Total grid memory (1 copy): %.1f MB\n",
           total_grid_mem / (1024.0 * 1024));
    printf("  Estimated total with %d threads: %.1f MB\n",
           omp_get_max_threads(),
           (double)total_grid_mem * omp_get_max_threads() / (1024.0 * 1024));

    pass1_collect();
    postprocess_danger();
    pass2_residence();
    print_report();
    write_csvs();

    /* Free grids and danger maps */
    for (int ki = 0; ki < num_levels; ki++) {
        free(levels[ki].grid);
        free(levels[ki].danger_map);
    }

    printf("\n========================================================================\n");
    printf("Done.\n");
    return 0;
}
