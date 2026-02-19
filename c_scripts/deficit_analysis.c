/*
 * deficit_analysis.c — Verify the Sliding Window Condition (SWC) for Collatz
 *
 * For each n in [1, N], run the UNCOMPRESSED Collatz trajectory:
 *   x_{t+1} = 3*x_t + 1  if x_t odd
 *   x_{t+1} = x_t / 2    if x_t even
 *
 * Track ν₃(t) = number of odd steps in first t steps.
 * deficit(t) = 3·ν₃(t) - t
 * SWC: ∃ W ≥ 1 s.t. ∀ t: deficit(t+W) ≤ deficit(t)
 *       equivalently: 3·(ν₃(t+W) - ν₃(t)) ≤ W
 *
 * Compile: gcc -O3 -march=native -fopenmp -o deficit_analysis deficit_analysis.c -lm
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

/* ---------- constants ---------- */
#define T_MAX        10000      /* max uncompressed steps before giving up */
#define HIST_MAX     2000       /* histogram bins for W_min */
#define CHECKPOINT   10000000   /* progress checkpoint every 10M */
#define TOP_K        100        /* extremes to track */

/* ---------- timer ---------- */
static struct timespec _ts;
static void tic(void) { clock_gettime(CLOCK_MONOTONIC, &_ts); }
static double toc(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (now.tv_sec - _ts.tv_sec) + 1e-9 * (now.tv_nsec - _ts.tv_nsec);
}
static void fmt_time(double s, char *buf, size_t len) {
    int h = (int)(s / 3600), m = ((int)s % 3600) / 60, sec = (int)s % 60;
    if (s < 60)        snprintf(buf, len, "%5.1fs", s);
    else if (s < 3600) snprintf(buf, len, "%dm%02ds", m, sec);
    else                snprintf(buf, len, "%dh%02dm%02ds", h, m, sec);
}

/* ---------- globals ---------- */
static int64_t param_N = 1000000000LL;  /* default 10^9 */

/* ---------- per-thread accumulators ---------- */
typedef struct {
    int64_t  wmin_sum;
    int      max_wmin;
    int      max_deficit;
    int      max_stop;
    int64_t  violations;             /* W_min > HIST_MAX or no W found */
    int64_t  wmin_hist[HIST_MAX + 1]; /* [1..HIST_MAX] */
    /* P(D|D) tracking */
    int64_t  dd_count;
    int64_t  d_count;
    /* top-K extremes: min-heap sorted ascending by wmin */
    int      top_count;
    int64_t  top_n[TOP_K];
    int      top_wmin[TOP_K];
    int      top_deficit[TOP_K];
    int      top_stop[TOP_K];
} thread_acc_t;

static void acc_insert_extreme(thread_acc_t *a, int64_t n, int wmin, int deficit, int stop) {
    if (a->top_count < TOP_K) {
        int i = a->top_count++;
        a->top_n[i] = n; a->top_wmin[i] = wmin;
        a->top_deficit[i] = deficit; a->top_stop[i] = stop;
        while (i > 0 && a->top_wmin[i] < a->top_wmin[i - 1]) {
            int64_t tn = a->top_n[i]; int tw = a->top_wmin[i];
            int td = a->top_deficit[i]; int ts = a->top_stop[i];
            a->top_n[i] = a->top_n[i-1]; a->top_wmin[i] = a->top_wmin[i-1];
            a->top_deficit[i] = a->top_deficit[i-1]; a->top_stop[i] = a->top_stop[i-1];
            a->top_n[i-1] = tn; a->top_wmin[i-1] = tw;
            a->top_deficit[i-1] = td; a->top_stop[i-1] = ts;
            i--;
        }
    } else if (wmin > a->top_wmin[0]) {
        a->top_n[0] = n; a->top_wmin[0] = wmin;
        a->top_deficit[0] = deficit; a->top_stop[0] = stop;
        int i = 0;
        while (i < TOP_K - 1 && a->top_wmin[i] > a->top_wmin[i + 1]) {
            int64_t tn = a->top_n[i]; int tw = a->top_wmin[i];
            int td = a->top_deficit[i]; int ts = a->top_stop[i];
            a->top_n[i] = a->top_n[i+1]; a->top_wmin[i] = a->top_wmin[i+1];
            a->top_deficit[i] = a->top_deficit[i+1]; a->top_stop[i] = a->top_stop[i+1];
            a->top_n[i+1] = tn; a->top_wmin[i+1] = tw;
            a->top_deficit[i+1] = td; a->top_stop[i+1] = ts;
            i++;
        }
    }
}

/* ---------- argument parsing ---------- */
static void parse_args(int argc, char **argv) {
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--N") == 0 && i + 1 < argc)
            param_N = atol(argv[++i]);
        else if (argv[i][0] != '-')
            param_N = atol(argv[i]);
    }
    if (param_N < 1) { fprintf(stderr, "N must be >= 1\n"); exit(1); }
}

/* ---------- process one trajectory ---------- */
static void process_n(int64_t n, thread_acc_t *acc) {
    int deficit[T_MAX + 1];
    uint64_t x = (uint64_t)n;
    int nu3 = 0;
    int T = 0;
    int last_odd_was_danger = -1;

    deficit[0] = 0;

    for (int t = 0; t < T_MAX; t++) {
        if (x == 1 && t > 0) { T = t; break; }

        if (x & 1) {
            if (x > UINT64_MAX / 3 - 1) { T = t; break; }
            uint64_t next = 3 * x + 1;
            int v2 = __builtin_ctzll(next);
            int danger = (v2 == 1);

            if (last_odd_was_danger == 1) {
                acc->d_count++;
                if (danger) acc->dd_count++;
            }
            last_odd_was_danger = danger;

            nu3++;
            x = next;
        } else {
            x = x >> 1;
        }
        deficit[t + 1] = 3 * nu3 - (t + 1);
    }
    if (T == 0) T = T_MAX;

    /* Max deficit over trajectory */
    int max_def = 0;
    for (int t = 0; t <= T; t++)
        if (deficit[t] > max_def) max_def = deficit[t];

    /* Find W_min: smallest W s.t. ∀ t ∈ [0, T-W]: deficit[t+W] ≤ deficit[t]
     * Search W from 1 up to T. Each failing W exits early on first violation. */
    int wmin = 0;
    for (int W = 1; W <= T; W++) {
        int ok = 1;
        for (int t = 0; t <= T - W; t++) {
            if (deficit[t + W] > deficit[t]) { ok = 0; break; }
        }
        if (ok) { wmin = W; break; }
    }

    if (wmin == 0) {
        /* Should not happen for trajectories reaching 1 */
        acc->violations++;
        wmin = T + 1;
    }

    /* Update accumulators */
    acc->wmin_sum += wmin;
    if (wmin > acc->max_wmin) acc->max_wmin = wmin;
    if (max_def > acc->max_deficit) acc->max_deficit = max_def;
    if (T > acc->max_stop) acc->max_stop = T;
    if (wmin >= 1 && wmin <= HIST_MAX)
        acc->wmin_hist[wmin]++;

    acc_insert_extreme(acc, n, wmin, max_def, T);
}

/* ---------- merge extremes ---------- */
static void merge_extremes(thread_acc_t *dst, const thread_acc_t *src) {
    for (int i = 0; i < src->top_count; i++)
        acc_insert_extreme(dst, src->top_n[i], src->top_wmin[i],
                           src->top_deficit[i], src->top_stop[i]);
}

/* ---------- main ---------- */
int main(int argc, char **argv) {
    parse_args(argc, argv);

    int nthreads = omp_get_max_threads();
    printf("=== Deficit / SWC Analysis ===\n");
    printf("  N         = %ld\n", (long)param_N);
    printf("  T_MAX     = %d\n", T_MAX);
    printf("  HIST_MAX  = %d\n", HIST_MAX);
    printf("  Threads   = %d\n", nthreads);
    printf("  Per-thread: deficit[%d] = %.1f KB (stack), acc = %.1f KB\n",
           T_MAX + 1, (T_MAX + 1) * sizeof(int) / 1024.0,
           sizeof(thread_acc_t) / 1024.0);

    thread_acc_t *accs = (thread_acc_t *)calloc(nthreads, sizeof(thread_acc_t));
    if (!accs) { perror("calloc accs"); return 1; }

    FILE *f_summary = fopen("deficit_swc_summary.csv", "w");
    if (!f_summary) { perror("deficit_swc_summary.csv"); return 1; }
    fprintf(f_summary, "N_checkpoint,max_W_min,mean_W_min,max_deficit,violations,max_stopping_time,pdd_rate\n");

    int64_t global_hist[HIST_MAX + 1];
    memset(global_hist, 0, sizeof(global_hist));

    thread_acc_t global_extremes;
    memset(&global_extremes, 0, sizeof(global_extremes));

    int64_t  g_wmin_sum = 0;
    int      g_max_wmin = 0;
    int      g_max_deficit = 0;
    int      g_max_stop = 0;
    int64_t  g_violations = 0;
    int64_t  g_dd_count = 0;
    int64_t  g_d_count = 0;

    tic();
    double last_report = 0;
    int64_t processed = 0;

    int64_t chunk_start = 1;
    while (chunk_start <= param_N) {
        int64_t chunk_end = chunk_start + CHECKPOINT - 1;
        if (chunk_end > param_N) chunk_end = param_N;
        int64_t chunk_size = chunk_end - chunk_start + 1;

        for (int t = 0; t < nthreads; t++)
            memset(&accs[t], 0, sizeof(thread_acc_t));

        #pragma omp parallel
        {
            int tid = omp_get_thread_num();
            thread_acc_t *my = &accs[tid];

            #pragma omp for schedule(dynamic, 1024)
            for (int64_t n = chunk_start; n <= chunk_end; n++) {
                process_n(n, my);

                if (tid == 0 && (n & 0x3FFF) == 0) {
                    double now = toc();
                    if (now - last_report >= 2.0) {
                        last_report = now;
                        double total_done = (double)(processed + (n - chunk_start));
                        double frac = total_done / param_N;
                        double eta = (frac > 0.001) ? now * (1.0 - frac) / frac : 0;
                        char el[32], et[32];
                        fmt_time(now, el, sizeof(el));
                        fmt_time(eta, et, sizeof(et));
                        int filled = (int)(frac * 30 + 0.5);
                        char bar[32];
                        for (int i = 0; i < 30; i++) bar[i] = (i < filled) ? '#' : '.';
                        bar[30] = '\0';
                        double rate = total_done / now / 1e6;
                        printf("\r  [%s] %5.1f%% | %s elapsed | ETA %s | %.1fM/s  ",
                               bar, 100.0 * frac, el, et, rate);
                        fflush(stdout);
                    }
                }
            }
        }

        /* Merge per-thread results */
        for (int t = 0; t < nthreads; t++) {
            g_wmin_sum += accs[t].wmin_sum;
            if (accs[t].max_wmin > g_max_wmin) g_max_wmin = accs[t].max_wmin;
            if (accs[t].max_deficit > g_max_deficit) g_max_deficit = accs[t].max_deficit;
            if (accs[t].max_stop > g_max_stop) g_max_stop = accs[t].max_stop;
            g_violations += accs[t].violations;
            g_dd_count += accs[t].dd_count;
            g_d_count += accs[t].d_count;
            for (int w = 1; w <= HIST_MAX; w++)
                global_hist[w] += accs[t].wmin_hist[w];
            merge_extremes(&global_extremes, &accs[t]);
        }

        processed += chunk_size;

        double mean_wmin = (double)g_wmin_sum / processed;
        double pdd = (g_d_count > 0) ? (double)g_dd_count / g_d_count : 0.0;
        fprintf(f_summary, "%ld,%d,%.4f,%d,%ld,%d,%.6f\n",
                (long)processed, g_max_wmin, mean_wmin,
                g_max_deficit, (long)g_violations, g_max_stop, pdd);
        fflush(f_summary);

        chunk_start = chunk_end + 1;
    }
    fclose(f_summary);

    double elapsed = toc();
    char el[32];
    fmt_time(elapsed, el, sizeof(el));
    printf("\r  Done! %ld numbers in %s (%.1fM/s)                        \n",
           (long)param_N, el, param_N / elapsed / 1e6);

    /* Histogram CSV */
    FILE *f_hist = fopen("deficit_swc_histogram.csv", "w");
    if (f_hist) {
        fprintf(f_hist, "W,count\n");
        for (int w = 1; w <= HIST_MAX; w++)
            if (global_hist[w] > 0)
                fprintf(f_hist, "%d,%ld\n", w, (long)global_hist[w]);
        fclose(f_hist);
        printf("  deficit_swc_histogram.csv written\n");
    }

    /* Extremes CSV (descending by W_min) */
    FILE *f_ext = fopen("deficit_swc_extremes.csv", "w");
    if (f_ext) {
        fprintf(f_ext, "n,W_min,max_deficit,stopping_time\n");
        int cnt = global_extremes.top_count;
        for (int i = cnt - 1; i >= 0; i--) {
            fprintf(f_ext, "%ld,%d,%d,%d\n",
                    (long)global_extremes.top_n[i],
                    global_extremes.top_wmin[i],
                    global_extremes.top_deficit[i],
                    global_extremes.top_stop[i]);
        }
        fclose(f_ext);
        printf("  deficit_swc_extremes.csv written\n");
    }

    /* Final summary */
    printf("\n  === Summary ===\n");
    printf("  N              = %ld\n", (long)param_N);
    printf("  Max W_min      = %d\n", g_max_wmin);
    printf("  Mean W_min     = %.4f\n", (double)g_wmin_sum / param_N);
    printf("  Max deficit    = %d\n", g_max_deficit);
    printf("  Violations     = %ld\n", (long)g_violations);
    printf("  Max stop time  = %d\n", g_max_stop);
    printf("  P(D|D)         = %.6f (%ld / %ld)\n",
           g_d_count > 0 ? (double)g_dd_count / g_d_count : 0.0,
           (long)g_dd_count, (long)g_d_count);
    printf("  deficit_swc_summary.csv written\n");

    free(accs);
    return 0;
}
