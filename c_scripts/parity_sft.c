/*
 * parity_sft.c
 *
 * Parity Sequence Transition Matrices & Subshift of Finite Type
 * for Collatz trajectories.  C port of parity_sft.py for performance.
 *
 * For Collatz trajectories n -> 1, define the parity sequence
 *   sigma(n) = (s0, s1, s2, ...) where si = 0 (even) or 1 (odd step).
 *
 * Computes:
 *   1. Order-m transition matrices P(st | st-1,...,st-m) for m = 1..5
 *   2. Autocorrelation C(k) of the parity process
 *   3. Simulated autocorrelation from each order-m Markov model
 *   4. Identifies forbidden words -> subshift of finite type
 *   5. Determines the SFT transition matrix and spectral properties
 *
 * Usage: ./parity_sft [N]   (default N = 1000000)
 *
 * Compile: gcc -O3 -march=native -o parity_sft parity_sft.c -lm
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

#define MAX_ORDER   5
#define MAX_LAG     20
#define N_SIM       500000
#define MAX_GRAM    (MAX_ORDER + 1)      /* 6 */
#define MAX_STATES  (1 << MAX_ORDER)     /* 32 */
#define MAX_BINS    (1 << MAX_GRAM)      /* 64 */

/* ── Global data ────────────────────────────────────────────────────── */

static int      N;
static int      n_trajs;
static int64_t  total_steps;
static double   p_odd;                   /* global P(sigma = 1) */

static int8_t   *all_parities;
static int32_t  *seq_lengths;
static int64_t  *seq_starts;

/* n-gram counts: ngram_counts[m][value] for m in [1..MAX_GRAM] */
static int64_t  ngram_counts[MAX_GRAM + 1][MAX_BINS];

/* Transition data per Markov order m in [1..MAX_ORDER] */
static int64_t  raw_cnt[MAX_ORDER + 1][MAX_STATES][2];
static double   T_prob[MAX_ORDER + 1][MAX_STATES][2];
static double   M_trans[MAX_ORDER + 1][MAX_STATES][MAX_STATES];
static double   pi_stat[MAX_ORDER + 1][MAX_STATES];

/* Autocorrelation arrays */
static double   C_emp[MAX_LAG + 1];
static double   C_exact[MAX_ORDER + 1][MAX_LAG + 1];
static double   C_sim[MAX_ORDER + 1][MAX_LAG + 1];

/* Entropy storage */
static double   h_top_arr[MAX_ORDER + 1];
static double   h_meas_arr[MAX_ORDER + 1];

/* ── Timer utility ──────────────────────────────────────────────────── */

static struct timespec _ts;
static void tic(void) { clock_gettime(CLOCK_MONOTONIC, &_ts); }
static double toc(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (now.tv_sec - _ts.tv_sec) + 1e-9 * (now.tv_nsec - _ts.tv_nsec);
}

/* ── Binary string utility ──────────────────────────────────────────── */

static void to_binstr(char *buf, int val, int width)
{
    for (int i = 0; i < width; i++)
        buf[i] = ((val >> (width - 1 - i)) & 1) ? '1' : '0';
    buf[width] = '\0';
}

/* Check whether a value of given bit-width contains "11" */
static int has_11(int val)
{
    return (val & (val >> 1)) != 0;
}

/* ═══════════════════════════════════════════════════════════════════════
 * Eigenvalue solver  (Householder Hessenberg + shifted QR iteration)
 * For real nonsymmetric matrices up to MAX_STATES × MAX_STATES.
 * ═══════════════════════════════════════════════════════════════════════ */

static void hessenberg_reduce(double *A, int n, int stride)
{
    double v[MAX_STATES];

    for (int k = 0; k < n - 2; k++) {
        int len = n - k - 1;

        /* Compute norm of sub-column A[k+1..n-1, k] */
        double norm2 = 0;
        for (int i = 0; i < len; i++) {
            double x = A[(k + 1 + i) * stride + k];
            v[i] = x;
            norm2 += x * x;
        }
        double norm = sqrt(norm2);
        if (norm < 1e-300) continue;

        /* Householder vector */
        if (v[0] >= 0) v[0] += norm; else v[0] -= norm;

        double vTv = 0;
        for (int i = 0; i < len; i++) vTv += v[i] * v[i];
        if (vTv < 1e-300) continue;
        double beta = 2.0 / vTv;

        /* Apply from left: A = (I - beta*v*v^T) * A  (rows k+1..n-1) */
        for (int j = 0; j < n; j++) {
            double dot = 0;
            for (int i = 0; i < len; i++)
                dot += v[i] * A[(k + 1 + i) * stride + j];
            dot *= beta;
            for (int i = 0; i < len; i++)
                A[(k + 1 + i) * stride + j] -= v[i] * dot;
        }

        /* Apply from right: A = A * (I - beta*v*v^T)  (cols k+1..n-1) */
        for (int row = 0; row < n; row++) {
            double dot = 0;
            for (int j = 0; j < len; j++)
                dot += A[row * stride + (k + 1 + j)] * v[j];
            dot *= beta;
            for (int j = 0; j < len; j++)
                A[row * stride + (k + 1 + j)] -= dot * v[j];
        }
    }
}

/*
 * Extract eigenvalues from upper Hessenberg matrix via explicit shifted
 * QR using Givens rotations.  Stores results in wr[] (real) and wi[] (imag).
 */
static void hess_qr_eig(double *H, int n, int stride, double *wr, double *wi)
{
    /* Work on a compact n×n copy */
    double A[MAX_STATES * MAX_STATES];
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
            A[i * n + j] = H[i * stride + j];

    int p = n;                 /* active block is [0..p-1] */
    int max_iter = 60 * n;
    int iter = 0;
    double cs[MAX_STATES], sn[MAX_STATES];

    while (p > 2 && iter < max_iter) {
        /* Check convergence at bottom */
        double s = fabs(A[(p - 2) * n + p - 2]) + fabs(A[(p - 1) * n + p - 1]);
        if (s == 0.0) s = 1.0;

        if (fabs(A[(p - 1) * n + p - 2]) < 1e-14 * s) {
            wr[p - 1] = A[(p - 1) * n + p - 1];
            wi[p - 1] = 0.0;
            p--;
            continue;
        }

        /* Check 2×2 block convergence */
        if (p >= 3) {
            double s2 = fabs(A[(p - 3) * n + p - 3]) + fabs(A[(p - 2) * n + p - 2]);
            if (s2 == 0.0) s2 = 1.0;
            if (fabs(A[(p - 2) * n + p - 3]) < 1e-14 * s2) {
                double a = A[(p-2)*n+p-2], b = A[(p-2)*n+p-1];
                double c = A[(p-1)*n+p-2], d = A[(p-1)*n+p-1];
                double tr = a + d, det = a * d - b * c;
                double disc = tr * tr - 4 * det;
                if (disc >= 0) {
                    wr[p-1] = (tr + sqrt(disc)) / 2;
                    wr[p-2] = (tr - sqrt(disc)) / 2;
                    wi[p-1] = wi[p-2] = 0;
                } else {
                    wr[p-1] = wr[p-2] = tr / 2;
                    wi[p-1] = sqrt(-disc) / 2;
                    wi[p-2] = -sqrt(-disc) / 2;
                }
                p -= 2;
                continue;
            }
        }

        /* Wilkinson shift from trailing 2×2 block */
        double a = A[(p-2)*n+p-2], b = A[(p-2)*n+p-1];
        double c = A[(p-1)*n+p-2], d = A[(p-1)*n+p-1];
        double tr = a + d, det = a * d - b * c;
        double disc = tr * tr - 4 * det;
        double shift;
        if (disc >= 0) {
            double e1 = (tr + sqrt(disc)) / 2;
            double e2 = (tr - sqrt(disc)) / 2;
            shift = (fabs(e1 - d) < fabs(e2 - d)) ? e1 : e2;
        } else {
            shift = d;
        }

        /* Exceptional shift every 10 iterations */
        if (iter > 0 && iter % 10 == 0) {
            shift = fabs(A[(p-1)*n+p-2]) + fabs(A[(p-2)*n+p-3]);
        }

        /* Shift */
        for (int i = 0; i < p; i++) A[i * n + i] -= shift;

        /* QR factorization via Givens rotations */
        for (int i = 0; i < p - 1; i++) {
            double x = A[i * n + i], y = A[(i + 1) * n + i];
            double r = hypot(x, y);
            if (r < 1e-300) { cs[i] = 1; sn[i] = 0; continue; }
            cs[i] = x / r;
            sn[i] = y / r;
            for (int j = i; j < p; j++) {
                double t1 = A[i * n + j], t2 = A[(i + 1) * n + j];
                A[i * n + j]       =  cs[i] * t1 + sn[i] * t2;
                A[(i + 1) * n + j] = -sn[i] * t1 + cs[i] * t2;
            }
        }

        /* RQ: apply Givens^T from right */
        for (int i = 0; i < p - 1; i++) {
            int jmax = (i + 2 < p) ? i + 2 : p;
            for (int j = 0; j < jmax; j++) {
                double t1 = A[j * n + i], t2 = A[j * n + i + 1];
                A[j * n + i]     =  cs[i] * t1 + sn[i] * t2;
                A[j * n + i + 1] = -sn[i] * t1 + cs[i] * t2;
            }
        }

        /* Unshift */
        for (int i = 0; i < p; i++) A[i * n + i] += shift;

        iter++;
    }

    /* Handle remaining 1×1 or 2×2 block */
    if (p == 2) {
        double a = A[0], b = A[1], c = A[n], d = A[n + 1];
        double tr = a + d, det = a * d - b * c;
        double disc = tr * tr - 4 * det;
        if (disc >= 0) {
            wr[1] = (tr + sqrt(disc)) / 2;
            wr[0] = (tr - sqrt(disc)) / 2;
            wi[0] = wi[1] = 0;
        } else {
            wr[0] = wr[1] = tr / 2;
            wi[1] = sqrt(-disc) / 2;
            wi[0] = -sqrt(-disc) / 2;
        }
    } else if (p == 1) {
        wr[0] = A[0];
        wi[0] = 0;
    } else if (p > 2) {
        /* QR didn't fully converge; read diagonal */
        for (int i = 0; i < p; i++) { wr[i] = A[i * n + i]; wi[i] = 0; }
    }
}

/*
 * Compute all eigenvalues of an n×n matrix (row-major, stride = n).
 * Returns eigenvalues sorted by descending magnitude.
 */
typedef struct { double re, im, mag; } eigen_t;

static int eigen_cmp_desc(const void *a, const void *b) {
    double da = ((const eigen_t *)a)->mag;
    double db = ((const eigen_t *)b)->mag;
    return (da < db) - (da > db);
}

static void compute_eigenvalues(const double *A_in, int n,
                                double *wr, double *wi)
{
    double A[MAX_STATES * MAX_STATES];
    memcpy(A, A_in, n * n * sizeof(double));
    hessenberg_reduce(A, n, n);
    hess_qr_eig(A, n, n, wr, wi);

    /* Sort by descending magnitude */
    eigen_t ev[MAX_STATES];
    for (int i = 0; i < n; i++) {
        ev[i].re  = wr[i];
        ev[i].im  = wi[i];
        ev[i].mag = hypot(wr[i], wi[i]);
    }
    qsort(ev, n, sizeof(eigen_t), eigen_cmp_desc);
    for (int i = 0; i < n; i++) {
        wr[i] = ev[i].re;
        wi[i] = ev[i].im;
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * Small matrix utilities
 * ═══════════════════════════════════════════════════════════════════════ */

static void mat_mul(const double *A, const double *B, double *C, int n)
{
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++) {
            double s = 0;
            for (int k = 0; k < n; k++)
                s += A[i * n + k] * B[k * n + j];
            C[i * n + j] = s;
        }
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 1: Generate parity sequences
 * ═══════════════════════════════════════════════════════════════════════ */

static void generate_trajectories(void)
{
    printf("Generating parity sequences for n in [2, %d]...\n", N);
    tic();

    int64_t alloc = (int64_t)(N - 1) * 120;  /* generous estimate */
    all_parities = (int8_t *)malloc(alloc);
    seq_lengths  = (int32_t *)malloc((size_t)(N - 1) * sizeof(int32_t));

    if (!all_parities || !seq_lengths) {
        fprintf(stderr, "Memory allocation failed\n");
        exit(1);
    }

    int8_t *p = all_parities;

    for (int n = 2; n <= N; n++) {
        int8_t *start = p;
        uint64_t x = (uint64_t)n;

        while (x != 1) {
            /* Grow buffer if needed */
            if (p - all_parities >= alloc - 1000) {
                int64_t offset = p - all_parities;
                int64_t soff   = start - all_parities;
                alloc *= 2;
                all_parities = (int8_t *)realloc(all_parities, alloc);
                if (!all_parities) { fprintf(stderr, "realloc failed\n"); exit(1); }
                p     = all_parities + offset;
                start = all_parities + soff;
            }
            if (x & 1) {
                *p++ = 1;
                x = 3 * x + 1;
            } else {
                *p++ = 0;
                x >>= 1;
            }
        }
        seq_lengths[n - 2] = (int32_t)(p - start);
    }

    total_steps = p - all_parities;
    n_trajs     = N - 1;

    /* Compute seq_starts (cumulative) */
    seq_starts = (int64_t *)malloc((n_trajs + 1) * sizeof(int64_t));
    seq_starts[0] = 0;
    for (int i = 0; i < n_trajs; i++)
        seq_starts[i + 1] = seq_starts[i] + seq_lengths[i];

    /* Compute p_odd */
    int64_t ones = 0;
    for (int64_t i = 0; i < total_steps; i++) ones += all_parities[i];
    p_odd = (double)ones / total_steps;

    double dt = toc();
    double mean_len = (double)total_steps / n_trajs;
    printf("  Done in %.1fs.\n", dt);
    printf("  Total parity symbols: %'ld\n", (long)total_steps);
    printf("  Mean trajectory length: %.1f\n", mean_len);
    printf("  P(sigma=1) = %.6f  (odd step frequency)\n", p_odd);
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 2: Count m-grams
 * ═══════════════════════════════════════════════════════════════════════ */

static void count_ngrams_all(void)
{
    printf("\nCounting m-grams (m = 1..%d)...\n", MAX_ORDER + 1);
    tic();

    memset(ngram_counts, 0, sizeof(ngram_counts));

    for (int t = 0; t < n_trajs; t++) {
        int64_t start = seq_starts[t];
        int L = seq_lengths[t];
        const int8_t *seq = all_parities + start;

        for (int m = 1; m <= MAX_GRAM && m <= L; m++) {
            int mask = (1 << m) - 1;

            /* Build initial window value */
            int val = 0;
            for (int k = 0; k < m; k++)
                val = (val << 1) | seq[k];
            ngram_counts[m][val]++;

            /* Slide window */
            for (int j = 1; j <= L - m; j++) {
                val = ((val << 1) | seq[j + m - 1]) & mask;
                ngram_counts[m][val]++;
            }
        }
    }

    printf("  Done in %.1fs.\n", toc());
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 3: Build transition matrices
 * ═══════════════════════════════════════════════════════════════════════ */

static void build_transitions(void)
{
    printf("\n========================================================================\n");
    printf("ORDER-m TRANSITION MATRICES\n");
    printf("========================================================================\n");

    for (int m = 1; m <= MAX_ORDER; m++) {
        int ns = 1 << m;
        char buf[MAX_GRAM + 2];

        /* Fill raw counts from (m+1)-gram counts */
        for (int ctx = 0; ctx < ns; ctx++)
            for (int sigma = 0; sigma <= 1; sigma++)
                raw_cnt[m][ctx][sigma] = ngram_counts[m + 1][ctx * 2 + sigma];

        /* Normalise -> T_prob; build state-to-state M_trans */
        memset(M_trans[m], 0, sizeof(M_trans[m]));

        for (int i = 0; i < ns; i++) {
            int64_t row_sum = raw_cnt[m][i][0] + raw_cnt[m][i][1];
            for (int sigma = 0; sigma <= 1; sigma++) {
                T_prob[m][i][sigma] = (row_sum > 0)
                    ? (double)raw_cnt[m][i][sigma] / row_sum
                    : 0.0;
                int j = ((i & ((1 << (m - 1)) - 1)) << 1) | sigma;
                M_trans[m][i][j] = T_prob[m][i][sigma];
            }
        }

        /* ── Stationary distribution via power iteration ── */
        {
            double pi[MAX_STATES], pi_next[MAX_STATES];
            for (int i = 0; i < ns; i++) pi[i] = 1.0 / ns;

            for (int it = 0; it < 2000; it++) {
                memset(pi_next, 0, ns * sizeof(double));
                for (int i = 0; i < ns; i++)
                    for (int j = 0; j < ns; j++)
                        pi_next[j] += pi[i] * M_trans[m][i][j];
                double sum = 0;
                for (int i = 0; i < ns; i++) sum += pi_next[i];
                if (sum > 0)
                    for (int i = 0; i < ns; i++) pi_next[i] /= sum;
                memcpy(pi, pi_next, ns * sizeof(double));
            }

            for (int i = 0; i < ns; i++) pi_stat[m][i] = pi[i];
        }

        /* ── Print section ── */
        printf("\n-- Order m = %d  (%d states) --\n", m, ns);

        /* Forbidden / unreachable */
        int any_forbidden = 0;
        for (int i = 0; i < ns; i++) {
            int64_t ctx_count = raw_cnt[m][i][0] + raw_cnt[m][i][1];
            if (ctx_count == 0) {
                if (!any_forbidden) { printf("  Forbidden/unreachable:\n"); any_forbidden = 1; }
                to_binstr(buf, i, m);
                if (ngram_counts[m][i] == 0)
                    printf("    Context '%s' never appears (unreachable state)\n", buf);
            } else {
                for (int sigma = 0; sigma <= 1; sigma++) {
                    if (raw_cnt[m][i][sigma] == 0) {
                        if (!any_forbidden) { printf("  Forbidden/unreachable:\n"); any_forbidden = 1; }
                        to_binstr(buf, i, m);
                        printf("    '%s' -> %d  (forbidden transition)\n", buf, sigma);
                    }
                }
            }
        }

        /* Transition table for small orders */
        if (m <= 3) {
            printf("\n  %10s    %8s  %8s  %10s\n", "Context", "P(->0)", "P(->1)", "Count");
            printf("  ---------------------------------------------\n");
            for (int i = 0; i < ns; i++) {
                int64_t count = raw_cnt[m][i][0] + raw_cnt[m][i][1];
                if (count > 0) {
                    to_binstr(buf, i, m);
                    printf("  %10s    %8.5f  %8.5f  %10ld\n",
                           buf, T_prob[m][i][0], T_prob[m][i][1], (long)count);
                }
            }
        }

        /* ── Eigenvalues of M ── */
        {
            /* Flatten M_trans[m] into contiguous n×n array */
            double M_flat[MAX_STATES * MAX_STATES];
            for (int i = 0; i < ns; i++)
                for (int j = 0; j < ns; j++)
                    M_flat[i * ns + j] = M_trans[m][i][j];

            double wr[MAX_STATES], wi[MAX_STATES];
            compute_eigenvalues(M_flat, ns, wr, wi);

            printf("\n  Top eigenvalues of M:\n");
            int show = (ns < 6) ? ns : 6;
            for (int k = 0; k < show; k++) {
                double mag = hypot(wr[k], wi[k]);
                printf("    lambda_%d = %+.6f %+.6fi  (|lambda| = %.6f)\n",
                       k, wr[k], wi[k], mag);
            }
        }

        /* ── Topological entropy = log2(spectral radius of adjacency) ── */
        {
            double A_adj[MAX_STATES * MAX_STATES];
            for (int i = 0; i < ns; i++)
                for (int j = 0; j < ns; j++)
                    A_adj[i * ns + j] = (M_trans[m][i][j] > 0) ? 1.0 : 0.0;

            double wr[MAX_STATES], wi[MAX_STATES];
            compute_eigenvalues(A_adj, ns, wr, wi);

            double rho = hypot(wr[0], wi[0]);
            double h_top = log2(rho);
            h_top_arr[m] = h_top;

            printf("\n  Adjacency matrix spectral radius: %.6f\n", rho);
            printf("  Topological entropy: h_top = log2(rho) = %.6f bits/step\n", h_top);
        }

        /* ── Measure entropy = -Sum pi_i Sum_j M_ij log2(M_ij) ── */
        {
            double h_meas = 0;
            for (int i = 0; i < ns; i++) {
                if (pi_stat[m][i] <= 0) continue;
                for (int j = 0; j < ns; j++) {
                    if (M_trans[m][i][j] > 0)
                        h_meas -= pi_stat[m][i] * M_trans[m][i][j]
                                  * log2(M_trans[m][i][j]);
                }
            }
            h_meas_arr[m] = h_meas;
            printf("  Measure-theoretic entropy: h_mu = %.6f bits/step\n", h_meas);
        }
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 4: Empirical autocorrelation
 * ═══════════════════════════════════════════════════════════════════════ */

static void compute_empirical_autocorr(void)
{
    printf("\n========================================================================\n");
    printf("AUTOCORRELATION OF PARITY PROCESS\n");
    printf("========================================================================\n");
    printf("Computing empirical autocorrelation...\n");
    tic();

    double sum_xy[MAX_LAG + 1];
    int64_t count[MAX_LAG + 1];
    memset(sum_xy, 0, sizeof(sum_xy));
    memset(count, 0, sizeof(count));

    C_emp[0] = 1.0;

    for (int t = 0; t < n_trajs; t++) {
        int64_t start = seq_starts[t];
        int L = seq_lengths[t];
        const int8_t *seq = all_parities + start;

        for (int k = 1; k <= MAX_LAG && k < L; k++) {
            double s = 0;
            int pairs = L - k;
            for (int j = 0; j < pairs; j++)
                s += (double)(seq[j] & seq[j + k]);
            sum_xy[k] += s;
            count[k]  += pairs;
        }
    }

    double var = p_odd * (1.0 - p_odd);
    for (int k = 1; k <= MAX_LAG; k++) {
        if (count[k] > 0 && var > 0) {
            double E_xy = sum_xy[k] / count[k];
            C_emp[k] = (E_xy - p_odd * p_odd) / var;
        }
    }

    printf("  Done in %.1fs.\n", toc());
    printf("\n  %6s  %10s\n", "Lag k", "C(k)");
    printf("  --------------------\n");
    for (int k = 0; k <= MAX_LAG; k++) {
        const char *marker = (k >= 1 && k <= 5 && fabs(C_emp[k]) > 0.01)
                             ? "  <" : "";
        printf("  %6d  %10.6f%s\n", k, C_emp[k], marker);
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 5: Markov model autocorrelation (simulated + exact)
 * ═══════════════════════════════════════════════════════════════════════ */

static void simulate_markov_autocorr_one(int m)
{
    int ns = 1 << m;

    srand48(42 + m);

    int *state_seq = (int *)malloc(N_SIM * sizeof(int));

    /* Sample initial state from stationary distribution */
    double r = drand48();
    double cum = 0;
    state_seq[0] = 0;
    for (int i = 0; i < ns; i++) {
        cum += pi_stat[m][i];
        if (r < cum) { state_seq[0] = i; break; }
    }

    /* Generate chain */
    for (int t = 1; t < N_SIM; t++) {
        int s = state_seq[t - 1];
        r = drand48();
        cum = 0;
        int next = 0;
        for (int j = 0; j < ns; j++) {
            cum += M_trans[m][s][j];
            if (r < cum) { next = j; break; }
        }
        /* Fallback if stuck in absorbing state */
        if (cum < 1e-10) {
            r = drand48(); cum = 0;
            for (int j = 0; j < ns; j++) {
                cum += pi_stat[m][j];
                if (r < cum) { next = j; break; }
            }
        }
        state_seq[t] = next;
    }

    /* Extract parities and compute autocorrelation */
    double *par = (double *)malloc(N_SIM * sizeof(double));
    double pmean = 0;
    for (int t = 0; t < N_SIM; t++) {
        par[t] = (double)(state_seq[t] & 1);
        pmean += par[t];
    }
    pmean /= N_SIM;
    double var = pmean * (1.0 - pmean);

    C_sim[m][0] = 1.0;
    for (int k = 1; k <= MAX_LAG; k++) {
        double s = 0;
        for (int t = 0; t < N_SIM - k; t++)
            s += par[t] * par[t + k];
        s /= (N_SIM - k);
        C_sim[m][k] = (var > 0) ? (s - pmean * pmean) / var : 0;
    }

    free(par);
    free(state_seq);
}

static void compute_exact_autocorr_one(int m)
{
    int ns = 1 << m;

    /* f[state] = last bit */
    double f[MAX_STATES];
    for (int i = 0; i < ns; i++) f[i] = (double)(i & 1);

    double mu = 0;
    for (int i = 0; i < ns; i++) mu += pi_stat[m][i] * f[i];
    double var = -mu * mu;
    for (int i = 0; i < ns; i++) var += pi_stat[m][i] * f[i] * f[i];

    C_exact[m][0] = 1.0;

    /* Flatten M */
    double Mf[MAX_STATES * MAX_STATES];
    for (int i = 0; i < ns; i++)
        for (int j = 0; j < ns; j++)
            Mf[i * ns + j] = M_trans[m][i][j];

    /* M^k by repeated multiplication */
    double Mk[MAX_STATES * MAX_STATES];
    double Mk_next[MAX_STATES * MAX_STATES];

    /* Mk = I */
    memset(Mk, 0, sizeof(Mk));
    for (int i = 0; i < ns; i++) Mk[i * ns + i] = 1.0;

    for (int lag = 1; lag <= MAX_LAG; lag++) {
        mat_mul(Mk, Mf, Mk_next, ns);
        memcpy(Mk, Mk_next, ns * ns * sizeof(double));

        /* E[f(Xt) f(Xt+k)] = sum_i pi[i]*f[i] * sum_j Mk[i][j]*f[j] */
        double E_ff = 0;
        for (int i = 0; i < ns; i++) {
            if (pi_stat[m][i] <= 0) continue;
            double Mkf = 0;
            for (int j = 0; j < ns; j++)
                Mkf += Mk[i * ns + j] * f[j];
            E_ff += pi_stat[m][i] * f[i] * Mkf;
        }
        C_exact[m][lag] = (var > 0) ? (E_ff - mu * mu) / var : 0;
    }
}

static void compute_markov_autocorr(void)
{
    printf("\n========================================================================\n");
    printf("MARKOV MODEL AUTOCORRELATION COMPARISON\n");
    printf("========================================================================\n");

    for (int m = 1; m <= MAX_ORDER; m++) {
        printf("  Simulating order-%d Markov chain...\n", m);
        simulate_markov_autocorr_one(m);
    }

    for (int m = 1; m <= MAX_ORDER; m++)
        compute_exact_autocorr_one(m);

    /* Print comparison table */
    printf("\n  %4s  %10s", "Lag", "Empirical");
    for (int m = 1; m <= MAX_ORDER; m++)
        printf("  %7s%d%2s", "m=", m, " exact");
    printf("\n  ----------------------------------------------------------------------\n");

    for (int k = 0; k <= MAX_LAG; k++) {
        printf("  %4d  %10.6f", k, C_emp[k]);
        for (int m = 1; m <= MAX_ORDER; m++)
            printf("  %10.6f", C_exact[m][k]);
        printf("\n");
    }

    /* Residuals */
    printf("\n  Residual |C_emp(k) - C_model(k)| summed over k=1..%d:\n", MAX_LAG);
    for (int m = 1; m <= MAX_ORDER; m++) {
        double sum_res = 0, max_res = 0;
        for (int k = 1; k <= MAX_LAG; k++) {
            double d = fabs(C_emp[k] - C_exact[m][k]);
            sum_res += d;
            if (d > max_res) max_res = d;
        }
        printf("    Order %d: Sum|dC| = %.6f,  max|dC| = %.6f\n",
               m, sum_res, max_res);
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 6: SFT analysis
 * ═══════════════════════════════════════════════════════════════════════ */

static void sft_analysis(void)
{
    printf("\n========================================================================\n");
    printf("SUBSHIFT OF FINITE TYPE ANALYSIS\n");
    printf("========================================================================\n");

    char buf[MAX_GRAM + 2];

    for (int m = 1; m <= MAX_ORDER; m++) {
        int ns = 1 << m;
        int wlen = m + 1;

        printf("\n  Order m = %d:\n", m);

        /* Forbidden (m+1)-grams: context -> sigma with zero count */
        int n_forbidden = 0;
        for (int i = 0; i < ns; i++)
            for (int sigma = 0; sigma <= 1; sigma++)
                if (raw_cnt[m][i][sigma] == 0)
                    n_forbidden++;

        printf("    Forbidden (m+1)-grams: %d\n", n_forbidden);
        for (int i = 0; i < ns; i++)
            for (int sigma = 0; sigma <= 1; sigma++)
                if (raw_cnt[m][i][sigma] == 0) {
                    int word = i * 2 + sigma;
                    to_binstr(buf, word, wlen);
                    printf("      '%s'\n", buf);
                }

        /* Unreachable m-grams */
        int n_unreach = 0;
        for (int i = 0; i < ns; i++)
            if (raw_cnt[m][i][0] + raw_cnt[m][i][1] == 0 && ngram_counts[m][i] == 0)
                n_unreach++;
        if (n_unreach > 0) {
            printf("    Unreachable m-grams: %d\n", n_unreach);
            for (int i = 0; i < ns; i++)
                if (raw_cnt[m][i][0] + raw_cnt[m][i][1] == 0 && ngram_counts[m][i] == 0) {
                    to_binstr(buf, i, m);
                    printf("      '%s'\n", buf);
                }
        }

        /* Check non-trivial forbidden words */
        int has_nontrivial = 0;
        for (int i = 0; i < ns; i++)
            for (int sigma = 0; sigma <= 1; sigma++)
                if (raw_cnt[m][i][sigma] == 0) {
                    int word = i * 2 + sigma;
                    if (!has_11(word)) {
                        if (!has_nontrivial)
                            printf("    *** NON-TRIVIAL forbidden words (not containing '11'): ***\n");
                        has_nontrivial = 1;
                        to_binstr(buf, word, wlen);
                        printf("      '%s'\n", buf);
                    }
                }

        if (!has_nontrivial)
            printf("    All forbidden words contain '11' as substring -> "
                   "no new constraints beyond order 1.\n");
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * Step 7: Golden mean shift analysis
 * ═══════════════════════════════════════════════════════════════════════ */

static void golden_mean_analysis(void)
{
    printf("\n========================================================================\n");
    printf("THE ORDER-1 SUBSHIFT OF FINITE TYPE\n");
    printf("========================================================================\n");

    printf("\n  Transition matrix (2x2):\n");
    printf("    From \\ To      0            1\n");
    printf("    0          %.6f     %.6f\n", T_prob[1][0][0], T_prob[1][0][1]);
    printf("    1          %.6f     %.6f\n", T_prob[1][1][0], T_prob[1][1][1]);

    printf("\n  Adjacency matrix (0/1):\n");
    int A[2][2];
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < 2; j++)
            A[i][j] = (M_trans[1][i][j] > 0) ? 1 : 0;
    printf("    [[%d %d]\n     [%d %d]]\n", A[0][0], A[0][1], A[1][0], A[1][1]);

    printf("\n  Forbidden bigrams: '11'\n");
    printf("  Allowed bigrams: '00', '01', '10'\n");
    printf("  This is the GOLDEN MEAN SHIFT (the classical SFT forbidding '11').\n");

    double phi = (1.0 + sqrt(5.0)) / 2.0;
    double h_golden = log2(phi);
    printf("\n  Golden ratio: phi = %.6f\n", phi);
    printf("  Topological entropy: log2(phi) = %.6f bits/step\n", h_golden);

    printf("\n  Empirical P(sigma=1) = %.6f\n", p_odd);
    printf("  SFT stationary P(sigma=1) = %.6f\n", pi_stat[1][1]);
    printf("  Maximal entropy (Parry measure) P(sigma=1) = 1/phi = %.6f\n", 1.0 / phi);

    printf("\n  The Collatz parity process is a SOFIC MEASURE on the golden mean shift.\n");
    printf("  It is NOT the Parry (maximal entropy) measure because:\n");
    printf("    P(1|0) = %.6f != 1/phi = %.6f\n", T_prob[1][0][1], 1.0 / phi);
}

/* ═══════════════════════════════════════════════════════════════════════
 * Data file output (for companion plotting script)
 * ═══════════════════════════════════════════════════════════════════════ */

static void write_data_files(void)
{
    printf("\n========================================================================\n");
    printf("WRITING DATA FILES\n");
    printf("========================================================================\n");

    /* Autocorrelation data */
    {
        FILE *f = fopen("parity_autocorr.csv", "w");
        if (!f) { perror("parity_autocorr.csv"); return; }
        fprintf(f, "lag,C_emp");
        for (int m = 1; m <= MAX_ORDER; m++) fprintf(f, ",C_exact_%d", m);
        for (int m = 1; m <= MAX_ORDER; m++) fprintf(f, ",C_sim_%d", m);
        fprintf(f, "\n");
        for (int k = 0; k <= MAX_LAG; k++) {
            fprintf(f, "%d,%.9f", k, C_emp[k]);
            for (int m = 1; m <= MAX_ORDER; m++) fprintf(f, ",%.9f", C_exact[m][k]);
            for (int m = 1; m <= MAX_ORDER; m++) fprintf(f, ",%.9f", C_sim[m][k]);
            fprintf(f, "\n");
        }
        fclose(f);
        printf("  Saved parity_autocorr.csv\n");
    }

    /* Entropy data */
    {
        FILE *f = fopen("parity_entropy.csv", "w");
        if (!f) { perror("parity_entropy.csv"); return; }
        fprintf(f, "order,h_top,h_meas\n");
        for (int m = 1; m <= MAX_ORDER; m++)
            fprintf(f, "%d,%.9f,%.9f\n", m, h_top_arr[m], h_meas_arr[m]);
        fclose(f);
        printf("  Saved parity_entropy.csv\n");
    }

    /* Transition matrices */
    for (int m = 1; m <= MAX_ORDER; m++) {
        char fname[64];
        snprintf(fname, sizeof(fname), "parity_matrix_m%d.csv", m);
        FILE *f = fopen(fname, "w");
        if (!f) { perror(fname); continue; }
        int ns = 1 << m;
        for (int i = 0; i < ns; i++) {
            for (int j = 0; j < ns; j++) {
                if (j > 0) fprintf(f, ",");
                fprintf(f, "%.9f", M_trans[m][i][j]);
            }
            fprintf(f, "\n");
        }
        fclose(f);
        printf("  Saved %s\n", fname);
    }

    /* Parameters */
    {
        FILE *f = fopen("parity_params.csv", "w");
        if (!f) { perror("parity_params.csv"); return; }
        fprintf(f, "N,%d\n", N);
        fprintf(f, "total_steps,%ld\n", (long)total_steps);
        fprintf(f, "n_trajs,%d\n", n_trajs);
        fprintf(f, "p_odd,%.9f\n", p_odd);
        fprintf(f, "mean_traj_len,%.2f\n", (double)total_steps / n_trajs);
        fprintf(f, "T_1_00,%.9f\n", T_prob[1][0][0]);
        fprintf(f, "T_1_01,%.9f\n", T_prob[1][0][1]);
        fprintf(f, "T_1_10,%.9f\n", T_prob[1][1][0]);
        fprintf(f, "T_1_11,%.9f\n", T_prob[1][1][1]);
        fclose(f);
        printf("  Saved parity_params.csv\n");
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * main
 * ═══════════════════════════════════════════════════════════════════════ */

int main(int argc, char **argv)
{
    N = (argc > 1) ? atoi(argv[1]) : 1000000;
    if (N < 3) { fprintf(stderr, "N must be >= 3\n"); return 1; }

    struct timespec wall_start;
    clock_gettime(CLOCK_MONOTONIC, &wall_start);

    generate_trajectories();
    count_ngrams_all();
    build_transitions();
    compute_empirical_autocorr();
    compute_markov_autocorr();
    sft_analysis();
    golden_mean_analysis();
    write_data_files();

    struct timespec wall_end;
    clock_gettime(CLOCK_MONOTONIC, &wall_end);
    double wall = (wall_end.tv_sec - wall_start.tv_sec)
                + 1e-9 * (wall_end.tv_nsec - wall_start.tv_nsec);
    printf("\nTotal wall time: %.2fs\n", wall);

    /* Cleanup */
    free(all_parities);
    free(seq_lengths);
    free(seq_starts);

    return 0;
}
