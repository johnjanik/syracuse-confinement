/* exp_tilt_law.c — Experiment B: empirical Cramer-tilt law on critical excursions.
 *
 * Pre-registered (spec Section "Experiment B"): the bulk valuation law of
 * critical excursions converges to p^(1)_b = 3*4^{-b}, with entropy-per-digit
 * approaching H_2(3/4) = 0.811278... Boundary-layer tests (first/middle/last r)
 * separate genuine bulk behavior from edge effects.
 */
#include "experiments.h"
#include "critical_events.h"
#include "entropy_stats.h"
#include "io_csv.h"
#include <stdio.h>
#include <string.h>
#include <math.h>

static const int R_VALUES[] = {4, 8, 16, 32};

static void fill_vstat(vstat_t *v, const uint16_t *b, size_t from, size_t to) {
    vstat_reset(v);
    for (size_t i = from; i < to; i++) vstat_add(v, b[i]);
}

static void emit_row(FILE *f, uint64_t eid, uint64_t seed, int N, int A,
                     const char *seg, int r, const vstat_t *v) {
    ldbl tail5 = 0.0L;
    for (int b = 5; b <= ES_BMAX; b++) tail5 += es_phat(v, b);
    fprintf(f, "%llu,%llu,%d,%d,%s,%d,%llu,%.6Lf,%.6Lf,%.6Lf,%.6Lf,%.6Lf,"
               "%.6Lf,%.6Lf,%.6Lf,%.6Lf,%.6Lf\n",
        (unsigned long long)eid, (unsigned long long)seed, N, A, seg, r,
        (unsigned long long)v->total,
        es_phat(v,1), es_phat(v,2), es_phat(v,3), es_phat(v,4), tail5,
        es_kl_annealed(v), es_kl_critical(v),
        es_entropy(v), es_mean_b(v), es_entropy_per_digit(v));
}

static int octave_of(uint64_t s) { int N = 0; while (s >>= 1) N++; return N; }

int exp_tilt_law(const config_t *c, int argc, char **argv) {
    char path[512];
    snprintf(path, sizeof path, "%s/tilt_law.csv", c->output_dir);
    FILE *f = csv_open(path, "tilt_law",
        "event_id,seed,N,A,segment_type,r,length,p1_hat,p2_hat,p3_hat,p4_hat,"
        "tail_b_ge_5,KL_to_p,KL_to_p1,entropy,mean_b,entropy_per_digit",
        argc, argv);
    if (!f) { perror("csv_open"); return 1; }

    uint64_t eid = 0, n_events = 0;

    /* seed selection: explicit range, else octave sweep (sampled). */
    uint64_t lo, hi, step;
    if (c->end >= c->start && c->end > 1) {
        lo = c->start | 1u; hi = c->end + 1; step = 2;
    } else {
        int N = c->octave_min;
        lo = ((uint64_t)1 << N) | 1u;
        hi = (N + 1 >= 64) ? ~(uint64_t)0 : ((uint64_t)1 << (N + 1));
        uint64_t odds = (hi - lo) / 2 + 1;
        step = 2;
        if (c->seeds_per_octave && odds > c->seeds_per_octave)
            step = 2 * (odds / c->seeds_per_octave);
    }

    for (uint64_t s = lo; s < hi; s += step) {
        orbit_data_t d;
        if (orbit_run_record(s, c, &d) != 0) continue;
        int N = octave_of(s);

        for (size_t ei = 0; ei < d.nev; ei++) {
            crit_event_t *e = &d.ev[ei];
            /* minimal aperture for which this excursion is critical */
            int Amin = -1;
            for (int a = 0; a < c->n_apertures; a++)
                if (e->critical_A[a]) { Amin = c->apertures[a]; break; }
            if (Amin < 0) continue;     /* not critical for any aperture */

            size_t from = e->start_step, to = e->end_step;
            if (to > d.len) to = d.len;
            size_t L = to - from;
            if (L == 0) continue;
            eid++; n_events++;

            vstat_t v;
            fill_vstat(&v, d.b, from, to);
            emit_row(f, eid, s, N, Amin, "full", 0, &v);

            for (size_t ri = 0; ri < sizeof R_VALUES/sizeof R_VALUES[0]; ri++) {
                int r = R_VALUES[ri];
                if (L < (size_t)(2 * r + 1)) continue;  /* need room for all 3 */
                fill_vstat(&v, d.b, from, from + (size_t)r);
                emit_row(f, eid, s, N, Amin, "first", r, &v);
                fill_vstat(&v, d.b, from + (size_t)r, to - (size_t)r);
                emit_row(f, eid, s, N, Amin, "middle", r, &v);
                fill_vstat(&v, d.b, to - (size_t)r, to);
                emit_row(f, eid, s, N, Amin, "last", r, &v);
            }
        }
        orbit_data_free(&d);
    }
    fclose(f);
    fprintf(stderr, "[tilt-law] %llu critical excursions processed; wrote %s\n",
            (unsigned long long)n_events, path);
    return 0;
}
