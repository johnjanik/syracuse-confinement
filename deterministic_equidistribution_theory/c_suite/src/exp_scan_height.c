/* exp_scan_height.c — Experiment A: baseline orbit & height-tail census.
 *
 * Pre-registered (spec Section "Experiment A"):
 *   log2 Pr(h >= H) ~ -H + C          (height tail, slope -1 in base-2)
 *   #(C_A in [2^N, 2^{N+1})) = O_A(1)  (octave-uniform critical count)
 */
#include "experiments.h"
#include "critical_events.h"
#include "io_csv.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define HT_MAX 48   /* height-tail buckets H = 0 .. HT_MAX-1 */

static double now_sec(void) {
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

int exp_scan_height(const config_t *c, int argc, char **argv) {
    char path[512], cpath[512];
    snprintf(path,  sizeof path,  "%s/height_tail.csv", c->output_dir);
    snprintf(cpath, sizeof cpath, "%s/critical_events.csv", c->output_dir);

    /* build the height_tail header with HT_MAX tail columns */
    char hdr[2048];
    int p = snprintf(hdr, sizeof hdr,
        "N,seeds_tested,A,critical_count,max_height,mean_height");
    for (int H = 0; H < HT_MAX; H++)
        p += snprintf(hdr + p, sizeof hdr - (size_t)p, ",tail_count_H%d", H);
    p += snprintf(hdr + p, sizeof hdr - (size_t)p, ",runtime_seconds");

    FILE *f = csv_open(path, "height_tail", hdr, argc, argv);
    if (!f) { perror("csv_open"); return 1; }
    FILE *cf = csv_open(cpath, "critical_events",
        "seed,octave_N,A,launch_V,peak_P,exit_X,start_step,end_step,"
        "word_length,D,height_log2,amin_exact_num,amin_exact_den_power2,"
        "overshoot,status", argc, argv);
    if (!cf) { perror("csv_open"); fclose(f); return 1; }

    int nmin = c->octave_min, nmax = c->octave_max;
    if (nmax > 62) nmax = 62;   /* FAST128 seeds are u64: 2^{N+1} must fit */

    for (int N = nmin; N <= nmax; N++) {
        double t0 = now_sec();
        uint64_t lo = ((uint64_t)1 << N) | 1u;
        uint64_t hi = (N + 1 >= 64) ? ~(uint64_t)0 : ((uint64_t)1 << (N + 1));
        uint64_t odds = (hi - lo) / 2 + 1;
        uint64_t step = 2;
        if (c->seeds_per_octave && odds > c->seeds_per_octave)
            step = 2 * (odds / c->seeds_per_octave);

        uint64_t tested = 0;
        ldbl sum_h = 0.0L, max_h = 0.0L;
        uint64_t tail[HT_MAX]; memset(tail, 0, sizeof tail);
        uint64_t crit_count[CE_MAX_APERTURES]; memset(crit_count, 0, sizeof crit_count);

        for (uint64_t s = lo; s < hi; s += step) {
            orbit_data_t d;
            if (orbit_run_record(s, c, &d) != 0) continue;
            tested++;
            sum_h += d.max_height;
            if (d.max_height > max_h) max_h = d.max_height;
            for (int H = 0; H < HT_MAX; H++)
                if (d.max_height >= (ldbl)H) tail[H]++;

            for (size_t ei = 0; ei < d.nev; ei++) {
                crit_event_t *e = &d.ev[ei];
                int any = 0;
                for (int a = 0; a < c->n_apertures; a++)
                    if (e->critical_A[a]) { crit_count[a]++; any = 1; }
                if (any) {
                    /* write one row per aperture for which it is critical */
                    for (int a = 0; a < c->n_apertures; a++) {
                        if (!e->critical_A[a]) continue;
                        fprintf(cf, "%llu,%d,%d,%s,%s,%s,%llu,%llu,%llu,%llu,"
                                    "%.6Lf,0,0,0,%s\n",
                            (unsigned long long)s, N, c->apertures[a],
                            e->launch_dec, e->peak_dec, e->exit_dec,
                            (unsigned long long)e->start_step,
                            (unsigned long long)e->end_step,
                            (unsigned long long)e->word_length,
                            (unsigned long long)e->D, e->height_log2, e->status);
                    }
                }
            }
            orbit_data_free(&d);
        }
        double rt = now_sec() - t0;
        ldbl mean_h = tested ? sum_h / (ldbl)tested : 0.0L;

        for (int a = 0; a < c->n_apertures; a++) {
            fprintf(f, "%d,%llu,%d,%llu,%.6Lf,%.6Lf", N,
                    (unsigned long long)tested, c->apertures[a],
                    (unsigned long long)crit_count[a], max_h, mean_h);
            for (int H = 0; H < HT_MAX; H++)
                fprintf(f, ",%llu", (unsigned long long)tail[H]);
            fprintf(f, ",%.3f\n", rt);
        }
        fprintf(stderr, "[scan-height] N=%d tested=%llu max_h=%.2Lf time=%.2fs\n",
                N, (unsigned long long)tested, max_h, rt);
    }
    fclose(f); fclose(cf);
    fprintf(stderr, "[scan-height] wrote %s and %s\n", path, cpath);
    return 0;
}
