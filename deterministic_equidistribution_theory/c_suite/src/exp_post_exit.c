/* exp_post_exit.c — Experiment D: post-exit taboo / entropy-space repulsion.
 *
 * After a completed critical excursion, is the next window separated from the
 * critical tilted law p^(1)? If M_post(1) = sum phat_post(b) 2^{log2 3 - b} < 1
 * with a stable margin, post-exit behavior is subcritical — the proposed reason
 * two critical excursions fail to concatenate (spec Section "Experiment D").
 */
#include "experiments.h"
#include "critical_events.h"
#include "entropy_stats.h"
#include "io_csv.h"
#include <stdio.h>

static int min_aperture(const config_t *c, const crit_event_t *e) {
    for (int a = 0; a < c->n_apertures; a++) if (e->critical_A[a]) return c->apertures[a];
    return -1;
}

int exp_post_exit(const config_t *c, int argc, char **argv) {
    char path[512];
    snprintf(path, sizeof path, "%s/post_exit.csv", c->output_dir);
    FILE *f = csv_open(path, "post_exit",
        "event_id,seed,A,exit_step,post_length,KL_post_to_p,KL_post_to_p1,"
        "M_post_1,p1_post,p2_post,p3_post,mean_b_post,next_critical_flag,"
        "next_critical_A,gap_steps", argc, argv);
    if (!f) { perror("csv_open"); return 1; }

    uint64_t lo, hi, step = 2;
    if (c->end >= c->start && c->end > 1) { lo = c->start | 1u; hi = c->end + 1; }
    else {
        int N = c->octave_min;
        lo = ((uint64_t)1 << N) | 1u;
        hi = (N + 1 >= 64) ? ~(uint64_t)0 : ((uint64_t)1 << (N + 1));
        uint64_t odds = (hi - lo) / 2 + 1;
        if (c->seeds_per_octave && odds > c->seeds_per_octave)
            step = 2 * (odds / c->seeds_per_octave);
    }

    uint64_t eid = 0, count = 0;
    for (uint64_t seed = lo; seed < hi; seed += step) {
        orbit_data_t d;
        if (orbit_run_record(seed, c, &d) != 0) continue;

        for (size_t ei = 0; ei < d.nev; ei++) {
            int A = min_aperture(c, &d.ev[ei]);
            if (A < 0) continue;                 /* only completed critical excursions */
            eid++;
            uint64_t exit_step = d.ev[ei].end_step;
            uint64_t L = (uint64_t)c->post_len;
            if (exit_step + L > d.len) L = (exit_step < d.len) ? d.len - exit_step : 0;
            if (L == 0) continue;
            count++;

            vstat_t v; vstat_reset(&v);
            for (uint64_t i = exit_step; i < exit_step + L; i++) vstat_add(&v, d.b[i]);

            /* next critical excursion */
            int nflag = 0, nA = -1; long gap = -1;
            for (size_t ej = ei + 1; ej < d.nev; ej++) {
                int A2 = min_aperture(c, &d.ev[ej]);
                if (A2 >= 0) { nflag = 1; nA = A2; gap = (long)(d.ev[ej].start_step - exit_step); break; }
            }

            fprintf(f, "%llu,%llu,%d,%llu,%llu,%.6Lf,%.6Lf,%.6Lf,%.6Lf,%.6Lf,"
                       "%.6Lf,%.6Lf,%d,%d,%ld\n",
                (unsigned long long)eid, (unsigned long long)seed, A,
                (unsigned long long)exit_step, (unsigned long long)L,
                es_kl_annealed(&v), es_kl_critical(&v), es_M(&v, 1.0L),
                es_phat(&v,1), es_phat(&v,2), es_phat(&v,3), es_mean_b(&v),
                nflag, nA, gap);
        }
        orbit_data_free(&d);
    }
    fclose(f);
    fprintf(stderr, "[post-exit] %llu post-exit windows; wrote %s\n",
            (unsigned long long)count, path);
    return 0;
}
