/* exp_shadow_search.c — Experiment I: quenched spectral-shadow search.
 *
 * The central integration experiment. Catalog unusual deterministic windows
 * (excursions of every label, plus post-exit windows) and, for each, find
 *     max_{Q,chi,s} |W_{n,l}(x;chi,s)|
 * over the configured grid. A window is shadow-bearing if this exceeds delta.
 *
 * CRITIQUE (dc_1.md, point 5): the obstruction may be sparse/clustered, not
 * positive-density. We therefore report per-window max|W| AND window length, so
 * both limsup plateaus (high |W| in any window) and long blocks (large length
 * with |W|>=delta) are visible; we do not require positive-density n.
 */
#include "experiments.h"
#include "critical_events.h"
#include "characters.h"
#include "defect_sums.h"
#include "entropy_stats.h"
#include "io_csv.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static int is_pow3(uint64_t Q){ if(Q%2==0)return 0; while(Q%3==0)Q/=3; return Q==1; }

int exp_shadow_search(const config_t *c, int argc, char **argv) {
    char path[512];
    snprintf(path, sizeof path, "%s/shadow_search.csv", c->output_dir);
    FILE *f = csv_open(path, "shadow_search",
        "window_id,seed,start_step,length,label,max_abs_W,argmax_Q,argmax_char,"
        "argmax_s,KL_to_p,KL_to_p1,mean_delta,max_height,shadow_flag", argc, argv);
    if (!f) { perror("csv_open"); return 1; }

    /* precompute characters per (modulus, k) — independent of seed */
    int nQ = c->n_moduli;
    int *kcount = calloc((size_t)nQ, sizeof *kcount);
    character_t **chars = calloc((size_t)nQ, sizeof *chars);
    for (int qi = 0; qi < nQ; qi++) {
        uint64_t Q = c->moduli[qi];
        int km = c->char_cap;
        int lim = is_pow3(Q) ? (int)(Q - Q/3) - 1 : (int)Q - 1;
        if (km > lim) km = lim;
        kcount[qi] = km;
        chars[qi] = malloc((size_t)km * sizeof(character_t));
        for (int k = 1; k <= km; k++) {
            if (is_pow3(Q)) char_make_mult_3r(&chars[qi][k-1], Q, (uint64_t)k);
            else            char_make_additive(&chars[qi][k-1], Q, (uint64_t)k);
        }
    }

    uint64_t lo, hi, step = 2;
    if (c->end >= c->start && c->end > 1) { lo = c->start | 1u; hi = c->end + 1; }
    else {
        int N = c->octave_min;
        lo = ((uint64_t)1 << N) | 1u;
        hi = (N + 1 >= 64) ? ~(uint64_t)0 : ((uint64_t)1 << (N + 1));
        uint64_t odds = (hi - lo)/2 + 1;
        if (c->seeds_per_octave && odds > c->seeds_per_octave) step = 2*(odds/c->seeds_per_octave);
    }

    uint64_t wid = 0, shadow_hits = 0;
    for (uint64_t seed = lo; seed < hi; seed += step) {
        orbit_data_t d;
        if (orbit_run_record_ex(seed, c, c->moduli, nQ, &d) != 0) continue;
        if (d.len == 0) { orbit_data_free(&d); continue; }
        uint8_t *label = malloc(d.len);
        ce_label_steps(&d, c, label);

        /* candidate windows: each excursion, plus its post-exit window */
        for (size_t ei = 0; ei < d.nev; ei++) {
            crit_event_t *e = &d.ev[ei];
            for (int which = 0; which < 2; which++) {
                uint64_t start, len;
                ldbl maxh;
                if (which == 0) {                       /* the excursion */
                    start = e->start_step;
                    len = (e->end_step <= d.len ? e->end_step : d.len) - start;
                    maxh = e->height_log2;
                } else {                                /* post-exit window */
                    start = e->end_step;
                    if (start >= d.len) continue;
                    len = (uint64_t)c->post_len;
                    if (start + len > d.len) len = d.len - start;
                    maxh = 0.0L;
                }
                if (len < 8) continue;

                vstat_t v; vstat_reset(&v);
                for (uint64_t i = start; i < start+len; i++) vstat_add(&v, d.b[i]);

                ldbl best = 0.0L; uint64_t aQ = 0; int ak = 0; ldbl as = 0.0L;
                for (int qi = 0; qi < nQ; qi++) {
                    for (int kk = 0; kk < kcount[qi]; kk++) {
                        for (int ti = 0; ti < c->n_tilts; ti++) {
                            ldbl s = c->tilts[ti];
                            cldbl W = 0;
                            for (uint64_t i = start; i < start+len; i++) {
                                uint64_t a = d.res[i*(size_t)d.nmod + (size_t)qi];
                                W += char_value(&chars[qi][kk], a) * ds_weight(s, d.b[i]);
                            }
                            ldbl ab = cabsl(W) / (ldbl)len;
                            if (ab > best) { best = ab; aQ = c->moduli[qi]; ak = kk+1; as = s; }
                        }
                    }
                }
                /* length-scaled null: a decorrelated window of length L with
                 * unit-modulus character gives E|W| ~ rms(weights)/sqrt(L).
                 * A genuine shadow must exceed delta AND clearly beat this null
                 * (critique pt 1/5: separate real plateaus from finite-length
                 * noise + max-over-grid inflation). */
                ldbl sq = 0.0L;
                for (uint64_t i = start; i < start+len; i++) {
                    ldbl w = ds_weight(as, d.b[i]); sq += w*w;
                }
                ldbl null_rms = sqrtl(sq) / (ldbl)len;   /* = rms_w / sqrt(len) */
                int flag = (best >= c->delta) && (best >= 3.0L * null_rms);
                if (flag) shadow_hits++;
                wid++;
                fprintf(f, "%llu,%llu,%llu,%llu,%s,%.6Lf,%llu,%d,%.4Lf,%.6Lf,%.6Lf,%.6Lf,%.4Lf,%d\n",
                    (unsigned long long)wid, (unsigned long long)seed,
                    (unsigned long long)start, (unsigned long long)len,
                    ce_label_name((seg_label_t)label[start < d.len ? start : d.len-1]),
                    best, (unsigned long long)aQ, ak, as,
                    es_kl_annealed(&v), es_kl_critical(&v),
                    LOG2_3 - es_mean_b(&v), maxh, flag);
            }
        }
        free(label);
        orbit_data_free(&d);
    }

    for (int qi = 0; qi < nQ; qi++) {
        for (int kk = 0; kk < kcount[qi]; kk++) char_free(&chars[qi][kk]);
        free(chars[qi]);
    }
    free(chars); free(kcount);

    fclose(f);
    fprintf(stderr, "[shadow-search] %llu windows, %llu shadow-bearing (delta=%.3Lf); wrote %s\n",
            (unsigned long long)wid, (unsigned long long)shadow_hits, c->delta, path);
    return 0;
}
