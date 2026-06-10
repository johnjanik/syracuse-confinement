/* exp_defect_windows.c — Experiment C: deterministic defect cocycle sums.
 *
 * Computes W_{n,l}(x;chi,s) on actual orbits, over a grid of moduli Q,
 * additive characters chi_k, tilts s, and window lengths l (plus the full
 * prefix sum). Each window is tagged with its segment label.
 *
 * Pre-registered (spec Section "Experiment C"): ordinary windows decay
 * (|W|->0); critical windows may carry the Cramer tilt in b-statistics but
 * should NOT show persistent nontrivial residue resonance if H23a holds.
 * Windowed sums are primary (critique: the obstruction is clustered).
 */
#include "experiments.h"
#include "critical_events.h"
#include "characters.h"
#include "defect_sums.h"
#include "io_csv.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static void emit(FILE *f, uint64_t seed, uint64_t start, uint64_t length,
                 uint64_t Q, const char *ctype, uint64_t cidx, ldbl s,
                 cldbl W, ldbl mean_b, const char *label, long eid) {
    ldbl ab = cabsl(W);
    ldbl mean_delta = LOG2_3 - mean_b;
    fprintf(f, "%llu,%llu,%llu,%llu,%s,%llu,%.4Lf,%.6Le,%.6Le,%.6Le,%.6Lf,%.6Lf,%s,%ld\n",
        (unsigned long long)seed, (unsigned long long)start,
        (unsigned long long)length, (unsigned long long)Q, ctype,
        (unsigned long long)cidx, s, creall(W), cimagl(W), ab,
        mean_delta, mean_b, label, eid);
}

int exp_defect_windows(const config_t *c, int argc, char **argv) {
    char path[512];
    snprintf(path, sizeof path, "%s/defect_windows.csv", c->output_dir);
    FILE *f = csv_open(path, "defect_windows",
        "seed,start_step,length,Q,char_type,char_index,s,real_W,imag_W,abs_W,"
        "mean_delta,mean_b,segment_label,event_id", argc, argv);
    if (!f) { perror("csv_open"); return 1; }

    uint64_t lo, hi;
    if (c->end >= c->start && c->end > 1) { lo = c->start | 1u; hi = c->end + 1; }
    else { lo = c->seed | 1u; hi = lo + 1; }

    uint64_t rows = 0;
    for (uint64_t seed = lo; seed < hi; seed += 2) {
        orbit_data_t d;
        if (orbit_run_record_ex(seed, c, c->moduli, c->n_moduli, &d) != 0) continue;
        if (d.len == 0) { orbit_data_free(&d); continue; }

        uint8_t *label = malloc(d.len);
        ce_label_steps(&d, c, label);

        /* prefix sums of b for mean_b over windows */
        uint64_t *Bpre = malloc((d.len + 1) * sizeof *Bpre);
        Bpre[0] = 0;
        for (size_t i = 0; i < d.len; i++) Bpre[i+1] = Bpre[i] + d.b[i];

        cldbl *term   = malloc(d.len * sizeof *term);
        cldbl *prefix = malloc((d.len + 1) * sizeof *prefix);

        for (int qi = 0; qi < c->n_moduli; qi++) {
            uint64_t Q = c->moduli[qi];
            int kmax = c->char_cap; if ((uint64_t)kmax > Q - 1) kmax = (int)(Q - 1);
            for (int k = 1; k <= kmax; k++) {
                character_t ch;
                if (char_make_additive(&ch, Q, (uint64_t)k) != 0) continue;
                for (int ti = 0; ti < c->n_tilts; ti++) {
                    ldbl s = c->tilts[ti];
                    for (size_t i = 0; i < d.len; i++) {
                        uint64_t a = d.res[i * (size_t)d.nmod + (size_t)qi];
                        term[i] = char_value(&ch, a) * ds_weight(s, d.b[i]);
                    }
                    ds_prefix(prefix, term, d.len);

                    /* full prefix W_{0,len} */
                    {
                        cldbl W = ds_window(prefix, 0, d.len);
                        ldbl mb = (ldbl)Bpre[d.len] / (ldbl)d.len;
                        emit(f, seed, 0, d.len, Q, "add", (uint64_t)k, s, W, mb,
                             ce_label_name((seg_label_t)label[0]),
                             ce_event_of_step(&d, 0));
                        rows++;
                    }
                    /* non-overlapping sliding windows of each length */
                    for (int wi = 0; wi < c->n_windows; wi++) {
                        size_t L = (size_t)c->windows[wi];
                        if (L == 0 || L > d.len) continue;
                        for (size_t n = 0; n + L <= d.len; n += L) {
                            cldbl W = ds_window(prefix, n, L);
                            ldbl mb = (ldbl)(Bpre[n+L] - Bpre[n]) / (ldbl)L;
                            emit(f, seed, n, L, Q, "add", (uint64_t)k, s, W, mb,
                                 ce_label_name((seg_label_t)label[n]),
                                 ce_event_of_step(&d, n));
                            rows++;
                        }
                    }
                }
                char_free(&ch);
            }
        }
        free(term); free(prefix); free(Bpre); free(label);
        orbit_data_free(&d);
    }
    fclose(f);
    fprintf(stderr, "[defect-windows] wrote %llu rows to %s\n",
            (unsigned long long)rows, path);
    return 0;
}
