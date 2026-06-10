#include "critical_events.h"
#include <stdlib.h>
#include <string.h>

static void close_event(orbit_data_t *out, const config_t *cfg,
                        bigval_t *launch, bigval_t *peak, bigval_t *exitv,
                        uint64_t start_step, uint64_t end_step, uint64_t D,
                        int overflowed) {
    if (out->nev % 64 == 0)
        out->ev = realloc(out->ev, (out->nev + 64) * sizeof *out->ev);
    crit_event_t *e = &out->ev[out->nev];
    memset(e, 0, sizeof *e);
    e->start_step = start_step;
    e->end_step   = end_step;
    e->word_length = end_step - start_step;
    e->D = D;
    e->launch_log2 = bv_log2(launch);
    e->peak_log2   = bv_log2(peak);
    e->exit_log2   = bv_log2(exitv);
    e->height_log2 = e->peak_log2 - e->launch_log2;
    bv_to_decimal(launch, e->launch_dec, sizeof e->launch_dec);
    bv_to_decimal(peak,   e->peak_dec,   sizeof e->peak_dec);
    bv_to_decimal(exitv,  e->exit_dec,   sizeof e->exit_dec);
    e->status = overflowed ? "overflow" : "ok";
    for (int a = 0; a < cfg->n_apertures && a < CE_MAX_APERTURES; a++) {
        int c = cfg->crit_mode == 1
                  ? bv_geq_shl(peak, launch, cfg->apertures[a])     /* P >= V<<A   */
                  : bv_is_A_critical(launch, peak, cfg->apertures[a]); /* V^2<=2^A P */
        e->critical_A[a] = (c == 1) ? 1 : 0; /* -1 (undecidable) treated as 0 */
    }
    out->nev++;
}

int orbit_run_record_ex(uint64_t seed, const config_t *cfg,
                        const uint64_t *moduli, int nmod, orbit_data_t *out) {
    memset(out, 0, sizeof *out);
    size_t cap = 1024;
    out->b = malloc(cap * sizeof *out->b);
    if (!out->b) return 1;
    out->nmod = (moduli && nmod > 0) ? nmod : 0;
    if (out->nmod) {
        out->res = malloc((cap + 1) * (size_t)out->nmod * sizeof *out->res);
        if (!out->res) { free(out->b); return 1; }
    }

    orbit_t o; orbit_init(&o, seed);
    out->max_height = 0.0L;
    if (out->nmod)  /* x_0 residues */
        for (int q = 0; q < out->nmod; q++)
            out->res[(size_t)0 * (size_t)out->nmod + (size_t)q] = bv_mod_u64(&o.x, moduli[q]);

    bigval_t launch, peak, exitv, runmin;
    bv_init_u64(&launch, seed);
    bv_init_u64(&peak,   seed);
    bv_init_u64(&exitv,  seed);
    bv_init_u64(&runmin, seed);

    uint64_t start_step = 0, D = 0;

    while (o.status == ORBIT_RUNNING && o.step < cfg->max_steps) {
        uint32_t bi = orbit_step(&o);
        if (o.status == ORBIT_OVERFLOW) break;
        if (out->len + 1 >= cap) {
            cap *= 2;
            out->b = realloc(out->b, cap * sizeof *out->b);
            if (!out->b) { orbit_clear(&o); return 1; }
            if (out->nmod) {
                out->res = realloc(out->res, (cap + 1) * (size_t)out->nmod * sizeof *out->res);
                if (!out->res) { orbit_clear(&o); return 1; }
            }
        }
        out->b[out->len++] = (uint16_t)bi;
        if (out->nmod)   /* residues of the new state x_{out->len} */
            for (int q = 0; q < out->nmod; q++)
                out->res[out->len * (size_t)out->nmod + (size_t)q] = bv_mod_u64(&o.x, moduli[q]);
        D += bi;

        ldbl h = orbit_height(&o);
        if (h > out->max_height) out->max_height = h;

        if (bv_cmp(&o.x, &peak) > 0) bv_set(&peak, &o.x);   /* new peak     */
        if (bv_cmp(&o.x, &runmin) < 0) {                     /* new record low */
            bv_set(&exitv, &o.x);
            close_event(out, cfg, &launch, &peak, &exitv,
                        start_step, o.step, D, 0);
            bv_set(&runmin, &o.x);
            bv_set(&launch, &o.x);
            bv_set(&peak,   &o.x);
            start_step = o.step;
            D = 0;
        }
    }
    /* close the trailing excursion */
    bv_set(&exitv, &o.x);
    close_event(out, cfg, &launch, &peak, &exitv,
                start_step, o.step, D, o.status == ORBIT_OVERFLOW);

    out->status = o.status;
    bv_clear(&launch); bv_clear(&peak); bv_clear(&exitv); bv_clear(&runmin);
    orbit_clear(&o);
    return 0;
}

int orbit_run_record(uint64_t seed, const config_t *cfg, orbit_data_t *out) {
    return orbit_run_record_ex(seed, cfg, NULL, 0, out);
}

const char *ce_label_name(seg_label_t l) {
    switch (l) {
        case LBL_ORDINARY:    return "ordinary";
        case LBL_HIGH_ASCENT: return "high_ascent";
        case LBL_CRITICAL:    return "critical_C_A";
        case LBL_POST_EXIT:   return "post_exit";
        case LBL_SUBEQ:       return "sub_equilibrium_tail";
        case LBL_CYCLE:       return "cycle_neighborhood";
        default:              return "unknown";
    }
}

long ce_event_of_step(const orbit_data_t *d, uint64_t j) {
    for (size_t e = 0; e < d->nev; e++)
        if (j >= d->ev[e].start_step && j < d->ev[e].end_step) return (long)e;
    return -1;
}

void ce_label_steps(const orbit_data_t *d, const config_t *cfg, uint8_t *label) {
    const ldbl SUBEQ = 2.0L;   /* deficit threshold (bits below equilibrium) */
    uint64_t B = 0;
    for (size_t i = 0; i < d->len; i++) {
        ldbl E = (ldbl)B - (ldbl)i * LOG2_3;   /* E_i before step i */
        label[i] = (E < -SUBEQ) ? (uint8_t)LBL_SUBEQ : (uint8_t)LBL_ORDINARY;
        B += d->b[i];
    }
    /* excursion labels override (critical for aperture index 0) */
    for (size_t e = 0; e < d->nev; e++) {
        crit_event_t *ev = &d->ev[e];
        uint8_t lab = ev->critical_A[0] ? (uint8_t)LBL_CRITICAL
                    : (ev->height_log2 >= 1.0L ? (uint8_t)LBL_HIGH_ASCENT : 0xFF);
        if (lab != 0xFF)
            for (uint64_t i = ev->start_step; i < ev->end_step && i < d->len; i++)
                label[i] = lab;
    }
    /* post-exit windows (only over ordinary/sub-equilibrium steps) */
    for (size_t e = 0; e < d->nev; e++) {
        uint64_t s0 = d->ev[e].end_step;
        for (uint64_t i = s0; i < s0 + (uint64_t)cfg->post_len && i < d->len; i++)
            if (label[i] == LBL_ORDINARY || label[i] == LBL_SUBEQ)
                label[i] = (uint8_t)LBL_POST_EXIT;
    }
}

void orbit_data_free(orbit_data_t *d) {
    free(d->b);   d->b = NULL;   d->len = 0;
    free(d->ev);  d->ev = NULL;  d->nev = 0;
    free(d->res); d->res = NULL; d->nmod = 0;
}
