#include "entropy_stats.h"
#include <math.h>
#include <string.h>

void vstat_reset(vstat_t *v) { memset(v, 0, sizeof *v); }

void vstat_add(vstat_t *v, uint32_t b) {
    if (b < 1) return;                 /* b = v2(3x+1) >= 1 always */
    if (b > ES_BMAX) b = ES_BMAX;      /* lump the (vanishingly rare) tail */
    v->count[b]++;
    v->total++;
}

ldbl es_p_annealed(int b) { return powl(2.0L, -(ldbl)b); }
ldbl es_p_critical(int b) { return 3.0L * powl(4.0L, -(ldbl)b); }

ldbl es_phat(const vstat_t *v, int b) {
    if (v->total == 0 || b < 1 || b > ES_BMAX) return 0.0L;
    return (ldbl)v->count[b] / (ldbl)v->total;
}

ldbl es_entropy(const vstat_t *v) {
    if (v->total == 0) return 0.0L;
    ldbl H = 0.0L;
    for (int b = 1; b <= ES_BMAX; b++) {
        ldbl p = es_phat(v, b);
        if (p > 0.0L) H -= p * log2l(p);
    }
    return H;
}

ldbl es_mean_b(const vstat_t *v) {
    if (v->total == 0) return 0.0L;
    ldbl m = 0.0L;
    for (int b = 1; b <= ES_BMAX; b++) m += (ldbl)b * es_phat(v, b);
    return m;
}

ldbl es_entropy_per_digit(const vstat_t *v) {
    ldbl mb = es_mean_b(v);
    return mb > 0.0L ? es_entropy(v) / mb : 0.0L;
}

ldbl es_M(const vstat_t *v, ldbl s) {
    if (v->total == 0) return 0.0L;
    ldbl M = 0.0L;
    for (int b = 1; b <= ES_BMAX; b++) {
        ldbl p = es_phat(v, b);
        if (p > 0.0L) M += p * powl(2.0L, s * (LOG2_3 - (ldbl)b));
    }
    return M;
}

static ldbl kl(const vstat_t *v, int annealed) {
    if (v->total == 0) return 0.0L;
    ldbl D = 0.0L;
    for (int b = 1; b <= ES_BMAX; b++) {
        ldbl p = es_phat(v, b);
        if (p <= 0.0L) continue;
        ldbl q = annealed ? es_p_annealed(b) : es_p_critical(b);
        D += p * log2l(p / q);
    }
    return D;
}
ldbl es_kl_annealed(const vstat_t *v) { return kl(v, 1); }
ldbl es_kl_critical(const vstat_t *v) { return kl(v, 0); }
