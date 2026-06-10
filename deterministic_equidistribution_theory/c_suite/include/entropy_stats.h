/* entropy_stats.h — empirical valuation laws, KL divergences, entropy,
 * Cramer-tilt comparisons. All divergences/entropies are in BITS (base-2),
 * consistent with the log2 framing of the manuscript.
 *
 * Reference laws:
 *   annealed     p_b   = 2^{-b}        (b >= 1)
 *   critical tilt p^(1)_b = 3 * 4^{-b}  (the M(1)=1 Cramer root)
 */
#ifndef AIPM_ENTROPY_STATS_H
#define AIPM_ENTROPY_STATS_H

#include <stdint.h>
#include "common.h"

#define ES_BMAX 64   /* valuations b in 1..ES_BMAX; larger lumped into ES_BMAX */

typedef struct {
    uint64_t count[ES_BMAX + 1];   /* count[b], b in 1..ES_BMAX */
    uint64_t total;
} vstat_t;

void  vstat_reset(vstat_t *v);
void  vstat_add(vstat_t *v, uint32_t b);

/* reference single-symbol laws */
ldbl  es_p_annealed(int b);   /* 2^{-b}      */
ldbl  es_p_critical(int b);   /* 3 * 4^{-b}  */

/* empirical quantities (return 0 if v->total == 0) */
ldbl  es_phat(const vstat_t *v, int b);
ldbl  es_entropy(const vstat_t *v);              /* H(phat), bits           */
ldbl  es_mean_b(const vstat_t *v);               /* sum b*phat              */
ldbl  es_entropy_per_digit(const vstat_t *v);    /* H(phat)/mean_b          */
ldbl  es_M(const vstat_t *v, ldbl s);            /* sum phat*2^{s(log2 3-b)}*/

/* KL(phat || q) in bits, q one of the reference laws (1 = annealed, else
 * critical). Tolerant of zero phat bins. */
ldbl  es_kl_annealed(const vstat_t *v);
ldbl  es_kl_critical(const vstat_t *v);

#endif /* AIPM_ENTROPY_STATS_H */
