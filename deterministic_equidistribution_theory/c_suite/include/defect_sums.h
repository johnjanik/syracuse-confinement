/* defect_sums.h — the deterministic defect cocycle W_{n,l}(x;chi,s).
 *
 *   W_{n,l}(x;chi,s) = (1/l) sum_{i=n}^{n+l-1} chi(x_i mod Q) 2^{s(log2 3 - b_i)}
 *
 * Computed from per-step "terms" t_i = chi(x_i mod Q) * 2^{s*Delta_{b_i}} via a
 * complex prefix sum, so any window is an O(1) difference. The residues
 * x_i mod Q are taken from the exact orbit value (works for any Q, including
 * Q = 2^a 3^r, where the accelerated step is not invertible mod 2^a).
 */
#ifndef AIPM_DEFECT_SUMS_H
#define AIPM_DEFECT_SUMS_H

#include <stddef.h>
#include "common.h"

/* tilt weight 2^{s(log2 3 - b)} (real, positive). */
ldbl  ds_weight(ldbl s, uint32_t b);

/* prefix[0]=0; prefix[m] = sum_{i<m} term[i], for m in 1..len. (len+1 entries) */
void  ds_prefix(cldbl *prefix, const cldbl *term, size_t len);

/* mean of term over [n, n+l): (prefix[n+l]-prefix[n]) / l. */
cldbl ds_window(const cldbl *prefix, size_t n, size_t l);

#endif /* AIPM_DEFECT_SUMS_H */
