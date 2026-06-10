#include "defect_sums.h"
#include <math.h>

ldbl ds_weight(ldbl s, uint32_t b) {
    return powl(2.0L, s * (LOG2_3 - (ldbl)b));
}

void ds_prefix(cldbl *prefix, const cldbl *term, size_t len) {
    prefix[0] = 0.0L + 0.0L * I;
    for (size_t i = 0; i < len; i++) prefix[i + 1] = prefix[i] + term[i];
}

cldbl ds_window(const cldbl *prefix, size_t n, size_t l) {
    if (l == 0) return 0.0L + 0.0L * I;
    return (prefix[n + l] - prefix[n]) / (ldbl)l;
}
