#include "residue_height_graph.h"
#include "modarith.h"
#include <math.h>

/* residue image of a under branch b (forward map for odd Q, inverse otherwise) */
static uint64_t residue_image(uint64_t a, int b, uint64_t Q, int forward,
                              uint64_t inv2, uint64_t inv3) {
    if (forward) {
        uint64_t f = (3 * a + 1) % Q;
        return ma_mulmod(f, ma_powmod(inv2, (uint64_t)b, Q), Q);
    }
    uint64_t p2 = ma_powmod(2, (uint64_t)b, Q);
    uint64_t val = (ma_mulmod(p2, a, Q) + Q - 1) % Q;
    return ma_mulmod(inv3, val, Q);
}

static ldbl tilt_weight(ldbl s, int b) {
    return powl(2.0L, -(ldbl)b) * powl(2.0L, s * (LOG2_3 - (ldbl)b));
}

int rhg_build(csr_t *out, operator_info_t *info,
              uint64_t Q, int L, int R, int Bmax, ldbl s,
              const character_t *chi, int use_height, int height_mode) {
    int even = (Q % 2 == 0);
    int div3 = (Q % 3 == 0);
    if (even && div3) return 1;                 /* mixed 2^a 3^r: unsupported here */

    int forward = !even;                        /* Q odd -> forward map */
    uint64_t inv2 = 0, inv3 = 0;
    if (forward) inv2 = ma_inv(2, Q);
    else         inv3 = ma_inv(3, Q);

    int Zsize = use_height ? (L + 1) : 1;
    long n = (long)Q * Zsize;
    triplets_t t; tri_init(&t, (int)n);

    if (!use_height || height_mode == RHG_SYNC) {
        /* faithful skew product: one b drives residue AND height together. */
        for (uint64_t a = 0; a < Q; a++) {
            cldbl phase = chi ? char_value(chi, a) : (1.0L + 0.0L * I);
            for (int b = 1; b <= Bmax; b++) {
                uint64_t ap = residue_image(a, b, Q, forward, inv2, inv3);
                cldbl w = tilt_weight(s, b) * phase;
                if (!use_height) {
                    tri_add(&t, (int)ap, (int)a, w);
                } else {
                    int dz = (int)lroundl((ldbl)R * (LOG2_3 - (ldbl)b));
                    for (int z = 0; z <= L; z++) {
                        int zp = z + dz;
                        if (zp < 0 || zp > L) continue;
                        tri_add(&t, (int)ap * Zsize + zp, (int)a * Zsize + z, w);
                    }
                }
            }
        }
    } else {
        /* FACTORED: M = L_res(chi) (x) T_height. The character twists only the
         * residue factor; the height is a residue-independent survival kernel
         * (its valuation b' drawn independently of the residue's b), so the
         * killed operator's gap ratio equals the residue-sector ratio.
         * Height kernel uses the normalized b-marginal q(b)=2^{-b}2^{s.Delta}/M(s). */
        ldbl Msum = 0.0L;
        for (int b = 1; b <= Bmax; b++) Msum += tilt_weight(s, b);

        for (uint64_t a = 0; a < Q; a++) {
            cldbl phase = chi ? char_value(chi, a) : (1.0L + 0.0L * I);
            for (int b = 1; b <= Bmax; b++) {
                uint64_t ap = residue_image(a, b, Q, forward, inv2, inv3);
                cldbl wr = tilt_weight(s, b) * phase;     /* residue factor (carries magnitude) */
                for (int z = 0; z <= L; z++) {
                    for (int bp = 1; bp <= Bmax; bp++) {  /* independent height valuation */
                        int dz = (int)lroundl((ldbl)R * (LOG2_3 - (ldbl)bp));
                        int zp = z + dz;
                        if (zp < 0 || zp > L) continue;
                        ldbl wh = tilt_weight(s, bp) / Msum; /* height transport (prob) */
                        tri_add(&t, (int)ap * Zsize + zp, (int)a * Zsize + z, wr * wh);
                    }
                }
            }
        }
    }

    *out = csr_from_triplets(&t);
    tri_free(&t);

    if (info) {
        info->Q = Q; info->L = L; info->R = R; info->Bmax = Bmax; info->s = s;
        info->use_height = use_height;
        info->height_mode = use_height ? height_mode : RHG_SYNC;
        info->dim = (int)n; info->nnz = out->nnz;
        info->trunc_tail = powl(2.0L, -(ldbl)Bmax);
        info->map_mode = forward ? 0 : 1;
    }
    return 0;
}
