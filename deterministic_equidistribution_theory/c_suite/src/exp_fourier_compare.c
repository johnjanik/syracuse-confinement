/* exp_fourier_compare.c — Experiment F: exact operator gap vs annealed Fourier.
 *
 * Compares the exact residue-only operator gap for Q = 3^r multiplicative
 * sectors against the i.i.d. valuation Fourier transform
 *     |p_hat(xi)| = 1/sqrt(5 - 4 cos 2 pi xi),   xi = k/phi,  phi = 2*3^{r-1}.
 *
 * CRITIQUE (dc_1.md, point 3): the annealed value is a MODEL prediction, NOT
 * the exact operator's spectral radius. We report them in SEPARATE columns and
 * never substitute one for the other; "deviation" measures how far the exact
 * coupled operator departs from the i.i.d. shadow.
 */
#include "experiments.h"
#include "residue_height_graph.h"
#include "io_csv.h"
#include <stdio.h>
#include <math.h>

#ifndef M_PIl
#define M_PIl 3.141592653589793238462643383279502884L
#endif

static int is_pow3(uint64_t Q) {
    if (Q % 2 == 0) return 0;
    while (Q % 3 == 0) Q /= 3;
    return Q == 1;
}

int exp_fourier_compare(const config_t *c, int argc, char **argv) {
    char path[512];
    snprintf(path, sizeof path, "%s/fourier_comparison.csv", c->output_dir);
    FILE *f = csv_open(path, "fourier_comparison",
        "Q,character_index,xi,annealed_abs_hat_p,exact_gap_ratio_s0,"
        "exact_gap_ratio_s1,deviation", argc, argv);
    if (!f) { perror("csv_open"); return 1; }

    /* residue-only operators are small (dim = Q); a moderate Krylov dimension
     * already nails the dominant eigenvalue magnitude. Looser growth keeps the
     * full-character-group sweep fast at large Q. */
    const int ARN_M0 = 60, ARN_MMAX = 150; const ldbl ARN_TOL = 1e-8L;

    for (int qi = 0; qi < c->n_moduli; qi++) {
        uint64_t Q = c->moduli[qi];
        if (!is_pow3(Q)) {
            fprintf(stderr, "[fourier-compare] Q=%llu not a power of 3, skipped\n",
                    (unsigned long long)Q);
            continue;
        }
        int phi = (int)(Q - Q/3);   /* 2*3^{r-1} */

        /* baseline = principal character on units (chi_0: 1 on units, 0 on
         * non-units), the apples-to-apples trivial sector for multiplicative
         * characters. (Using the full trivial operator would mix in non-unit
         * residues that the chi sectors never see.) */
        ldbl rho0_s0 = 0, rho0_s1 = 0;
        for (int pass = 0; pass < 2; pass++) {
            ldbl s = pass ? 1.0L : 0.0L;
            character_t ch0; char_make_mult_3r(&ch0, Q, 0);
            csr_t A0; operator_info_t i0;
            rhg_build(&A0, &i0, Q, 0, 0, c->bmax, s, &ch0, 0, RHG_SYNC);
            ldbl r = csr_spectral_radius_arnoldi(&A0, ARN_M0, ARN_MMAX, ARN_TOL, NULL, NULL);
            if (pass) rho0_s1 = r; else rho0_s0 = r;
            csr_free(&A0); char_free(&ch0);
        }

        /* char_cap<=0 => full character group. chi_k and chi_{phi-k} are
         * complex conjugates with equal spectral radius, so k=1..floor(phi/2)
         * covers every distinct gap magnitude (incl. the quadratic char k=phi/2). */
        int kmax = (c->char_cap <= 0) ? phi/2 : c->char_cap;
        if (kmax > phi - 1) kmax = phi - 1;
        for (int k = 1; k <= kmax; k++) {
            ldbl xi = (ldbl)k / (ldbl)phi;
            ldbl ann = 1.0L / sqrtl(5.0L - 4.0L * cosl(2.0L * M_PIl * xi));

            character_t ch; char_make_mult_3r(&ch, Q, (uint64_t)k);
            ldbl gr0 = 0, gr1 = 0;
            for (int pass = 0; pass < 2; pass++) {
                ldbl s = pass ? 1.0L : 0.0L;
                csr_t A; operator_info_t info;
                rhg_build(&A, &info, Q, 0, 0, c->bmax, s, &ch, 0, RHG_SYNC);
                ldbl r = csr_spectral_radius_arnoldi(&A, ARN_M0, ARN_MMAX, ARN_TOL, NULL, NULL);
                ldbl r0 = pass ? rho0_s1 : rho0_s0;
                ldbl gr = r0 > 0 ? r / r0 : 0.0L;
                if (pass) gr1 = gr; else gr0 = gr;
                csr_free(&A);
            }
            char_free(&ch);
            fprintf(f, "%llu,%d,%.6Lf,%.6Lf,%.6Lf,%.6Lf,%.6Lf\n",
                (unsigned long long)Q, k, xi, ann, gr0, gr1, gr0 - ann);
        }
        fprintf(stderr, "[fourier-compare] Q=%llu phi=%d done\n",
                (unsigned long long)Q, phi);
    }
    fclose(f);
    fprintf(stderr, "[fourier-compare] wrote %s\n", path);
    return 0;
}
