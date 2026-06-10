/* exp_spectral_gaps.c — Experiment E: exact residue-height operator gaps.
 *
 * Builds L_{s,Q,L,chi} and estimates rho(L_{s,Q,L,chi}) <= (1-kappa_Q) rho_0.
 * Trivial sector rho0 via power iteration; nontrivial sectors likewise (the
 * dominant eigenvalue may be complex; we estimate its magnitude). For Q = 3^r
 * we use multiplicative characters (the arithmetically natural family, with 2
 * a primitive root); otherwise additive characters.
 */
#include "experiments.h"
#include "residue_height_graph.h"
#include "io_csv.h"
#include <stdio.h>
#include <string.h>

/* a power of 3 (and odd) -> use multiplicative characters mod 3^r. */
static int is_pow3(uint64_t Q) {
    if (Q % 2 == 0) return 0;
    while (Q % 3 == 0) Q /= 3;
    return Q == 1;
}
static int make_char(character_t *ch, uint64_t Q, uint64_t k, const char **type) {
    if (is_pow3(Q)) { *type = "mult3r"; return char_make_mult_3r(ch, Q, k); }
    *type = "add"; return char_make_additive(ch, Q, k);
}

int exp_spectral_gaps(const config_t *c, int argc, char **argv) {
    char path[512];
    snprintf(path, sizeof path, "%s/spectral_gaps.csv", c->output_dir);
    FILE *f = csv_open(path, "spectral_gaps",
        "Q,L,R,Bmax,s,char_type,char_index,rho_est,rho0_est,gap_ratio,"
        "iterations,residual,truncation_tail,matrix_nnz,matrix_dim,"
        "rho_principal,gap_ratio_units", argc, argv);
    if (!f) { perror("csv_open"); return 1; }

    /* Arnoldi (Krylov) solver: resolves the near-degenerate top cluster of the
     * killed residue-height operator that defeats power iteration. */
    const int ARN_M0 = 40, ARN_MMAX = 240; const ldbl ARN_TOL = 1e-10L;

    for (int qi = 0; qi < c->n_moduli; qi++) {
        uint64_t Q = c->moduli[qi];
        for (int ti = 0; ti < c->n_tilts; ti++) {
            ldbl s = c->tilts[ti];

            /* trivial sector */
            csr_t A0; operator_info_t i0;
            if (rhg_build(&A0, &i0, Q, c->L, c->R, c->bmax, s, NULL, 1, c->height_mode) != 0) {
                fprintf(stderr, "[spectral-gaps] Q=%llu unsupported (2^a 3^r), skipped\n",
                        (unsigned long long)Q);
                break;
            }
            ldbl res0; int it0;
            ldbl rho0 = csr_spectral_radius_arnoldi(&A0, ARN_M0, ARN_MMAX, ARN_TOL, &res0, &it0);

            /* principal-on-units baseline: for multiplicative characters (which
             * vanish on non-units) the apples-to-apples trivial sector is the
             * principal character chi_0 (=1 on units, 0 on non-units), NOT the
             * full trivial operator. For non-pow3 (additive) Q, rho_principal=rho0. */
            ldbl rho_principal = rho0;
            if (is_pow3(Q)) {
                character_t ch0; char_make_mult_3r(&ch0, Q, 0);
                csr_t Ap; operator_info_t ip;
                if (rhg_build(&Ap, &ip, Q, c->L, c->R, c->bmax, s, &ch0, 1, c->height_mode) == 0) {
                    rho_principal = csr_spectral_radius_arnoldi(&Ap, ARN_M0, ARN_MMAX, ARN_TOL, NULL, NULL);
                    csr_free(&Ap);
                }
                char_free(&ch0);
            }
            fprintf(f, "%llu,%d,%d,%d,%.4Lf,trivial,0,%.10Lf,%.10Lf,1.0,%d,%.2Le,%.3Le,%zu,%d,%.10Lf,%.10Lf\n",
                (unsigned long long)Q, c->L, c->R, c->bmax, s, rho0, rho0, it0, res0,
                i0.trunc_tail, A0.nnz, i0.dim,
                rho_principal, rho_principal > 0 ? rho0/rho_principal : 0.0L);

            int phi_or_Q = is_pow3(Q) ? (int)(Q - Q/3) : (int)Q;
            /* char_cap<=0 => full character group; for 3^r use conjugate
             * symmetry (k=1..phi/2 covers all distinct gap magnitudes). */
            int kmax;
            if (c->char_cap <= 0) kmax = is_pow3(Q) ? phi_or_Q/2 : (phi_or_Q - 1);
            else { kmax = c->char_cap; if (kmax > phi_or_Q - 1) kmax = phi_or_Q - 1; }
            for (int k = 1; k <= kmax; k++) {
                character_t ch; const char *ctype;
                if (make_char(&ch, Q, (uint64_t)k, &ctype) != 0) continue;
                csr_t A; operator_info_t info;
                if (rhg_build(&A, &info, Q, c->L, c->R, c->bmax, s, &ch, 1, c->height_mode) != 0) {
                    char_free(&ch); continue;
                }
                ldbl res; int it;
                ldbl rho = csr_spectral_radius_arnoldi(&A, ARN_M0, ARN_MMAX, ARN_TOL, &res, &it);
                fprintf(f, "%llu,%d,%d,%d,%.4Lf,%s,%d,%.10Lf,%.10Lf,%.10Lf,%d,%.2Le,%.3Le,%zu,%d,%.10Lf,%.10Lf\n",
                    (unsigned long long)Q, c->L, c->R, c->bmax, s, ctype, k,
                    rho, rho0, rho0 > 0 ? rho/rho0 : 0.0L, it, res,
                    info.trunc_tail, A.nnz, info.dim,
                    rho_principal, rho_principal > 0 ? rho/rho_principal : 0.0L);
                csr_free(&A); char_free(&ch);
            }
            csr_free(&A0);
            fprintf(stderr, "[spectral-gaps] Q=%llu s=%.2Lf rho0=%.6Lf (dim=%d)\n",
                    (unsigned long long)Q, s, rho0, i0.dim);
        }
    }
    fclose(f);
    fprintf(stderr, "[spectral-gaps] wrote %s\n", path);
    return 0;
}
