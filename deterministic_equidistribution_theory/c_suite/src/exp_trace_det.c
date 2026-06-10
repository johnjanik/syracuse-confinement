/* exp_trace_det.c — Experiment G: finite trace & determinant shadows.
 *
 * For small (Q,L) operators, compute tr(L^n) and the Fredholm-style
 * determinant Xi(z,s) = det(1 - z L_{s,Q,L,chi}) at selected z, to see whether
 * closed-walk data carry unexpected peripheral structure (spec Section
 * "Experiment G"). Dense path (LU) for small dimension.
 */
#include "experiments.h"
#include "residue_height_graph.h"
#include "io_csv.h"
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#define G_DIM_CAP 700      /* dense O(dim^3) det; keep modest */
#define G_NMAX    8         /* traces tr(L^n), n=1..G_NMAX     */

static int is_pow3(uint64_t Q){ if(Q%2==0)return 0; while(Q%3==0)Q/=3; return Q==1; }

/* dense matrix from CSR (row-major). */
static cldbl *dense_from_csr(const csr_t *A) {
    cldbl *M = calloc((size_t)A->n * A->n, sizeof *M);
    for (int r = 0; r < A->n; r++)
        for (size_t p = A->rowptr[r]; p < A->rowptr[r+1]; p++)
            M[(size_t)r * A->n + A->col[p]] += A->val[p];
    return M;
}

/* det(I - z*M) via complex LU with partial pivoting; M is n x n row-major. */
static cldbl det_I_minus_zM(const cldbl *M, int n, cldbl z) {
    cldbl *B = malloc((size_t)n * n * sizeof *B);
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
            B[(size_t)i*n+j] = (i==j ? 1.0L : 0.0L) - z * M[(size_t)i*n+j];
    cldbl det = 1.0L; int sign = 1;
    for (int k = 0; k < n; k++) {
        int piv = k; ldbl best = cabsl(B[(size_t)k*n+k]);
        for (int i = k+1; i < n; i++) { ldbl m = cabsl(B[(size_t)i*n+k]); if (m > best){best=m;piv=i;} }
        if (best == 0.0L) { free(B); return 0.0L; }
        if (piv != k) { sign = -sign;
            for (int j = 0; j < n; j++) { cldbl t=B[(size_t)k*n+j]; B[(size_t)k*n+j]=B[(size_t)piv*n+j]; B[(size_t)piv*n+j]=t; } }
        cldbl pivval = B[(size_t)k*n+k];
        det *= pivval;
        for (int i = k+1; i < n; i++) {
            cldbl f = B[(size_t)i*n+k] / pivval;
            for (int j = k; j < n; j++) B[(size_t)i*n+j] -= f * B[(size_t)k*n+j];
        }
    }
    free(B);
    return (sign < 0) ? -det : det;
}

int exp_trace_det(const config_t *c, int argc, char **argv) {
    char path[512];
    snprintf(path, sizeof path, "%s/trace_determinant.csv", c->output_dir);
    FILE *f = csv_open(path, "trace_determinant",
        "Q,L,s,char_index,n,trace_real,trace_imag,trace_abs,"
        "determinant_real,determinant_imag,z_real,z_imag", argc, argv);
    if (!f) { perror("csv_open"); return 1; }

    const ldbl zvals[] = {0.25L, 0.5L, 0.75L, 1.0L};

    for (int qi = 0; qi < c->n_moduli; qi++) {
        uint64_t Q = c->moduli[qi];
        for (int ti = 0; ti < c->n_tilts; ti++) {
            ldbl s = c->tilts[ti];
            /* trivial (k=0) then a few characters */
            int kmax = c->char_cap;
            for (int k = 0; k <= kmax; k++) {
                character_t ch; int have_char = 0;
                if (k >= 1) {
                    if (is_pow3(Q)) { if (char_make_mult_3r(&ch,Q,(uint64_t)k)==0) have_char=1; }
                    else            { if (char_make_additive(&ch,Q,(uint64_t)k)==0) have_char=1; }
                    if (!have_char) continue;
                }
                csr_t A; operator_info_t info;
                int rc = rhg_build(&A, &info, Q, c->L, c->R, c->bmax, s,
                                   have_char ? &ch : NULL, 1, c->height_mode);
                if (rc != 0) { if (have_char) char_free(&ch); break; }
                if (A.n > G_DIM_CAP) {
                    fprintf(stderr, "[trace-det] Q=%llu dim=%d > cap %d, skipped\n",
                            (unsigned long long)Q, A.n, G_DIM_CAP);
                    csr_free(&A); if (have_char) char_free(&ch); continue;
                }
                cldbl *M = dense_from_csr(&A);
                /* traces of powers: maintain P = M^n via dense mult */
                cldbl *P = malloc((size_t)A.n*A.n*sizeof *P);
                cldbl *T = malloc((size_t)A.n*A.n*sizeof *T);
                for (int i=0;i<A.n*A.n;i++) P[i]=M[i];
                for (int npow = 1; npow <= G_NMAX; npow++) {
                    cldbl tr = 0; for (int i=0;i<A.n;i++) tr += P[(size_t)i*A.n+i];
                    fprintf(f, "%llu,%d,%.4Lf,%d,%d,%.6Le,%.6Le,%.6Le,,,,\n",
                        (unsigned long long)Q, c->L, s, k, npow,
                        creall(tr), cimagl(tr), cabsl(tr));
                    if (npow < G_NMAX) { /* P = P*M */
                        for (int i=0;i<A.n;i++) for (int j=0;j<A.n;j++){
                            cldbl acc=0; for(int l=0;l<A.n;l++) acc+=P[(size_t)i*A.n+l]*M[(size_t)l*A.n+j];
                            T[(size_t)i*A.n+j]=acc;
                        }
                        cldbl *tmp=P; P=T; T=tmp;
                    }
                }
                for (size_t zi=0; zi<sizeof zvals/sizeof zvals[0]; zi++) {
                    cldbl z = zvals[zi];
                    cldbl det = det_I_minus_zM(M, A.n, z);
                    fprintf(f, "%llu,%d,%.4Lf,%d,0,,,,%.6Le,%.6Le,%.4Lf,0.0\n",
                        (unsigned long long)Q, c->L, s, k,
                        creall(det), cimagl(det), zvals[zi]);
                }
                free(M); free(P); free(T);
                csr_free(&A); if (have_char) char_free(&ch);
            }
        }
        fprintf(stderr, "[trace-det] Q=%llu done\n", (unsigned long long)Q);
    }
    fclose(f);
    fprintf(stderr, "[trace-det] wrote %s\n", path);
    return 0;
}
