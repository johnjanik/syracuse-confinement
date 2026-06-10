#include "sparse_matrix.h"
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <float.h>

void tri_init(triplets_t *t, int n) {
    t->n = n; t->cap = 1024; t->cnt = 0;
    t->row = malloc(t->cap * sizeof *t->row);
    t->col = malloc(t->cap * sizeof *t->col);
    t->val = malloc(t->cap * sizeof *t->val);
}
void tri_add(triplets_t *t, int row, int col, cldbl v) {
    if (t->cnt == t->cap) {
        t->cap *= 2;
        t->row = realloc(t->row, t->cap * sizeof *t->row);
        t->col = realloc(t->col, t->cap * sizeof *t->col);
        t->val = realloc(t->val, t->cap * sizeof *t->val);
    }
    t->row[t->cnt] = row; t->col[t->cnt] = col; t->val[t->cnt] = v; t->cnt++;
}
void tri_free(triplets_t *t) { free(t->row); free(t->col); free(t->val); memset(t,0,sizeof *t); }

csr_t csr_from_triplets(const triplets_t *t) {
    csr_t A; A.n = t->n; A.nnz = t->cnt;
    A.rowptr = calloc((size_t)t->n + 1, sizeof *A.rowptr);
    A.col = malloc(t->cnt * sizeof *A.col);
    A.val = malloc(t->cnt * sizeof *A.val);
    for (size_t i = 0; i < t->cnt; i++) A.rowptr[t->row[i] + 1]++;
    for (int r = 0; r < t->n; r++) A.rowptr[r+1] += A.rowptr[r];
    size_t *fill = malloc((size_t)t->n * sizeof *fill);
    for (int r = 0; r < t->n; r++) fill[r] = A.rowptr[r];
    for (size_t i = 0; i < t->cnt; i++) {
        int r = t->row[i]; size_t p = fill[r]++;
        A.col[p] = t->col[i]; A.val[p] = t->val[i];
    }
    free(fill);
    return A;
}
void csr_free(csr_t *A) { free(A->rowptr); free(A->col); free(A->val); memset(A,0,sizeof *A); }

void csr_spmv(const csr_t *A, const cldbl *x, cldbl *y) {
    for (int r = 0; r < A->n; r++) {
        cldbl s = 0;
        for (size_t p = A->rowptr[r]; p < A->rowptr[r+1]; p++) s += A->val[p] * x[A->col[p]];
        y[r] = s;
    }
}
void csr_spmv_herm(const csr_t *A, const cldbl *x, cldbl *y) {
    for (int r = 0; r < A->n; r++) y[r] = 0;
    for (int r = 0; r < A->n; r++)
        for (size_t p = A->rowptr[r]; p < A->rowptr[r+1]; p++)
            y[A->col[p]] += conjl(A->val[p]) * x[r];
}

static ldbl vnorm(const cldbl *x, int n) {
    ldbl s = 0; for (int i = 0; i < n; i++) s += creall(x[i]*conjl(x[i]));
    return sqrtl(s);
}

ldbl csr_spectral_radius(const csr_t *A, int max_iter, ldbl tol,
                         int restarts, ldbl *residual, int *iters_used) {
    int n = A->n;
    cldbl *x = malloc((size_t)n * sizeof *x);
    cldbl *y = malloc((size_t)n * sizeof *y);
    ldbl best = 0.0L; ldbl best_res = 1.0L; int best_it = 0;
    if (restarts < 1) restarts = 1;
    for (int rs = 0; rs < restarts; rs++) {
        /* deterministic but restart-varied init */
        for (int i = 0; i < n; i++) {
            ldbl a = (ldbl)((i * 2654435761u + (unsigned)rs * 40503u) % 1000) / 1000.0L + 0.1L;
            ldbl b = (ldbl)((i * 1597334677u + (unsigned)rs * 22277u) % 1000) / 1000.0L;
            x[i] = a + b * I;
        }
        ldbl nrm = vnorm(x, n); for (int i = 0; i < n; i++) x[i] /= nrm;
        ldbl rho = 0.0L, prev = 0.0L, res = 1.0L; int it;
        for (it = 0; it < max_iter; it++) {
            csr_spmv(A, x, y);
            rho = vnorm(y, n);
            if (rho == 0.0L) break;
            for (int i = 0; i < n; i++) x[i] = y[i] / rho;
            res = prev > 0 ? fabsl(rho - prev) / prev : 1.0L;
            if (res < tol) { it++; break; }
            prev = rho;
        }
        if (rho > best) { best = rho; best_res = res; best_it = it; }
    }
    free(x); free(y);
    if (residual) *residual = best_res;
    if (iters_used) *iters_used = best_it;
    return best;
}

/* ============================ Arnoldi eigensolver ======================= */

/* Complex Givens: c (real>=0), s such that the unitary R=[[c,s],[-conj(s),c]]
 * sends [a;b] -> [r;0]. */
static void cgivens(cldbl a, cldbl b, ldbl *c, cldbl *s) {
    ldbl aa = cabsl(a), bb = cabsl(b);
    if (bb == 0.0L) { *c = 1.0L; *s = 0.0L; return; }
    if (aa == 0.0L) { *c = 0.0L; *s = conjl(b) / bb; return; }
    ldbl r = hypotl(aa, bb);
    *c = aa / r;
    *s = (*c) * conjl(b) / conjl(a);
}

/* One single-shift QR sweep on the active Hessenberg block [lo..hi]
 * (stride N), shift mu. Preserves the eigenvalues (unitary similarity). */
static void qr_step(cldbl *H, int N, int lo, int hi, cldbl mu) {
    int nb = hi - lo;                 /* number of rotations */
    ldbl  *cc = malloc((size_t)nb * sizeof *cc);
    cldbl *ss = malloc((size_t)nb * sizeof *ss);
    for (int i = lo; i <= hi; i++) H[i*N + i] -= mu;
    /* QR: left rotations make the block upper triangular */
    for (int k = lo; k < hi; k++) {
        ldbl c; cldbl s;
        cgivens(H[k*N+k], H[(k+1)*N+k], &c, &s);
        cc[k-lo] = c; ss[k-lo] = s;
        for (int j = k; j <= hi; j++) {
            cldbl t1 = H[k*N+j], t2 = H[(k+1)*N+j];
            H[k*N+j]     =  c*t1 + s*t2;
            H[(k+1)*N+j] = -conjl(s)*t1 + c*t2;
        }
        H[(k+1)*N+k] = 0.0L;
    }
    /* RQ: apply the rotations from the right */
    for (int k = lo; k < hi; k++) {
        ldbl c = cc[k-lo]; cldbl s = ss[k-lo];
        int top = (k+2 < hi) ? k+2 : hi;
        for (int i = lo; i <= top; i++) {
            cldbl t1 = H[i*N+k], t2 = H[i*N+(k+1)];
            H[i*N+k]     =  c*t1 + conjl(s)*t2;
            H[i*N+(k+1)] = -s*t1 + c*t2;
        }
    }
    for (int i = lo; i <= hi; i++) H[i*N + i] += mu;
    free(cc); free(ss);
}

/* Eigenvalues of the leading mm x mm block of an upper-Hessenberg matrix Hin
 * (stride N). Shifted QR with Wilkinson shift + deflation. */
static void hess_qr_eig(const cldbl *Hin, int N, int mm, cldbl *eig) {
    if (mm <= 0) return;
    cldbl *H = malloc((size_t)mm*mm * sizeof *H);
    for (int i = 0; i < mm; i++)
        for (int j = 0; j < mm; j++) H[i*mm+j] = Hin[i*N+j];
    int hi = mm - 1, iter = 0, maxiter = 80*mm + 200;
    while (hi >= 0 && iter < maxiter) {
        if (hi == 0) { eig[0] = H[0]; hi = -1; break; }
        int lo = hi;
        while (lo > 0) {
            ldbl sub = cabsl(H[lo*mm + (lo-1)]);
            ldbl dia = cabsl(H[(lo-1)*mm + (lo-1)]) + cabsl(H[lo*mm + lo]);
            if (sub <= LDBL_EPSILON * dia) { H[lo*mm + (lo-1)] = 0.0L; break; }
            lo--;
        }
        if (lo == hi) { eig[hi] = H[hi*mm + hi]; hi--; iter = 0; continue; }
        /* Wilkinson shift from trailing 2x2 of [lo..hi] */
        cldbl a = H[(hi-1)*mm + (hi-1)], b = H[(hi-1)*mm + hi];
        cldbl cc = H[hi*mm + (hi-1)],    d = H[hi*mm + hi];
        cldbl tr = a + d, det = a*d - b*cc;
        cldbl disc = csqrtl(tr*tr - 4.0L*det);
        cldbl l1 = (tr + disc) / 2.0L, l2 = (tr - disc) / 2.0L;
        cldbl mu = (cabsl(l1 - d) < cabsl(l2 - d)) ? l1 : l2;
        qr_step(H, mm, lo, hi, mu);
        iter++;
    }
    for (int i = 0; i <= hi; i++) eig[i] = H[i*mm + i];  /* if iter cap hit */
    free(H);
}

static cldbl cdot(const cldbl *a, const cldbl *b, int n) {   /* <a,b> = sum conj(a)b */
    cldbl s = 0; for (int i = 0; i < n; i++) s += conjl(a[i]) * b[i]; return s;
}

/* dominant Ritz value magnitude from an m-step Arnoldi factorization. */
static ldbl arnoldi_dom(const csr_t *A, int m) {
    int n = A->n;
    cldbl *V = malloc((size_t)n * (m+1) * sizeof *V);
    cldbl *H = calloc((size_t)m * m, sizeof *H);
    cldbl *w = malloc((size_t)n * sizeof *w);
    cldbl *eig = malloc((size_t)m * sizeof *eig);

    for (int i = 0; i < n; i++) {
        ldbl re = (ldbl)((i*2654435761u + 12345u) % 1000)/1000.0L + 0.1L;
        ldbl im = (ldbl)((i*40503u + 7u) % 1000)/1000.0L;
        V[i] = re + im*I;
    }
    ldbl nrm = sqrtl(creall(cdot(V, V, n))); for (int i = 0; i < n; i++) V[i] /= nrm;

    int mm = m;
    for (int j = 0; j < m; j++) {
        csr_spmv(A, V + (size_t)j*n, w);
        for (int reo = 0; reo < 2; reo++)            /* MGS + 1 reorthogonalization */
            for (int i = 0; i <= j; i++) {
                cldbl hij = cdot(V + (size_t)i*n, w, n);
                H[i*m + j] += hij;
                for (int t = 0; t < n; t++) w[t] -= hij * V[(size_t)i*n + t];
            }
        ldbl hnext = sqrtl(creall(cdot(w, w, n)));
        if (hnext <= 1e-14L) { mm = j + 1; break; }  /* invariant subspace */
        if (j + 1 < m) {
            for (int t = 0; t < n; t++) V[(size_t)(j+1)*n + t] = w[t] / hnext;
            H[(j+1)*m + j] = hnext;
        }
    }
    hess_qr_eig(H, m, mm, eig);
    ldbl best = 0; for (int i = 0; i < mm; i++) { ldbl a = cabsl(eig[i]); if (a > best) best = a; }

    free(V); free(H); free(w); free(eig);
    return best;
}

ldbl csr_spectral_radius_arnoldi(const csr_t *A, int m_start, int m_max,
                                 ldbl tol, ldbl *residual, int *m_used) {
    int cap = A->n;                 /* m = n gives full (exact) Arnoldi */
    if (m_max > cap) m_max = cap;
    if (m_start > m_max) m_start = m_max;
    if (m_start < 1) m_start = 1;
    ldbl prev = -1.0L, rho = 0.0L, res = 1.0L;
    int m = m_start;
    for (;;) {
        rho = arnoldi_dom(A, m);
        if (prev >= 0.0L) {
            res = rho > 0 ? fabsl(rho - prev) / rho : fabsl(rho - prev);
            if (res < tol) break;
        }
        prev = rho;
        if (m >= m_max) break;
        m += m_start; if (m > m_max) m = m_max;
    }
    if (residual) *residual = res;
    if (m_used) *m_used = m;
    return rho;
}

ldbl csr_singular_max(const csr_t *A, int max_iter, ldbl tol) {
    int n = A->n;
    cldbl *x = malloc((size_t)n * sizeof *x);
    cldbl *y = malloc((size_t)n * sizeof *y);
    cldbl *z = malloc((size_t)n * sizeof *z);
    for (int i = 0; i < n; i++) x[i] = 1.0L + 0.0L * I;
    ldbl nrm = vnorm(x, n); for (int i = 0; i < n; i++) x[i] /= nrm;
    ldbl s2 = 0, prev = 0;
    for (int it = 0; it < max_iter; it++) {
        csr_spmv(A, x, y);       /* y = A x      */
        csr_spmv_herm(A, y, z);  /* z = A^* A x  */
        s2 = vnorm(z, n);
        if (s2 == 0) break;
        for (int i = 0; i < n; i++) x[i] = z[i] / s2;
        if (prev > 0 && fabsl(s2 - prev)/prev < tol) break;
        prev = s2;
    }
    free(x); free(y); free(z);
    return sqrtl(s2);  /* sigma_max */
}
