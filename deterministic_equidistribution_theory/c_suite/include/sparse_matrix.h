/* sparse_matrix.h — CSR complex matrices + iterative spectral estimates.
 * Spec Section "Module Architecture / sparse_matrix" and "Experiment E". */
#ifndef AIPM_SPARSE_MATRIX_H
#define AIPM_SPARSE_MATRIX_H

#include <stddef.h>
#include "common.h"

/* triplet accumulator (row, col, val); duplicates are allowed and summed by spmv. */
typedef struct {
    int    n;            /* matrix dimension */
    size_t cap, cnt;
    int   *row, *col;
    cldbl *val;
} triplets_t;

void tri_init(triplets_t *t, int n);
void tri_add(triplets_t *t, int row, int col, cldbl v);
void tri_free(triplets_t *t);

/* compressed sparse row */
typedef struct {
    int    n;
    size_t nnz;
    size_t *rowptr;      /* n+1 */
    int    *col;         /* nnz  */
    cldbl  *val;         /* nnz  */
} csr_t;

csr_t csr_from_triplets(const triplets_t *t);
void  csr_free(csr_t *A);
void  csr_spmv(const csr_t *A, const cldbl *x, cldbl *y);     /* y = A x      */
void  csr_spmv_herm(const csr_t *A, const cldbl *x, cldbl *y);/* y = A^* x    */

/* dominant eigenvalue magnitude via power iteration with random restarts.
 * Returns |lambda_max|; writes the achieved relative change to *residual.
 * NOTE: unreliable when the top eigenvalues form a near-degenerate cluster
 * (e.g. the killed residue-height operator). Use the Arnoldi solver there. */
ldbl  csr_spectral_radius(const csr_t *A, int max_iter, ldbl tol,
                          int restarts, ldbl *residual, int *iters_used);

/* Spectral radius via restarted Arnoldi: build a Krylov subspace, take the
 * dominant Ritz value (eigenvalue of the m x m Hessenberg). Resolves clustered
 * top eigenvalues that defeat power iteration. The Krylov dimension grows by
 * `m_start` until the dominant Ritz value stabilizes (relative change < tol) or
 * `m_max` (clamped to n-1) is reached. Writes the final relative change to
 * *residual and the Krylov dimension used to *m_used. */
ldbl  csr_spectral_radius_arnoldi(const csr_t *A, int m_start, int m_max,
                                  ldbl tol, ldbl *residual, int *m_used);

/* largest singular value (power iteration on A^*A); an upper bound on rho. */
ldbl  csr_singular_max(const csr_t *A, int max_iter, ldbl tol);

#endif /* AIPM_SPARSE_MATRIX_H */
