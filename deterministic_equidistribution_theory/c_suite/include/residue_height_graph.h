/* residue_height_graph.h — build the finite killed residue-height operator
 * L_{s,Q,L,chi} as a complex CSR matrix (spec Section "Experiment E").
 *
 * State space X_{Q,L} = {(a,z): a in 0..Q-1, z in 0..L}.  Matrix entry
 * M[(a',z'),(a,z)] += w_s(b) * chi(a) for each admissible valuation b<=Bmax,
 * where  w_s(b) = 2^{-b} 2^{s(log2 3 - b)}  and the residue transition is
 *   forward  (Q odd):           a' = (3a+1) 2^{-b}        (mod Q)   [2 invertible]
 *   inverse  (gcd(3,Q)=1, Q even): a' = 3^{-1}(2^b a - 1) (mod Q)   [3 invertible]
 * Height update z' = z + round(R*(log2 3 - b)); edges with z' notin [0,L] are
 * killed.  use_height=0 collapses the height coordinate (residue-only operator,
 * used by the Fourier comparison Experiment F).
 *
 * chi == NULL is the trivial sector.  The character multiplies the SOURCE
 * residue a; this convention is recorded in output metadata.
 */
#ifndef AIPM_RESIDUE_HEIGHT_GRAPH_H
#define AIPM_RESIDUE_HEIGHT_GRAPH_H

#include <stdint.h>
#include "sparse_matrix.h"
#include "characters.h"

/* Height-coupling mode (how the height coordinate relates to the character):
 *   RHG_SYNC     : a single valuation b drives BOTH the residue transition and
 *                  the height increment (the faithful skew product). The
 *                  quadratic character is then a height-coboundary -> kappa_Q=0.
 *   RHG_FACTORED : the height contributes a residue-independent survival factor
 *                  (Kronecker product L_res(chi) (x) T_height); the character
 *                  twists only the residue factor, so the killed operator
 *                  inherits the residue-sector gap (gaps every character). */
typedef enum { RHG_SYNC = 0, RHG_FACTORED = 1 } rhg_height_mode_t;

typedef struct {
    uint64_t Q; int L, R, Bmax; ldbl s;
    int   use_height;
    int   height_mode;    /* rhg_height_mode_t                    */
    int   dim;            /* matrix dimension                    */
    size_t nnz;
    ldbl  trunc_tail;     /* 2^{-Bmax}: ignored valuation mass    */
    int   map_mode;       /* 0 forward, 1 inverse                 */
} operator_info_t;

/* Build the operator. Returns 0 ok, 1 if Q has both factors 2 and 3 (unsupported).
 * height_mode is ignored when use_height==0. */
int rhg_build(csr_t *out, operator_info_t *info,
              uint64_t Q, int L, int R, int Bmax, ldbl s,
              const character_t *chi, int use_height, int height_mode);

#endif /* AIPM_RESIDUE_HEIGHT_GRAPH_H */
