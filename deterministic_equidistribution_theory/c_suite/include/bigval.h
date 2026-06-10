/* bigval.h — the orbit's "true value" abstraction.
 *
 * Only collatz_core needs arbitrary-precision integers: the accelerated step
 * x -> (3x+1)/2^b is NOT closed modulo any 2^k (the division shifts in unknown
 * high bits), so to recover the exact valuation word b_0,b_1,... of a long
 * orbit we must carry the full integer. Everything downstream (residues,
 * windows, valuations) is small once b_i is known.
 *
 * Two backends behind one API, selected at compile time:
 *   default  : __uint128_t, with an overflow flag (FAST128 profile).
 *   -DUSE_GMP: mpz_t (no overflow; for large seeds / long orbits / Exp H).
 */
#ifndef AIPM_BIGVAL_H
#define AIPM_BIGVAL_H

#include "common.h"

#ifdef USE_GMP
#include <gmp.h>
typedef struct { mpz_t v; } bigval_t;
#else
typedef struct { __uint128_t v; int overflow; } bigval_t;
#endif

void     bv_init_u64(bigval_t *x, uint64_t seed);
void     bv_clear(bigval_t *x);
void     bv_set(bigval_t *dst, const bigval_t *src);

/* Accelerated odd step in place: x <- (3x+1)/2^b. Returns b and overflow. */
step_meta_t bv_syracuse_step(bigval_t *x);

/* x mod m  (m a 64-bit modulus, e.g. 3^r). */
uint64_t bv_mod_u64(const bigval_t *x, uint64_t m);

int      bv_is_one(const bigval_t *x);
int      bv_cmp(const bigval_t *a, const bigval_t *b); /* -1,0,1 */
/* approximate log2 of x, for height diagnostics only (never a predicate). */
ldbl     bv_log2(const bigval_t *x);
int      bv_overflowed(const bigval_t *x);             /* always 0 under GMP */

/* decimal string of x into buf (truncated to n). For CSV value columns. */
void     bv_to_decimal(const bigval_t *x, char *buf, size_t n);

/* Exact criticality predicates (no floating point), per spec Section
 * "Numerical precision". Return 1 (true), 0 (false), or -1 (undecidable:
 * FAST128 input already overflowed; rerun under GMP). */
int      bv_is_A_critical(const bigval_t *V, const bigval_t *P, int A); /* V^2 <= 2^A P */
int      bv_geq_shl(const bigval_t *P, const bigval_t *V, int A);       /* P >= V<<A    */

#endif /* AIPM_BIGVAL_H */
