/* common.h — shared types, build-profile macros, math constants.
 *
 * Build profiles (mutually exclusive numeric backend; DEBUG is orthogonal):
 *   FAST128 (default) : __uint128_t orbit values, overflow-flagged.
 *   GMP     (-DUSE_GMP): mpz_t orbit values, no overflow.
 *   DEBUG   (-DAIPM_DEBUG): enables invariant assertions in collatz_core.
 *
 * Spec: collatz_defect_cocycle_c_specs.tex Section "Implementation Language".
 */
#ifndef AIPM_COMMON_H
#define AIPM_COMMON_H

#include <stdint.h>
#include <stddef.h>
#include <complex.h>

/* log2(3): the annealed equilibrium mean valuation. High precision constant. */
#define LOG2_3   1.5849625007211561814537389439478165087598144076924L
/* H_2(3/4) = -(3/4)log2(3/4) - (1/4)log2(1/4): critical bulk dimension (Exp B). */
#define H2_THREE_QUARTERS  0.8112781244591328L

typedef long double ldbl;
typedef long double _Complex cldbl;

/* A single accelerated Syracuse step result. */
typedef struct {
    uint32_t b;        /* b = v2(3x+1)                      */
    int      overflow; /* set if 3x+1 exceeded the backend  */
} step_meta_t;

#endif /* AIPM_COMMON_H */
