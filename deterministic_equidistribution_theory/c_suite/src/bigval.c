/* bigval.c — FAST128 and GMP backends for the orbit's true value. */
#include "bigval.h"
#include <math.h>

#ifdef USE_GMP
/* ----------------------------- GMP backend ----------------------------- */

void bv_init_u64(bigval_t *x, uint64_t seed) { mpz_init_set_ui(x->v, seed); }
void bv_clear(bigval_t *x) { mpz_clear(x->v); }
void bv_set(bigval_t *dst, const bigval_t *src) { mpz_set(dst->v, src->v); }

step_meta_t bv_syracuse_step(bigval_t *x) {
    step_meta_t m = {0, 0};
    /* y = 3x + 1 */
    mpz_mul_ui(x->v, x->v, 3u);
    mpz_add_ui(x->v, x->v, 1u);
    /* b = v2(y); divide out */
    m.b = (uint32_t)mpz_scan1(x->v, 0);      /* index of lowest set bit */
    mpz_tdiv_q_2exp(x->v, x->v, m.b);
    return m;
}

uint64_t bv_mod_u64(const bigval_t *x, uint64_t mod) {
    return (uint64_t)mpz_fdiv_ui((mpz_srcptr)x->v, mod);
}
int bv_is_one(const bigval_t *x) { return mpz_cmp_ui(x->v, 1u) == 0; }
int bv_cmp(const bigval_t *a, const bigval_t *b) { return mpz_cmp(a->v, b->v); }
ldbl bv_log2(const bigval_t *x) {
    signed long e; double d = mpz_get_d_2exp(&e, x->v);
    return (ldbl)log2(d) + (ldbl)e;
}
int bv_overflowed(const bigval_t *x) { (void)x; return 0; }
void bv_to_decimal(const bigval_t *x, char *buf, size_t n) {
    gmp_snprintf(buf, n, "%Zd", x->v);
}
int bv_is_A_critical(const bigval_t *V, const bigval_t *P, int A) {
    mpz_t lhs, rhs; mpz_init(lhs); mpz_init(rhs);
    mpz_mul(lhs, V->v, V->v);          /* V^2          */
    mpz_mul_2exp(rhs, P->v, (mp_bitcnt_t)A); /* 2^A * P */
    int r = mpz_cmp(lhs, rhs) <= 0 ? 1 : 0;
    mpz_clear(lhs); mpz_clear(rhs);
    return r;
}
int bv_geq_shl(const bigval_t *P, const bigval_t *V, int A) {
    mpz_t rhs; mpz_init(rhs);
    mpz_mul_2exp(rhs, V->v, (mp_bitcnt_t)A);  /* V << A */
    int r = mpz_cmp(P->v, rhs) >= 0 ? 1 : 0;
    mpz_clear(rhs);
    return r;
}

#else
/* --------------------------- FAST128 backend --------------------------- */

void bv_init_u64(bigval_t *x, uint64_t seed) { x->v = seed; x->overflow = 0; }
void bv_clear(bigval_t *x) { (void)x; }
void bv_set(bigval_t *dst, const bigval_t *src) { *dst = *src; }

/* count trailing zeros of a 128-bit value (assumes nonzero). */
static uint32_t ctz128(__uint128_t y) {
    uint64_t lo = (uint64_t)y;
    if (lo) return (uint32_t)__builtin_ctzll(lo);
    uint64_t hi = (uint64_t)(y >> 64);
    return 64u + (uint32_t)__builtin_ctzll(hi);
}

step_meta_t bv_syracuse_step(bigval_t *x) {
    step_meta_t m = {0, 0};
    if (x->overflow) { m.overflow = 1; return m; }
    __uint128_t v = x->v;
    /* overflow guard: 3v+1 must fit in 128 bits. */
    if (v > (((__uint128_t)-1) - 1) / 3) {
        x->overflow = 1; m.overflow = 1; return m;
    }
    __uint128_t y = 3 * v + 1;
    m.b = ctz128(y);
    x->v = y >> m.b;
    return m;
}

uint64_t bv_mod_u64(const bigval_t *x, uint64_t mod) {
    return (uint64_t)(x->v % (__uint128_t)mod);
}
int bv_is_one(const bigval_t *x) { return x->v == 1; }
int bv_cmp(const bigval_t *a, const bigval_t *b) {
    if (a->v < b->v) return -1;
    if (a->v > b->v) return 1;
    return 0;
}
ldbl bv_log2(const bigval_t *x) {
    __uint128_t v = x->v;
    if (v == 0) return -1.0L/0.0L; /* -inf */
    /* split into high/low 64-bit halves for precision */
    uint64_t hi = (uint64_t)(v >> 64);
    if (hi) return 64.0L + log2l((ldbl)hi + (ldbl)((uint64_t)v) / 18446744073709551616.0L);
    return log2l((ldbl)(uint64_t)v);
}
int bv_overflowed(const bigval_t *x) { return x->overflow; }

void bv_to_decimal(const bigval_t *x, char *buf, size_t n) {
    /* decimal print of a 128-bit value (no native printf support). */
    char tmp[40]; int ti = 0;
    __uint128_t v = x->v;
    if (v == 0) { if (n) buf[0] = '0', buf[1] = '\0'; return; }
    while (v > 0 && ti < (int)sizeof tmp) { tmp[ti++] = (char)('0' + (int)(v % 10)); v /= 10; }
    size_t bi = 0;
    while (ti > 0 && bi + 1 < n) buf[bi++] = tmp[--ti];
    if (bi < n) buf[bi] = '\0';
}

int bv_is_A_critical(const bigval_t *V, const bigval_t *P, int A) {
    if (V->overflow || P->overflow) return -1;
    __uint128_t v = V->v, p = P->v;
    if (v >> 64) return -1;                 /* V^2 would overflow 128 bits */
    __uint128_t lhs = v * v;                /* < 2^128, exact             */
    __uint128_t maxp = (~(__uint128_t)0) >> A;
    if (p > maxp) return 1;                 /* 2^A * P overflows => huge >= lhs */
    return lhs <= (p << A) ? 1 : 0;
}

int bv_geq_shl(const bigval_t *P, const bigval_t *V, int A) {
    if (V->overflow || P->overflow) return -1;
    __uint128_t v = V->v, p = P->v;
    __uint128_t maxv = (~(__uint128_t)0) >> A;
    if (v > maxv) return (bv_cmp(P, V) >= 0) ? -1 : 0; /* V<<A overflows */
    return p >= (v << A) ? 1 : 0;
}

#endif
