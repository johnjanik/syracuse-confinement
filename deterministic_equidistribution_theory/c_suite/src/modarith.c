#include "modarith.h"

uint64_t ma_gcd(uint64_t a, uint64_t b) {
    while (b) { uint64_t t = a % b; a = b; b = t; }
    return a;
}

uint64_t ma_ipow(uint64_t base, uint64_t exp) {
    uint64_t r = 1;
    while (exp) { if (exp & 1u) r *= base; base *= base; exp >>= 1; }
    return r;
}

uint64_t ma_mulmod(uint64_t a, uint64_t b, uint64_t m) {
    return (uint64_t)(((__uint128_t)a * (__uint128_t)b) % (__uint128_t)m);
}

uint64_t ma_powmod(uint64_t base, uint64_t exp, uint64_t m) {
    uint64_t r = 1 % m; base %= m;
    while (exp) {
        if (exp & 1u) r = ma_mulmod(r, base, m);
        base = ma_mulmod(base, base, m);
        exp >>= 1;
    }
    return r;
}

/* extended Euclid: returns a^{-1} mod m, or 0 if gcd(a,m) != 1. */
uint64_t ma_inv(uint64_t a, uint64_t m) {
    if (m == 1) return 0;
    int64_t t = 0, newt = 1;
    int64_t r = (int64_t)m, newr = (int64_t)(a % m);
    while (newr != 0) {
        int64_t q = r / newr;
        int64_t tmp = t - q * newt; t = newt; newt = tmp;
        tmp = r - q * newr;        r = newr; newr = tmp;
    }
    if (r != 1) return 0;           /* not invertible */
    if (t < 0) t += (int64_t)m;
    return (uint64_t)t;
}
