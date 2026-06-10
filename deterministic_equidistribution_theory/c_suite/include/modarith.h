/* modarith.h — small modular-integer helpers (exact, no floating point).
 * Used by Experiment H (mod 3^r congruence) and the residue-height graph. */
#ifndef AIPM_MODARITH_H
#define AIPM_MODARITH_H

#include <stdint.h>

uint64_t ma_gcd(uint64_t a, uint64_t b);
uint64_t ma_ipow(uint64_t base, uint64_t exp);            /* base^exp, no mod  */
uint64_t ma_mulmod(uint64_t a, uint64_t b, uint64_t m);   /* a*b mod m, 128-bit*/
uint64_t ma_powmod(uint64_t base, uint64_t exp, uint64_t m);
/* modular inverse of a mod m (m,a coprime), via extended Euclid; 0 if none. */
uint64_t ma_inv(uint64_t a, uint64_t m);

#endif /* AIPM_MODARITH_H */
