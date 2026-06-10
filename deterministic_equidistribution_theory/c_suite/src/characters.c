#include "characters.h"
#include "modarith.h"
#include <stdlib.h>
#include <math.h>

#ifndef M_PIl
#define M_PIl 3.141592653589793238462643383279502884L
#endif

int char_make_additive(character_t *ch, uint64_t Q, uint64_t k) {
    ch->type = CHAR_ADDITIVE; ch->Q = Q; ch->k = k;
    ch->table = malloc(Q * sizeof *ch->table);
    if (!ch->table) return 1;
    for (uint64_t a = 0; a < Q; a++) {
        ldbl theta = 2.0L * M_PIl * (ldbl)((k * a) % Q) / (ldbl)Q;
        ch->table[a] = cosl(theta) + I * sinl(theta);
    }
    return 0;
}

int char_make_mult_3r(character_t *ch, uint64_t Q, uint64_t k) {
    ch->type = CHAR_MULT_3R; ch->Q = Q; ch->k = k;
    ch->table = malloc(Q * sizeof *ch->table);
    if (!ch->table) return 1;
    /* phi(3^r) = 2*3^{r-1}; 2 is a primitive root, so discrete-log base 2. */
    uint64_t phi = Q - Q / 3;                 /* 3^r - 3^{r-1} */
    /* build discrete log table: dlog[2^j mod Q] = j */
    for (uint64_t a = 0; a < Q; a++) ch->table[a] = 0; /* non-units stay 0 */
    uint64_t pw = 1;
    for (uint64_t j = 0; j < phi; j++) {
        ldbl theta = 2.0L * M_PIl * (ldbl)((k * j) % phi) / (ldbl)phi;
        ch->table[pw] = cosl(theta) + I * sinl(theta);
        pw = ma_mulmod(pw, 2, Q);
    }
    return 0;
}

void char_free(character_t *ch) { free(ch->table); ch->table = NULL; }
