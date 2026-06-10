/* characters.h — finite residue characters modulo Q.
 *
 * Spec Section "Experiment C / Characters":
 *   (1) additive characters chi_k(a) = exp(2 pi i k a / Q), 1 <= k < Q;
 *   (2) multiplicative unit characters for Q = 3^r (units are cyclic, gen 2);
 *   (3) product characters for Q = 2^a 3^r via CRT  (built on the above).
 *
 * A character is materialized as a lookup table over residues 0..Q-1 so that
 * evaluating chi(x_i mod Q) along an orbit is a single array read.
 */
#ifndef AIPM_CHARACTERS_H
#define AIPM_CHARACTERS_H

#include <stdint.h>
#include "common.h"

typedef enum { CHAR_ADDITIVE = 0, CHAR_MULT_3R = 1 } char_type_t;

typedef struct {
    char_type_t type;
    uint64_t    Q;
    uint64_t    k;        /* additive frequency, or mult-character index */
    cldbl      *table;    /* table[a] = chi(a), a in 0..Q-1 */
} character_t;

/* additive: chi_k(a) = e(k a / Q). */
int  char_make_additive(character_t *ch, uint64_t Q, uint64_t k);
/* multiplicative on (Z/3^r)^*: chi(2^j) = e(k j / phi), phi = 2*3^{r-1};
 * chi(a) = 0 on non-units. Requires Q = 3^r. */
int  char_make_mult_3r(character_t *ch, uint64_t Q, uint64_t k);
void char_free(character_t *ch);

static inline cldbl char_value(const character_t *ch, uint64_t a) {
    return ch->table[a % ch->Q];
}

#endif /* AIPM_CHARACTERS_H */
