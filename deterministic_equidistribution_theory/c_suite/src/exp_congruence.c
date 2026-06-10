/* exp_congruence.c — Experiment H: sliding-window congruence verification.
 *
 * CORRECTNESS GATE (critique dc_1.md, point 2): the manuscript's load-bearing
 * identity is, for n >= r,
 *
 *     x_n  ==  sum_{k=1}^{r} 3^{k-1} * 2^{-(b_{n-k}+...+b_{n-1})}   (mod 3^r).
 *
 * The critique flags this as plausible-but-unverified and says it must not be
 * used as load-bearing until proved. Here we verify it numerically against the
 * directly-reduced orbit value before any spectral/character code relies on it.
 *
 * `direct_residue`  = x_n mod 3^r, reduced from the true orbit value (independent
 *                     of the formula).
 * `formula_residue` = the right-hand side, using 2^{-1} mod 3^r and the b-word.
 * Any mismatch (without an overflow flag) is a bug or a convention error.
 */
#include "experiments.h"
#include "orbit_scan.h"
#include "modarith.h"
#include "io_csv.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int run_one_seed(FILE *f, uint64_t seed, const config_t *c,
                        uint64_t *n_match, uint64_t *n_total) {
    int r_max = c->r_max;
    uint64_t mod_max = ma_ipow(3, (uint64_t)r_max);

    /* Record the full b-word and the residue mod 3^{r_max} at every step. */
    size_t cap = 1024, len = 0;
    uint32_t *b   = malloc(cap * sizeof *b);
    uint64_t *res = malloc((cap + 1) * sizeof *res); /* res[i] = x_i mod mod_max */
    uint64_t *B   = malloc((cap + 1) * sizeof *B);   /* prefix sums of b        */
    if (!b || !res || !B) { free(b); free(res); free(B); return 1; }

    orbit_t o; orbit_init(&o, seed);
    res[0] = bv_mod_u64(&o.x, mod_max);
    B[0] = 0;
    const char *status = "ok";

    while (o.status == ORBIT_RUNNING && o.step < c->max_steps) {
        uint32_t bi = orbit_step(&o);
        if (o.status == ORBIT_OVERFLOW) { status = "overflow"; break; }
        if (len + 1 >= cap) {
            cap *= 2;
            b   = realloc(b,   cap * sizeof *b);
            res = realloc(res, (cap + 1) * sizeof *res);
            B   = realloc(B,   (cap + 1) * sizeof *B);
            if (!b || !res || !B) { free(b); free(res); free(B); orbit_clear(&o); return 1; }
        }
        b[len]     = bi;
        B[len + 1] = B[len] + bi;
        res[len + 1] = bv_mod_u64(&o.x, mod_max);
        len++;
    }
    orbit_clear(&o);

    if (len < (size_t)r_max) { free(b); free(res); free(B); return 0; }

    /* Sample n positions evenly across [r_max, len]. */
    int ns = c->n_samples; if (ns < 1) ns = 1;
    for (int si = 0; si < ns; si++) {
        size_t n = (size_t)r_max +
                   (size_t)((double)(len - r_max) * (double)si / (double)(ns > 1 ? ns - 1 : 1));
        if (n < (size_t)r_max) n = r_max;
        if (n > len) n = len;

        for (int r = 1; r <= r_max; r++) {
            uint64_t modr = ma_ipow(3, (uint64_t)r);
            uint64_t inv2 = ma_inv(2, modr);
            uint64_t direct = res[n] % modr;

            /* formula: sum_{k=1}^r 3^{k-1} * inv2^{(B[n]-B[n-k])}  (mod 3^r) */
            uint64_t formula = 0, pow3 = 1;
            for (int k = 1; k <= r; k++) {
                uint64_t S = B[n] - B[n - k];          /* b_{n-k}+...+b_{n-1} */
                uint64_t term = ma_mulmod(pow3, ma_powmod(inv2, S, modr), modr);
                formula = (formula + term) % modr;
                pow3 = ma_mulmod(pow3, 3, modr);
            }
            uint64_t phi = 2 * ma_ipow(3, (uint64_t)(r - 1)); /* ord(2 mod 3^r) */
            int match = (direct == formula);
            (*n_total)++; if (match) (*n_match)++;

            fprintf(f, "%llu,%zu,%d,%llu,%llu,%llu,%d,%llu,%s\n",
                    (unsigned long long)seed, n, r, (unsigned long long)modr,
                    (unsigned long long)direct, (unsigned long long)formula,
                    match, (unsigned long long)(B[n] % phi), status);
        }
    }

    free(b); free(res); free(B);
    return 0;
}

int exp_congruence(const config_t *c, int argc, char **argv) {
    char path[512];
    snprintf(path, sizeof path, "%s/congruence_checks.csv", c->output_dir);
    FILE *f = csv_open(path, "congruence_checks",
        "seed,n,r,modulus,direct_residue,formula_residue,match_flag,Bn_mod_phi,status",
        argc, argv);
    if (!f) { perror("csv_open"); return 1; }

    uint64_t n_match = 0, n_total = 0;

    if (c->end >= c->start && c->end > 1) {
        for (uint64_t s = c->start | 1u; s <= c->end; s += 2)
            run_one_seed(f, s, c, &n_match, &n_total);
    } else {
        uint64_t s = c->seed | 1u;
        run_one_seed(f, s, c, &n_match, &n_total);
    }
    fclose(f);

    fprintf(stderr, "[congruence] %llu/%llu checks matched (%s)\n",
            (unsigned long long)n_match, (unsigned long long)n_total,
            n_match == n_total ? "PASS" : "MISMATCH — investigate");
    fprintf(stderr, "[congruence] wrote %s\n", path);
    return (n_total > 0 && n_match != n_total) ? 2 : 0;
}
