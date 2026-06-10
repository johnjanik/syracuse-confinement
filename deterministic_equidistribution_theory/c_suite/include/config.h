/* config.h — CLI parsing + experiment configuration shared by all subcommands.
 * Spec Section "Command-Line Interface". */
#ifndef AIPM_CONFIG_H
#define AIPM_CONFIG_H

#include <stdint.h>
#include <stdio.h>
#include "common.h"

#define CFG_MAX_LIST 64

typedef struct {
    /* seed / range selection */
    uint64_t start, end;          /* odd seed range (inclusive)             */
    int      octave_min, octave_max;
    uint64_t max_steps;
    uint64_t seed;                /* single-seed convenience                */

    /* grids */
    int      windows[CFG_MAX_LIST];   int n_windows;
    uint64_t moduli[CFG_MAX_LIST];    int n_moduli;
    ldbl     tilts[CFG_MAX_LIST];     int n_tilts;
    int      apertures[CFG_MAX_LIST]; int n_apertures;

    /* experiment-specific knobs */
    int      char_cap;            /* additive characters per modulus (Exp C) */
    int      post_len;            /* post-exit window length (Exp D)         */
    int      r_max;               /* max r for mod 3^r tests (Exp H)        */
    int      n_samples;           /* number of n positions to sample        */
    ldbl     delta;               /* shadow-flag threshold (Exp I)          */
    int      L;                   /* height-band size for finite operator   */
    int      R;                   /* height scale factor                    */
    int      bmax;                /* max valuation in finite operator       */

    uint64_t seeds_per_octave;    /* cap on odd seeds sampled per octave (0=all) */
    int      crit_mode;           /* 0 = V^2<=2^A P (literal spec); 1 = P>=V<<A (high ascent) */
    int      height_mode;         /* 0 = sync skew product; 1 = factored (residue (x) height) */

    int      threads;
    int      debug_checks;
    const char *output_dir;
} config_t;

void config_defaults(config_t *c);
/* Parse argv[from..argc) of "--key value" form into c. Returns 0 on success. */
int  config_parse(config_t *c, int argc, char **argv, int from);
void config_print(const config_t *c, FILE *f);

#endif /* AIPM_CONFIG_H */
