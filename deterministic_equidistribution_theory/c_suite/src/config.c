#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void config_defaults(config_t *c) {
    memset(c, 0, sizeof *c);
    c->start = 1; c->end = 0;
    c->octave_min = 10; c->octave_max = 12;
    c->max_steps = 1000000;
    c->seed = 27;
    c->char_cap = 3;
    c->post_len = 32;
    c->r_max = 6;
    c->n_samples = 8;
    c->delta = 0.1L;
    c->L = 64; c->R = 8; c->bmax = 20;
    c->seeds_per_octave = 50000;
    c->crit_mode = 1;   /* default: height (peak>=launch*2^A); vsq is degenerate */
    c->height_mode = 0; /* default: sync (faithful skew product) */
    c->threads = 1;
    c->output_dir = "out";
    /* default grids from spec */
    int dw[] = {16,32,64,128,256,512,1024,2048};
    for (size_t i = 0; i < sizeof dw/sizeof dw[0]; i++) c->windows[c->n_windows++] = dw[i];
    uint64_t dm[] = {8,16,27,81,243,729};
    for (size_t i = 0; i < sizeof dm/sizeof dm[0]; i++) c->moduli[c->n_moduli++] = dm[i];
    ldbl dt[] = {0.0L,0.25L,0.5L,0.75L,1.0L,1.25L,1.5L};
    for (size_t i = 0; i < sizeof dt/sizeof dt[0]; i++) c->tilts[c->n_tilts++] = dt[i];
    int da[] = {4,5,6,7,8};
    for (size_t i = 0; i < sizeof da/sizeof da[0]; i++) c->apertures[c->n_apertures++] = da[i];
}

static int parse_int_list(const char *s, int *out, int cap) {
    int n = 0; char *dup = strdup(s); char *tok = strtok(dup, ",");
    while (tok && n < cap) { out[n++] = atoi(tok); tok = strtok(NULL, ","); }
    free(dup); return n;
}
static int parse_u64_list(const char *s, uint64_t *out, int cap) {
    int n = 0; char *dup = strdup(s); char *tok = strtok(dup, ",");
    while (tok && n < cap) { out[n++] = strtoull(tok,NULL,10); tok = strtok(NULL, ","); }
    free(dup); return n;
}
static int parse_ldbl_list(const char *s, ldbl *out, int cap) {
    int n = 0; char *dup = strdup(s); char *tok = strtok(dup, ",");
    while (tok && n < cap) { out[n++] = strtold(tok,NULL); tok = strtok(NULL, ","); }
    free(dup); return n;
}

int config_parse(config_t *c, int argc, char **argv, int from) {
    for (int i = from; i < argc; i++) {
        const char *k = argv[i];
        #define NEED_VAL() do{ if(i+1>=argc){fprintf(stderr,"missing value for %s\n",k);return 1;} }while(0)
        if      (!strcmp(k,"--start"))      { NEED_VAL(); c->start = strtoull(argv[++i],NULL,10); }
        else if (!strcmp(k,"--end"))        { NEED_VAL(); c->end = strtoull(argv[++i],NULL,10); }
        else if (!strcmp(k,"--octave-min")) { NEED_VAL(); c->octave_min = atoi(argv[++i]); }
        else if (!strcmp(k,"--octave-max")) { NEED_VAL(); c->octave_max = atoi(argv[++i]); }
        else if (!strcmp(k,"--max-steps"))  { NEED_VAL(); c->max_steps = strtoull(argv[++i],NULL,10); }
        else if (!strcmp(k,"--seed"))       { NEED_VAL(); c->seed = strtoull(argv[++i],NULL,10); }
        else if (!strcmp(k,"--windows"))    { NEED_VAL(); c->n_windows = parse_int_list(argv[++i],c->windows,CFG_MAX_LIST); }
        else if (!strcmp(k,"--moduli"))     { NEED_VAL(); c->n_moduli = parse_u64_list(argv[++i],c->moduli,CFG_MAX_LIST); }
        else if (!strcmp(k,"--tilts"))      { NEED_VAL(); c->n_tilts = parse_ldbl_list(argv[++i],c->tilts,CFG_MAX_LIST); }
        else if (!strcmp(k,"--apertures"))  { NEED_VAL(); c->n_apertures = parse_int_list(argv[++i],c->apertures,CFG_MAX_LIST); }
        else if (!strcmp(k,"--char-cap"))   { NEED_VAL(); c->char_cap = atoi(argv[++i]); }
        else if (!strcmp(k,"--post-len"))   { NEED_VAL(); c->post_len = atoi(argv[++i]); }
        else if (!strcmp(k,"--r-max"))      { NEED_VAL(); c->r_max = atoi(argv[++i]); }
        else if (!strcmp(k,"--n-samples"))  { NEED_VAL(); c->n_samples = atoi(argv[++i]); }
        else if (!strcmp(k,"--delta"))      { NEED_VAL(); c->delta = strtold(argv[++i],NULL); }
        else if (!strcmp(k,"--L"))          { NEED_VAL(); c->L = atoi(argv[++i]); }
        else if (!strcmp(k,"--R"))          { NEED_VAL(); c->R = atoi(argv[++i]); }
        else if (!strcmp(k,"--bmax"))       { NEED_VAL(); c->bmax = atoi(argv[++i]); }
        else if (!strcmp(k,"--seeds-per-octave")) { NEED_VAL(); c->seeds_per_octave = strtoull(argv[++i],NULL,10); }
        else if (!strcmp(k,"--crit-mode")) { NEED_VAL(); ++i; c->crit_mode = !strcmp(argv[i],"height") ? 1 : 0; }
        else if (!strcmp(k,"--height-mode")) { NEED_VAL(); ++i; c->height_mode = !strcmp(argv[i],"factored") ? 1 : 0; }
        else if (!strcmp(k,"--threads"))    { NEED_VAL(); c->threads = atoi(argv[++i]); }
        else if (!strcmp(k,"--output-dir")) { NEED_VAL(); c->output_dir = argv[++i]; }
        else if (!strcmp(k,"--profile"))    { NEED_VAL(); ++i; /* backend is compile-time; informational */ }
        else if (!strcmp(k,"--debug-checks")){ c->debug_checks = 1; }
        else { fprintf(stderr, "unknown option: %s\n", k); return 1; }
        #undef NEED_VAL
    }
    return 0;
}

void config_print(const config_t *c, FILE *f) {
    fprintf(f, "# config: seed=%llu start=%llu end=%llu max_steps=%llu r_max=%d L=%d R=%d bmax=%d delta=%.3Lf\n",
            (unsigned long long)c->seed, (unsigned long long)c->start,
            (unsigned long long)c->end, (unsigned long long)c->max_steps,
            c->r_max, c->L, c->R, c->bmax, c->delta);
}
