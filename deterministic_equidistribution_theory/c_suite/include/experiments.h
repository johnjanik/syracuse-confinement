/* experiments.h — entry points for each experiment subcommand (A..I).
 * Each returns 0 on success. Built incrementally across milestones M0..M4. */
#ifndef AIPM_EXPERIMENTS_H
#define AIPM_EXPERIMENTS_H

#include "config.h"

int exp_congruence(const config_t *c, int argc, char **argv);  /* H (M0) */
int exp_scan_height(const config_t *c, int argc, char **argv); /* A (M1) */
int exp_tilt_law(const config_t *c, int argc, char **argv);    /* B (M1) */
int exp_defect_windows(const config_t *c, int argc, char **argv);/* C (M2)*/
int exp_post_exit(const config_t *c, int argc, char **argv);   /* D (M2) */
int exp_spectral_gaps(const config_t *c, int argc, char **argv);/* E (M3) */
int exp_fourier_compare(const config_t *c, int argc, char **argv);/* F (M3)*/
int exp_trace_det(const config_t *c, int argc, char **argv);   /* G (M4) */
int exp_shadow_search(const config_t *c, int argc, char **argv);/* I (M4) */

#endif /* AIPM_EXPERIMENTS_H */
