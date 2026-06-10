/* critical_events.h — run one orbit, record its valuation word, detect
 * excursions between record-lows, and flag critical ones.
 *
 * EXCURSION = the orbit segment from one record-low ("launch floor" V) up to a
 *             peak P and down to the next record-low ("exit" X). Launches are
 *             the monotone-decreasing sequence of record lows.
 *
 * CRITICALITY (spec Section "Numerical precision"): an excursion is A-critical
 * iff  V^2 <= 2^A * P, checked in exact integer arithmetic (bv_is_A_critical).
 *
 * NOTE (definitional caveat): the project-internal "C_A-critical" certificate
 * (H23a/PVT/SRCE machinery) is carried over without restatement in the source
 * notes. We implement the literal inequality V^2 <= 2^A P from the spec; the
 * "high ascent" height log2(P/V) is also recorded so the two readings can be
 * compared. See the M1 status note for the open question on this definition.
 */
#ifndef AIPM_CRITICAL_EVENTS_H
#define AIPM_CRITICAL_EVENTS_H

#include "orbit_scan.h"
#include "config.h"

#define CE_MAX_APERTURES 16

typedef struct {
    uint64_t start_step, end_step;   /* excursion covers steps (start_step, end_step] */
    uint64_t word_length;            /* end_step - start_step                         */
    uint64_t D;                      /* sum of b over the excursion                   */
    ldbl     launch_log2, peak_log2, exit_log2, height_log2; /* height = peak-launch  */
    char     launch_dec[48], peak_dec[48], exit_dec[48];
    int      critical_A[CE_MAX_APERTURES]; /* 1 if A-critical, parallel to cfg->apertures */
    const char *status;
} crit_event_t;

typedef struct {
    uint16_t      *b;            /* full valuation word, b[0..len-1]      */
    size_t         len;
    orbit_status_t status;
    ldbl           max_height;   /* max over orbit of log2(x_n)-log2(x_0) */
    crit_event_t  *ev;           /* detected excursions                   */
    size_t         nev;
    /* optional residue capture: res[i*nmod + qi] = x_i mod moduli[qi],
     * for i = 0..len (states x_0..x_len). NULL if not requested. */
    uint64_t      *res;
    int            nmod;
} orbit_data_t;

/* per-step segment labels (spec Section "Experiment C / Segment labels"). */
typedef enum {
    LBL_ORDINARY = 0, LBL_HIGH_ASCENT, LBL_CRITICAL, LBL_POST_EXIT,
    LBL_SUBEQ, LBL_CYCLE, LBL_UNKNOWN
} seg_label_t;
const char *ce_label_name(seg_label_t l);
/* Fill label[0..d->len-1]. Uses excursions (critical for aperture index 0),
 * the running deficit E_m = B_m - m*log2 3 for sub-equilibrium tails, and
 * cfg->post_len for post-exit windows. */
void ce_label_steps(const orbit_data_t *d, const config_t *cfg, uint8_t *label);
/* index of the excursion containing step j, or -1. */
long ce_event_of_step(const orbit_data_t *d, uint64_t j);

/* Run the orbit of `seed`, recording the word and excursions. If `moduli`
 * is non-NULL (nmod entries), also capture per-step residues. Returns 0 ok. */
int  orbit_run_record_ex(uint64_t seed, const config_t *cfg,
                         const uint64_t *moduli, int nmod, orbit_data_t *out);
/* convenience: no residue capture. */
int  orbit_run_record(uint64_t seed, const config_t *cfg, orbit_data_t *out);
void orbit_data_free(orbit_data_t *d);

#endif /* AIPM_CRITICAL_EVENTS_H */
