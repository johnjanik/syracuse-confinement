/* orbit_scan.h — streaming accelerated-Syracuse orbit iterator.
 *
 * Streaming by design (spec Section "Performance Requirements"): the iterator
 * holds only the current true value, the running partial-sum B_n, step index,
 * and status. Callers that need history keep their own ring buffers.
 */
#ifndef AIPM_ORBIT_SCAN_H
#define AIPM_ORBIT_SCAN_H

#include "bigval.h"

typedef enum {
    ORBIT_RUNNING = 0,
    ORBIT_REACHED_ONE,   /* x == 1 (the trivial fixed point of S)            */
    ORBIT_MAX_STEPS,     /* hit step budget                                  */
    ORBIT_OVERFLOW       /* FAST128 backend overflowed; rerun under GMP      */
} orbit_status_t;

typedef struct {
    bigval_t       x;        /* current odd value                           */
    uint64_t       step;     /* number of steps taken (n)                   */
    uint64_t       Bn;       /* sum_{i<n} b_i                               */
    uint32_t       last_b;   /* b_{n-1}, valuation of the last step         */
    orbit_status_t status;
    ldbl           log2_x0;  /* log2 of the seed, for height diagnostics    */
} orbit_t;

void orbit_init(orbit_t *o, uint64_t seed);   /* seed must be odd, >= 1 */
void orbit_clear(orbit_t *o);

/* Advance one accelerated step. Returns b for the step, or sets status and
 * returns 0 if the orbit cannot continue. Stops at x==1. */
uint32_t orbit_step(orbit_t *o);

/* Current height log2(x_n) - log2(x_0)  (diagnostic only). */
ldbl orbit_height(const orbit_t *o);

#endif /* AIPM_ORBIT_SCAN_H */
