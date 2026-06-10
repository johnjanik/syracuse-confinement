#include "orbit_scan.h"

#ifdef AIPM_DEBUG
#include <assert.h>
#endif

void orbit_init(orbit_t *o, uint64_t seed) {
    bv_init_u64(&o->x, seed);
    o->step = 0;
    o->Bn = 0;
    o->last_b = 0;
    o->status = (seed == 1) ? ORBIT_REACHED_ONE : ORBIT_RUNNING;
    o->log2_x0 = bv_log2(&o->x);
}

void orbit_clear(orbit_t *o) { bv_clear(&o->x); }

uint32_t orbit_step(orbit_t *o) {
    if (o->status != ORBIT_RUNNING) return 0;

#ifdef AIPM_DEBUG
    /* invariant: every state on the accelerated orbit is an odd integer */
    assert((bv_mod_u64(&o->x, 2) == 1) && "orbit value must be odd");
#endif

    step_meta_t m = bv_syracuse_step(&o->x);
    if (m.overflow) { o->status = ORBIT_OVERFLOW; return 0; }

#ifdef AIPM_DEBUG
    assert(m.b >= 1 && "v2(3x+1) >= 1 since 3*odd+1 is even");
    assert((bv_mod_u64(&o->x, 2) == 1) && "S(x) must be odd");
#endif

    o->step  += 1;
    o->Bn    += m.b;
    o->last_b = m.b;
    if (bv_is_one(&o->x)) o->status = ORBIT_REACHED_ONE;
    return m.b;
}

ldbl orbit_height(const orbit_t *o) {
    return bv_log2(&o->x) - o->log2_x0;
}
