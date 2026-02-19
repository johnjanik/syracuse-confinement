/*
 * gpu_branch_kernel.cl — OpenCL kernels for Collatz branch locus counting
 *
 * Two kernels:
 *   verify_convergence:  Simple convergence check with step-count checksum
 *   branch_count:        Cell visit counting on (Z/kZ)^2 tori for k=3,9,27,81
 *
 * Grid memory layout (all uint32, 32-bit atomics):
 *   Level 0 (k=3):   even[0..8],       odd[9..17]          =    18 cells
 *   Level 1 (k=9):   even[18..98],      odd[99..179]        =   162 cells
 *   Level 2 (k=27):  even[180..908],    odd[909..1637]       =  1458 cells
 *   Level 3 (k=81):  even[1638..8198],  odd[8199..14759]     = 13122 cells
 *   Total: 14760 uint32 counters = 57.66 KB
 *
 * Strategy (branch_count):
 *   k=3, k=9:   private per-work-item accumulators, flushed with atomics at end
 *   k=27, k=81: direct global atomic_add at each step
 *
 * Strategy (branch_count_v2 — optimized):
 *   k=3, k=9:   private per-work-item accumulators
 *   k=27:       local memory accumulators per workgroup (5832 bytes)
 *   k=81:       global atomics
 */

/* ── Grid offsets (compile-time constants) ────────────────────────── */
#define K0 3
#define K1 9
#define K2 27
#define K3 81

#define E0_OFF  0                           /* even k=3   */
#define O0_OFF  (E0_OFF + K0*K0)            /* 9          */
#define E1_OFF  (O0_OFF + K0*K0)            /* 18         */
#define O1_OFF  (E1_OFF + K1*K1)            /* 99         */
#define E2_OFF  (O1_OFF + K1*K1)            /* 180        */
#define O2_OFF  (E2_OFF + K2*K2)            /* 909        */
#define E3_OFF  (O2_OFF + K2*K2)            /* 1638       */
#define O3_OFF  (E3_OFF + K3*K3)            /* 8199       */
#define GRID_TOTAL (O3_OFF + K3*K3)         /* 14760      */

/* ── Kernel 1: Convergence verification ──────────────────────────── */
/*
 * Each work item processes a strided subset of [n_start, n_end].
 * Outputs per-work-item checksum = sum of trajectory lengths.
 * Host sums these for total verification checksum.
 */
__kernel void verify_convergence(
    __global ulong *checksums,      /* [global_work_size] output */
    ulong n_start,
    ulong n_end
)
{
    size_t gid = get_global_id(0);
    size_t gsz = get_global_size(0);
    ulong checksum = 0;

    for (ulong n = n_start + gid; n <= n_end; n += gsz) {
        ulong x = n;
        ulong steps = 0;
        while (x > 1) {
            if (x & 1) x = 3*x + 1;
            else       x >>= 1;
            steps++;
        }
        checksum += steps;
    }

    checksums[gid] = checksum;
}

/* ── Kernel 2: Branch counting ───────────────────────────────────── */
/*
 * Tracks cell visits on (Z/kZ)^2 torus for k = 3, 9, 27, 81.
 * Residues: r2 = count of even steps mod k, r3 = count of odd steps mod k.
 * Cell (r2, r3) updated at each Collatz step.
 *
 * Uses 32-bit grid counters — host must read back and accumulate
 * into 64-bit before overflow (safe for batches up to ~100M numbers).
 */
__kernel void branch_count(
    __global uint *grids,           /* [GRID_TOTAL] = 14760 uint32 */
    ulong n_start,
    ulong n_end
)
{
    size_t gid = get_global_id(0);
    size_t gsz = get_global_size(0);

    /* Private accumulators for k=3 (9 cells) and k=9 (81 cells) */
    uint pe3[K0*K0], po3[K0*K0];
    uint pe9[K1*K1], po9[K1*K1];
    for (int i = 0; i < K0*K0; i++) { pe3[i] = 0; po3[i] = 0; }
    for (int i = 0; i < K1*K1; i++) { pe9[i] = 0; po9[i] = 0; }

    for (ulong n = n_start + gid; n <= n_end; n += gsz) {
        ulong x = n;

        /* Per-level residue state */
        uint r2_0 = 0, r3_0 = 0;   /* k=3  */
        uint r2_1 = 0, r3_1 = 0;   /* k=9  */
        uint r2_2 = 0, r3_2 = 0;   /* k=27 */
        uint r2_3 = 0, r3_3 = 0;   /* k=81 */

        while (x > 1) {
            uint is_odd = x & 1;
            uint idx;

            /* Level 0: k=3 (private) */
            idx = r2_0 * K0 + r3_0;
            if (is_odd) { po3[idx]++; if (++r3_0 == K0) r3_0 = 0; }
            else        { pe3[idx]++; if (++r2_0 == K0) r2_0 = 0; }

            /* Level 1: k=9 (private) */
            idx = r2_1 * K1 + r3_1;
            if (is_odd) { po9[idx]++; if (++r3_1 == K1) r3_1 = 0; }
            else        { pe9[idx]++; if (++r2_1 == K1) r2_1 = 0; }

            /* Level 2: k=27 (global atomic) */
            idx = r2_2 * K2 + r3_2;
            if (is_odd) { atomic_add(&grids[O2_OFF + idx], 1u);
                          if (++r3_2 == K2) r3_2 = 0; }
            else        { atomic_add(&grids[E2_OFF + idx], 1u);
                          if (++r2_2 == K2) r2_2 = 0; }

            /* Level 3: k=81 (global atomic) */
            idx = r2_3 * K3 + r3_3;
            if (is_odd) { atomic_add(&grids[O3_OFF + idx], 1u);
                          if (++r3_3 == K3) r3_3 = 0; }
            else        { atomic_add(&grids[E3_OFF + idx], 1u);
                          if (++r2_3 == K3) r2_3 = 0; }

            /* Collatz step */
            if (is_odd) x = 3*x + 1;
            else        x >>= 1;
        }
    }

    /* Flush private accumulators to global with atomics */
    for (uint i = 0; i < K0*K0; i++) {
        if (pe3[i]) atomic_add(&grids[E0_OFF + i], pe3[i]);
        if (po3[i]) atomic_add(&grids[O0_OFF + i], po3[i]);
    }
    for (uint i = 0; i < K1*K1; i++) {
        if (pe9[i]) atomic_add(&grids[E1_OFF + i], pe9[i]);
        if (po9[i]) atomic_add(&grids[O1_OFF + i], po9[i]);
    }
}

/* ── Kernel 3: Optimized branch counting (local mem for k=27) ──── */
/*
 * Same as branch_count but uses workgroup-local memory for k=27.
 * Local k=27 grids: 729 × 2 × 4 = 5832 bytes (fits in 48 KB LDS).
 * Reduces k=27 global atomic contention by workgroup_size factor.
 */
__kernel void branch_count_v2(
    __global uint *grids,
    ulong n_start,
    ulong n_end
)
{
    size_t gid = get_global_id(0);
    size_t gsz = get_global_size(0);
    size_t lid = get_local_id(0);
    size_t lsz = get_local_size(0);

    /* Local memory for k=27 grids */
    __local uint le27[K2*K2];   /* 729 cells */
    __local uint lo27[K2*K2];

    /* Cooperative init of local memory */
    for (size_t i = lid; i < K2*K2; i += lsz) {
        le27[i] = 0;
        lo27[i] = 0;
    }
    barrier(CLK_LOCAL_MEM_FENCE);

    /* Private accumulators for k=3 and k=9 */
    uint pe3[K0*K0], po3[K0*K0];
    uint pe9[K1*K1], po9[K1*K1];
    for (int i = 0; i < K0*K0; i++) { pe3[i] = 0; po3[i] = 0; }
    for (int i = 0; i < K1*K1; i++) { pe9[i] = 0; po9[i] = 0; }

    for (ulong n = n_start + gid; n <= n_end; n += gsz) {
        ulong x = n;
        uint r2_0 = 0, r3_0 = 0;
        uint r2_1 = 0, r3_1 = 0;
        uint r2_2 = 0, r3_2 = 0;
        uint r2_3 = 0, r3_3 = 0;

        while (x > 1) {
            uint is_odd = x & 1;
            uint idx;

            /* k=3 (private) */
            idx = r2_0 * K0 + r3_0;
            if (is_odd) { po3[idx]++; if (++r3_0 == K0) r3_0 = 0; }
            else        { pe3[idx]++; if (++r2_0 == K0) r2_0 = 0; }

            /* k=9 (private) */
            idx = r2_1 * K1 + r3_1;
            if (is_odd) { po9[idx]++; if (++r3_1 == K1) r3_1 = 0; }
            else        { pe9[idx]++; if (++r2_1 == K1) r2_1 = 0; }

            /* k=27 (local atomic) */
            idx = r2_2 * K2 + r3_2;
            if (is_odd) { atomic_add(&lo27[idx], 1u);
                          if (++r3_2 == K2) r3_2 = 0; }
            else        { atomic_add(&le27[idx], 1u);
                          if (++r2_2 == K2) r2_2 = 0; }

            /* k=81 (global atomic) */
            idx = r2_3 * K3 + r3_3;
            if (is_odd) { atomic_add(&grids[O3_OFF + idx], 1u);
                          if (++r3_3 == K3) r3_3 = 0; }
            else        { atomic_add(&grids[E3_OFF + idx], 1u);
                          if (++r2_3 == K3) r2_3 = 0; }

            if (is_odd) x = 3*x + 1;
            else        x >>= 1;
        }
    }

    /* Flush private k=3, k=9 to global */
    for (uint i = 0; i < K0*K0; i++) {
        if (pe3[i]) atomic_add(&grids[E0_OFF + i], pe3[i]);
        if (po3[i]) atomic_add(&grids[O0_OFF + i], po3[i]);
    }
    for (uint i = 0; i < K1*K1; i++) {
        if (pe9[i]) atomic_add(&grids[E1_OFF + i], pe9[i]);
        if (po9[i]) atomic_add(&grids[O1_OFF + i], po9[i]);
    }

    /* Flush local k=27 to global (cooperative) */
    barrier(CLK_LOCAL_MEM_FENCE);
    for (size_t i = lid; i < K2*K2; i += lsz) {
        if (le27[i]) atomic_add(&grids[E2_OFF + i], le27[i]);
        if (lo27[i]) atomic_add(&grids[O2_OFF + i], lo27[i]);
    }
}

/* ── Kernel 4: Fast k=3,9,27 only (no global atomics) ─────────── */
/*
 * Drops k=81 to eliminate all global atomics from inner loop.
 * k=3, k=9: private. k=27: local memory. Zero global atomics during iteration.
 * Grid layout: only first 1638 cells used (k=3 + k=9 + k=27).
 */
#define GRID_SMALL (E2_OFF + 2*K2*K2)  /* 1638 */

__kernel void branch_count_fast(
    __global uint *grids,       /* [GRID_SMALL] = 1638 uint32 */
    ulong n_start,
    ulong n_end
)
{
    size_t gid = get_global_id(0);
    size_t gsz = get_global_size(0);
    size_t lid = get_local_id(0);
    size_t lsz = get_local_size(0);

    __local uint le27[K2*K2];
    __local uint lo27[K2*K2];

    for (size_t i = lid; i < K2*K2; i += lsz) {
        le27[i] = 0;
        lo27[i] = 0;
    }
    barrier(CLK_LOCAL_MEM_FENCE);

    uint pe3[K0*K0], po3[K0*K0];
    uint pe9[K1*K1], po9[K1*K1];
    for (int i = 0; i < K0*K0; i++) { pe3[i] = 0; po3[i] = 0; }
    for (int i = 0; i < K1*K1; i++) { pe9[i] = 0; po9[i] = 0; }

    for (ulong n = n_start + gid; n <= n_end; n += gsz) {
        ulong x = n;
        uint r2_0 = 0, r3_0 = 0;
        uint r2_1 = 0, r3_1 = 0;
        uint r2_2 = 0, r3_2 = 0;

        while (x > 1) {
            uint is_odd = x & 1;
            uint idx;

            idx = r2_0 * K0 + r3_0;
            if (is_odd) { po3[idx]++; if (++r3_0 == K0) r3_0 = 0; }
            else        { pe3[idx]++; if (++r2_0 == K0) r2_0 = 0; }

            idx = r2_1 * K1 + r3_1;
            if (is_odd) { po9[idx]++; if (++r3_1 == K1) r3_1 = 0; }
            else        { pe9[idx]++; if (++r2_1 == K1) r2_1 = 0; }

            idx = r2_2 * K2 + r3_2;
            if (is_odd) { atomic_add(&lo27[idx], 1u);
                          if (++r3_2 == K2) r3_2 = 0; }
            else        { atomic_add(&le27[idx], 1u);
                          if (++r2_2 == K2) r2_2 = 0; }

            if (is_odd) x = 3*x + 1;
            else        x >>= 1;
        }
    }

    for (uint i = 0; i < K0*K0; i++) {
        if (pe3[i]) atomic_add(&grids[E0_OFF + i], pe3[i]);
        if (po3[i]) atomic_add(&grids[O0_OFF + i], po3[i]);
    }
    for (uint i = 0; i < K1*K1; i++) {
        if (pe9[i]) atomic_add(&grids[E1_OFF + i], pe9[i]);
        if (po9[i]) atomic_add(&grids[O1_OFF + i], po9[i]);
    }

    barrier(CLK_LOCAL_MEM_FENCE);
    for (size_t i = lid; i < K2*K2; i += lsz) {
        if (le27[i]) atomic_add(&grids[E2_OFF + i], le27[i]);
        if (lo27[i]) atomic_add(&grids[O2_OFF + i], lo27[i]);
    }
}
