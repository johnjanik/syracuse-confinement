/*
 * gpu_branch_host.c — GPU-accelerated Collatz branch locus counting
 *
 * Usage:
 *   ./gpu_branch --verify  N     Convergence verification with checksum
 *   ./gpu_branch --branch  N     Branch counting for k=3,9,27,81
 *   ./gpu_branch --compare N     GPU vs CPU correctness comparison
 *
 * Requires: OpenCL runtime with NVIDIA GPU
 *
 * Build: gcc -O3 -o gpu_branch gpu_branch_host.c -lOpenCL -lm
 */

#define _GNU_SOURCE
#define CL_TARGET_OPENCL_VERSION 120
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <math.h>
#include <time.h>
#include <CL/cl.h>

/* ── Grid geometry (must match kernel) ──────────────────────────── */
#define NUM_LEVELS 4
static const int K_VAL[NUM_LEVELS] = {3, 9, 27, 81};

/* Offsets into flat grid buffer */
static int E_OFF[NUM_LEVELS];  /* even grid start */
static int O_OFF[NUM_LEVELS];  /* odd grid start  */
static int GRID_TOTAL;         /* total uint32 cells */

static void compute_offsets(void) {
    int off = 0;
    for (int i = 0; i < NUM_LEVELS; i++) {
        int k = K_VAL[i];
        E_OFF[i] = off;
        O_OFF[i] = off + k * k;
        off += 2 * k * k;
    }
    GRID_TOTAL = off;  /* 14760 */
}

/* ── Timing ─────────────────────────────────────────────────────── */
static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void fmt_time(double s, char *buf, int len) {
    int h = (int)(s / 3600);
    int m = (int)(fmod(s, 3600) / 60);
    double sec = fmod(s, 60);
    snprintf(buf, len, "%02d:%02d:%04.1f", h, m, sec);
}

/* ── OpenCL helpers ─────────────────────────────────────────────── */
static const char *cl_err_str(cl_int e) {
    switch (e) {
    case CL_SUCCESS:                    return "CL_SUCCESS";
    case CL_DEVICE_NOT_FOUND:           return "CL_DEVICE_NOT_FOUND";
    case CL_BUILD_PROGRAM_FAILURE:      return "CL_BUILD_PROGRAM_FAILURE";
    case CL_INVALID_VALUE:              return "CL_INVALID_VALUE";
    case CL_INVALID_DEVICE:             return "CL_INVALID_DEVICE";
    case CL_INVALID_CONTEXT:            return "CL_INVALID_CONTEXT";
    case CL_INVALID_KERNEL_NAME:        return "CL_INVALID_KERNEL_NAME";
    case CL_INVALID_MEM_OBJECT:         return "CL_INVALID_MEM_OBJECT";
    case CL_INVALID_ARG_VALUE:          return "CL_INVALID_ARG_VALUE";
    case CL_INVALID_WORK_GROUP_SIZE:    return "CL_INVALID_WORK_GROUP_SIZE";
    case CL_OUT_OF_RESOURCES:           return "CL_OUT_OF_RESOURCES";
    case CL_MEM_OBJECT_ALLOCATION_FAILURE: return "CL_MEM_OBJECT_ALLOC_FAIL";
    case CL_COMPILER_NOT_AVAILABLE:     return "CL_COMPILER_NOT_AVAILABLE";
    default: {
        static char buf[32];
        snprintf(buf, sizeof(buf), "CL_ERROR_%d", e);
        return buf;
    }
    }
}

#define CL_CHECK(call, msg) do { \
    cl_int _e = (call); \
    if (_e != CL_SUCCESS) { \
        fprintf(stderr, "[ERROR] %s: %s\n", msg, cl_err_str(_e)); \
        exit(1); \
    } \
} while (0)

/* Load kernel source from file */
static char *load_kernel_source(const char *path, size_t *len) {
    FILE *f = fopen(path, "r");
    if (!f) { perror(path); exit(1); }
    fseek(f, 0, SEEK_END);
    *len = ftell(f);
    rewind(f);
    char *src = malloc(*len + 1);
    size_t nread = fread(src, 1, *len, f);
    if (nread != *len) { *len = nread; }
    src[*len] = '\0';
    fclose(f);
    return src;
}

/* ── OpenCL context setup ───────────────────────────────────────── */
typedef struct {
    cl_platform_id   platform;
    cl_device_id     device;
    cl_context       ctx;
    cl_command_queue  queue;
    cl_program       prog;
    char             dev_name[256];
    cl_ulong         global_mem;
    cl_ulong         local_mem;
    size_t           max_wg;
    cl_uint          compute_units;
} gpu_ctx_t;

static void gpu_init(gpu_ctx_t *g, const char *kernel_path) {
    cl_int err;
    cl_uint np;
    CL_CHECK(clGetPlatformIDs(0, NULL, &np), "clGetPlatformIDs count");
    if (np == 0) { fprintf(stderr, "No OpenCL platforms\n"); exit(1); }

    cl_platform_id *plats = malloc(np * sizeof(cl_platform_id));
    CL_CHECK(clGetPlatformIDs(np, plats, NULL), "clGetPlatformIDs");

    /* Find first GPU device */
    int found = 0;
    for (cl_uint p = 0; p < np && !found; p++) {
        cl_uint nd;
        if (clGetDeviceIDs(plats[p], CL_DEVICE_TYPE_GPU, 0, NULL, &nd)
            != CL_SUCCESS || nd == 0) continue;
        cl_device_id *devs = malloc(nd * sizeof(cl_device_id));
        clGetDeviceIDs(plats[p], CL_DEVICE_TYPE_GPU, nd, devs, NULL);
        g->platform = plats[p];
        g->device   = devs[0];
        free(devs);
        found = 1;
    }
    free(plats);
    if (!found) { fprintf(stderr, "No GPU device found\n"); exit(1); }

    /* Query device info */
    clGetDeviceInfo(g->device, CL_DEVICE_NAME, sizeof(g->dev_name),
                    g->dev_name, NULL);
    clGetDeviceInfo(g->device, CL_DEVICE_GLOBAL_MEM_SIZE, sizeof(cl_ulong),
                    &g->global_mem, NULL);
    clGetDeviceInfo(g->device, CL_DEVICE_LOCAL_MEM_SIZE, sizeof(cl_ulong),
                    &g->local_mem, NULL);
    clGetDeviceInfo(g->device, CL_DEVICE_MAX_WORK_GROUP_SIZE, sizeof(size_t),
                    &g->max_wg, NULL);
    clGetDeviceInfo(g->device, CL_DEVICE_MAX_COMPUTE_UNITS, sizeof(cl_uint),
                    &g->compute_units, NULL);

    printf("GPU: %s\n", g->dev_name);
    printf("  Global mem: %.1f GB, Local mem: %lu KB\n",
           g->global_mem / 1e9, (unsigned long)(g->local_mem / 1024));
    printf("  Compute units: %u, Max workgroup: %zu\n",
           g->compute_units, g->max_wg);

    /* Create context and command queue */
    g->ctx = clCreateContext(NULL, 1, &g->device, NULL, NULL, &err);
    CL_CHECK(err, "clCreateContext");

    g->queue = clCreateCommandQueue(g->ctx, g->device, 0, &err);
    CL_CHECK(err, "clCreateCommandQueue");

    /* Load and build program */
    size_t src_len;
    char *src = load_kernel_source(kernel_path, &src_len);
    g->prog = clCreateProgramWithSource(g->ctx, 1,
                (const char **)&src, &src_len, &err);
    CL_CHECK(err, "clCreateProgramWithSource");

    err = clBuildProgram(g->prog, 1, &g->device, "", NULL, NULL);
    if (err == CL_BUILD_PROGRAM_FAILURE) {
        size_t log_sz;
        clGetProgramBuildInfo(g->prog, g->device,
            CL_PROGRAM_BUILD_LOG, 0, NULL, &log_sz);
        char *log = malloc(log_sz + 1);
        clGetProgramBuildInfo(g->prog, g->device,
            CL_PROGRAM_BUILD_LOG, log_sz, log, NULL);
        log[log_sz] = '\0';
        fprintf(stderr, "Build log:\n%s\n", log);
        free(log);
    }
    CL_CHECK(err, "clBuildProgram");
    free(src);

    printf("  Kernel compiled OK\n\n");
}

static void gpu_cleanup(gpu_ctx_t *g) {
    clReleaseProgram(g->prog);
    clReleaseCommandQueue(g->queue);
    clReleaseContext(g->ctx);
}

/* CPU reference: convergence checksum */
static uint64_t cpu_verify(uint64_t n_start, uint64_t n_end) {
    uint64_t checksum = 0;
    for (uint64_t n = n_start; n <= n_end; n++) {
        uint64_t x = n;
        uint64_t steps = 0;
        while (x > 1) {
            if (x & 1) x = 3*x + 1;
            else       x >>= 1;
            steps++;
        }
        checksum += steps;
    }
    return checksum;
}

/* ── GPU verify mode ────────────────────────────────────────────── */
static void run_verify(gpu_ctx_t *g, uint64_t N, int do_compare) {
    cl_int err;
    size_t gws = 65536;  /* global work size */
    uint64_t batch_size = 50000000ULL;  /* 50M per batch */

    printf("=== Convergence verification: N = %" PRIu64 " ===\n", N);
    printf("Global work size: %zu, Batch size: %" PRIu64 "\n\n", gws, batch_size);

    cl_kernel kern = clCreateKernel(g->prog, "verify_convergence", &err);
    CL_CHECK(err, "clCreateKernel verify_convergence");

    cl_mem mem_checksums = clCreateBuffer(g->ctx, CL_MEM_WRITE_ONLY,
        gws * sizeof(cl_ulong), NULL, &err);
    CL_CHECK(err, "clCreateBuffer checksums");

    uint64_t *checksums = malloc(gws * sizeof(uint64_t));
    uint64_t gpu_total = 0;
    double t0 = now_sec();

    for (uint64_t batch_start = 2; batch_start <= N; batch_start += batch_size) {
        uint64_t batch_end = batch_start + batch_size - 1;
        if (batch_end > N) batch_end = N;

        cl_ulong ns = batch_start, ne = batch_end;
        CL_CHECK(clSetKernelArg(kern, 0, sizeof(cl_mem), &mem_checksums),
                 "setarg 0");
        CL_CHECK(clSetKernelArg(kern, 1, sizeof(cl_ulong), &ns), "setarg 1");
        CL_CHECK(clSetKernelArg(kern, 2, sizeof(cl_ulong), &ne), "setarg 2");

        CL_CHECK(clEnqueueNDRangeKernel(g->queue, kern, 1, NULL,
                 &gws, NULL, 0, NULL, NULL), "enqueue verify");

        CL_CHECK(clEnqueueReadBuffer(g->queue, mem_checksums, CL_TRUE, 0,
                 gws * sizeof(cl_ulong), checksums, 0, NULL, NULL),
                 "read checksums");

        uint64_t batch_sum = 0;
        for (size_t i = 0; i < gws; i++) batch_sum += checksums[i];
        gpu_total += batch_sum;

        double dt = now_sec() - t0;
        double nums_done = (double)(batch_end - 1);
        double rate = nums_done / dt / 1e6;
        printf("  batch [%" PRIu64 ", %" PRIu64 "] checksum=%" PRIu64
               "  (%.1fM nums/s)\n", batch_start, batch_end, batch_sum, rate);
    }

    double total_time = now_sec() - t0;
    char tbuf[32]; fmt_time(total_time, tbuf, sizeof(tbuf));
    printf("\nGPU total checksum: %" PRIu64 "\n", gpu_total);
    printf("GPU time: %s (%.1fM nums/s)\n", tbuf, (double)N / total_time / 1e6);

    if (do_compare) {
        printf("\nRunning CPU reference...\n");
        double tc0 = now_sec();
        uint64_t cpu_total = cpu_verify(2, N);
        double tc = now_sec() - tc0;
        char tcbuf[32]; fmt_time(tc, tcbuf, sizeof(tcbuf));
        printf("CPU total checksum: %" PRIu64 "\n", cpu_total);
        printf("CPU time: %s (%.1fM nums/s)\n", tcbuf, (double)N / tc / 1e6);
        if (gpu_total == cpu_total)
            printf("\n*** MATCH: GPU and CPU checksums agree ***\n");
        else
            printf("\n*** MISMATCH: GPU=%" PRIu64 " CPU=%" PRIu64 " ***\n",
                   gpu_total, cpu_total);
    }

    free(checksums);
    clReleaseMemObject(mem_checksums);
    clReleaseKernel(kern);
}

/* ── GPU branch mode ────────────────────────────────────────────── */
static void run_branch(gpu_ctx_t *g, uint64_t N, int do_compare, int fast) {
    cl_int err;
    size_t gws = 65536;
    uint64_t batch_size = 50000000ULL;

    compute_offsets();

    /* fast mode: k=3,9,27 only (no global atomics); full: k=3,9,27,81 */
    int num_levels = fast ? 3 : NUM_LEVELS;
    int grid_cells = fast ? (E_OFF[2] + 2 * K_VAL[2] * K_VAL[2]) : GRID_TOTAL;
    size_t grid_bytes = grid_cells * sizeof(cl_uint);
    const char *kern_name = fast ? "branch_count_fast" : "branch_count_v2";

    printf("=== Branch counting%s: N = %" PRIu64 " ===\n",
           fast ? " (fast, k<=27)" : "", N);
    printf("Levels: k=3, k=9, k=27%s\n", fast ? "" : ", k=81");
    printf("Grid: %d cells = %.1f KB\n", grid_cells, grid_bytes / 1024.0);
    printf("Global work size: %zu, Batch size: %" PRIu64 "\n\n", gws, batch_size);

    cl_kernel kern = clCreateKernel(g->prog, kern_name, &err);
    CL_CHECK(err, kern_name);

    /* GPU grid buffer — zeroed */
    cl_mem mem_grids = clCreateBuffer(g->ctx, CL_MEM_READ_WRITE,
        grid_bytes, NULL, &err);
    CL_CHECK(err, "clCreateBuffer grids");

    cl_uint zero = 0;
    CL_CHECK(clEnqueueFillBuffer(g->queue, mem_grids, &zero, sizeof(cl_uint),
             0, grid_bytes, 0, NULL, NULL), "fill grids zero");
    clFinish(g->queue);

    /* Host 64-bit accumulators */
    int64_t *host_grids = calloc(grid_cells, sizeof(int64_t));
    uint32_t *batch_grids = malloc(grid_bytes);

    double t0 = now_sec();
    uint64_t total_processed = 0;

    for (uint64_t batch_start = 2; batch_start <= N; batch_start += batch_size) {
        uint64_t batch_end = batch_start + batch_size - 1;
        if (batch_end > N) batch_end = N;

        /* Zero GPU grids for this batch */
        CL_CHECK(clEnqueueFillBuffer(g->queue, mem_grids, &zero,
                 sizeof(cl_uint), 0, grid_bytes, 0, NULL, NULL), "fill zero");

        cl_ulong ns = batch_start, ne = batch_end;
        CL_CHECK(clSetKernelArg(kern, 0, sizeof(cl_mem), &mem_grids), "arg 0");
        CL_CHECK(clSetKernelArg(kern, 1, sizeof(cl_ulong), &ns), "arg 1");
        CL_CHECK(clSetKernelArg(kern, 2, sizeof(cl_ulong), &ne), "arg 2");

        CL_CHECK(clEnqueueNDRangeKernel(g->queue, kern, 1, NULL,
                 &gws, NULL, 0, NULL, NULL), "enqueue branch");

        /* Read back and accumulate into 64-bit host arrays */
        CL_CHECK(clEnqueueReadBuffer(g->queue, mem_grids, CL_TRUE, 0,
                 grid_bytes, batch_grids, 0, NULL, NULL), "read grids");

        for (int i = 0; i < grid_cells; i++)
            host_grids[i] += (int64_t)batch_grids[i];

        total_processed += (batch_end - batch_start + 1);

        double dt = now_sec() - t0;
        double rate = (double)total_processed / dt / 1e6;

        /* Compute batch stats from grid totals */
        int64_t batch_even = 0, batch_odd = 0;
        for (int lev = 0; lev < NUM_LEVELS; lev++) {
            /* Use level 0 (k=3) totals as canonical step count */
            if (lev == 0) {
                for (int c = 0; c < K_VAL[0]*K_VAL[0]; c++) {
                    batch_even += batch_grids[E_OFF[0] + c];
                    batch_odd  += batch_grids[O_OFF[0] + c];
                }
            }
        }

        printf("  batch [%" PRIu64 ", %" PRIu64 "] even=%" PRId64
               " odd=%" PRId64 " (%.1fM nums/s)\n",
               batch_start, batch_end, batch_even, batch_odd, rate);
    }

    double total_time = now_sec() - t0;
    char tbuf[32]; fmt_time(total_time, tbuf, sizeof(tbuf));

    /* Print summary */
    printf("\n=== GPU Results (N = %" PRIu64 ") ===\n", N);
    printf("Time: %s (%.1fM nums/s)\n\n", tbuf,
           (double)N / total_time / 1e6);

    for (int lev = 0; lev < num_levels; lev++) {
        int k = K_VAL[lev];
        int64_t total_even = 0, total_odd = 0;
        int branch = 0, pure_even = 0, pure_odd = 0, empty = 0;

        for (int c = 0; c < k*k; c++) {
            int64_t ne = host_grids[E_OFF[lev] + c];
            int64_t no = host_grids[O_OFF[lev] + c];
            total_even += ne;
            total_odd  += no;
            if (ne == 0 && no == 0) empty++;
            else if (ne > 0 && no > 0) branch++;
            else if (no == 0) pure_even++;
            else pure_odd++;
        }

        printf("k=%3d: visits=%" PRId64 " (even=%" PRId64 " odd=%" PRId64
               ") | branch=%d pure_even=%d pure_odd=%d empty=%d\n",
               k, total_even + total_odd, total_even, total_odd,
               branch, pure_even, pure_odd, empty);
    }

    /* CPU comparison */
    if (do_compare) {
        printf("\nRunning CPU reference...\n");

        /* CPU grid layout: for each level, even_grid then odd_grid
         * We use the same flat layout but with 64-bit counters.
         * Level offset = sum of k^2 for prior levels */
        int cpu_level_off[NUM_LEVELS];
        int cpu_total = 0;
        for (int i = 0; i < num_levels; i++) {
            cpu_level_off[i] = cpu_total;
            cpu_total += K_VAL[i] * K_VAL[i];
        }
        int64_t *cpu_even = calloc(cpu_total, sizeof(int64_t));
        int64_t *cpu_odd  = calloc(cpu_total, sizeof(int64_t));

        double tc0 = now_sec();

        for (uint64_t n = 2; n <= N; n++) {
            uint64_t x = n;
            int r2[NUM_LEVELS] = {0}, r3[NUM_LEVELS] = {0};
            while (x > 1) {
                int is_odd = x & 1;
                for (int lev = 0; lev < num_levels; lev++) {
                    int k = K_VAL[lev];
                    int idx = r2[lev] * k + r3[lev];
                    if (is_odd) {
                        cpu_odd[cpu_level_off[lev] + idx]++;
                        if (++r3[lev] == k) r3[lev] = 0;
                    } else {
                        cpu_even[cpu_level_off[lev] + idx]++;
                        if (++r2[lev] == k) r2[lev] = 0;
                    }
                }
                if (is_odd) x = 3*x + 1;
                else        x >>= 1;
            }
        }

        double tc = now_sec() - tc0;
        char tcbuf[32]; fmt_time(tc, tcbuf, sizeof(tcbuf));
        printf("CPU time: %s (%.1fM nums/s)\n\n", tcbuf,
               (double)N / tc / 1e6);

        /* Compare */
        int mismatches = 0;
        for (int lev = 0; lev < num_levels; lev++) {
            int k = K_VAL[lev];
            for (int c = 0; c < k*k; c++) {
                int64_t ge = host_grids[E_OFF[lev] + c];
                int64_t go = host_grids[O_OFF[lev] + c];
                int64_t ce = cpu_even[cpu_level_off[lev] + c];
                int64_t co = cpu_odd[cpu_level_off[lev] + c];
                if (ge != ce || go != co) {
                    if (mismatches < 10) {
                        int r2c = c / k, r3c = c % k;
                        printf("  MISMATCH k=%d (%d,%d): GPU even=%" PRId64
                               " odd=%" PRId64 " vs CPU even=%" PRId64
                               " odd=%" PRId64 "\n",
                               k, r2c, r3c, ge, go, ce, co);
                    }
                    mismatches++;
                }
            }
        }

        if (mismatches == 0)
            printf("*** MATCH: all %d grid cells agree ***\n", grid_cells);
        else
            printf("*** %d MISMATCHES out of %d cells ***\n",
                   mismatches, grid_cells);

        free(cpu_even);
        free(cpu_odd);
    }

    free(host_grids);
    free(batch_grids);
    clReleaseMemObject(mem_grids);
    clReleaseKernel(kern);
}

/* ── Main ───────────────────────────────────────────────────────── */
int main(int argc, char *argv[]) {
    if (argc < 3) {
        fprintf(stderr,
            "Usage: %s <mode> <N>\n"
            "  --verify  N   Convergence verification with checksum\n"
            "  --branch  N   Branch counting for k=3,9,27,81\n"
            "  --fast    N   Fast branch counting, k=3,9,27 only (no global atomics)\n"
            "  --compare N   GPU vs CPU comparison (verify + branch)\n",
            argv[0]);
        return 1;
    }

    const char *mode = argv[1];
    uint64_t N = strtoull(argv[2], NULL, 10);
    if (N < 2) { fprintf(stderr, "N must be >= 2\n"); return 1; }

    compute_offsets();

    /* Find kernel file: look in same directory as executable, then cwd */
    const char *kernel_path = "gpu_branch_kernel.cl";

    gpu_ctx_t gpu;
    gpu_init(&gpu, kernel_path);

    if (strcmp(mode, "--verify") == 0) {
        run_verify(&gpu, N, 0);
    } else if (strcmp(mode, "--branch") == 0) {
        run_branch(&gpu, N, 0, 0);
    } else if (strcmp(mode, "--fast") == 0) {
        run_branch(&gpu, N, 0, 1);
    } else if (strcmp(mode, "--compare") == 0) {
        printf("──── Convergence Verification ────\n");
        run_verify(&gpu, N, 1);
        printf("\n──── Branch Counting (k=3,9,27) ────\n");
        run_branch(&gpu, N, 1, 1);
    } else {
        fprintf(stderr, "Unknown mode: %s\n", mode);
        gpu_cleanup(&gpu);
        return 1;
    }

    gpu_cleanup(&gpu);
    return 0;
}
