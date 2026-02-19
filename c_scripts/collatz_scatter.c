/*
 * collatz_scatter.c — Collatz Total Stopping Time Scatter Plot
 * =============================================================
 * Pure C with cairo. Uses density accumulation for efficient
 * rendering of 100M+ points.
 *
 * Compile:
 *   gcc -O3 -march=native -o collatz_scatter collatz_scatter.c \
 *       $(pkg-config --cflags --libs cairo) -lm
 *
 * Run:
 *   ./collatz_scatter [MAX_N] [STEP]
 *   defaults: MAX_N=100000000  STEP=1
 */

#include <cairo/cairo.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* ─── Parameters ──────────────────────────────────────────────────── */
#define IMG_W   4000
#define IMG_H   2800

/* Plot area within image (pixels) */
#define PLOT_L  120
#define PLOT_R  (IMG_W - 60)
#define PLOT_T  80
#define PLOT_B  (IMG_H - 100)
#define PLOT_W  (PLOT_R - PLOT_L)
#define PLOT_H  (PLOT_B - PLOT_T)

/* ─── Memoised stopping time ─────────────────────────────────────── */
/* For n up to 100M, sequences can briefly exceed 4*MAX_N.             */
/* We cache values for n < CACHE_SZ in an array; larger values are     */
/* computed on the fly (they're rare transients).                       */

static int32_t *stop_cache = NULL;
static int64_t  cache_sz   = 0;

static int stopping_time_iterative(int64_t n)
{
    /* Iterative with stack to avoid deep recursion */
    /* Walk until we hit a cached value, then backfill */
    static int64_t stack[2048];
    int sp = 0;
    int64_t cur = n;

    while (cur != 1 && !(cur < cache_sz && stop_cache[cur] > 0)) {
        if (sp < 2048) stack[sp++] = cur;
        cur = (cur & 1) ? 3 * cur + 1 : cur >> 1;
    }

    int steps = (cur == 1) ? 0 : stop_cache[cur];
    for (int i = sp - 1; i >= 0; i--) {
        steps++;
        if (stack[i] < cache_sz)
            stop_cache[stack[i]] = steps;
    }
    return steps;
}

/* ─── Density accumulator ─────────────────────────────────────────── */
/* 2D histogram: density[y * PLOT_W + x] = count of points at pixel   */
static uint32_t *density = NULL;

/* ================================================================== */
int main(int argc, char **argv)
{
    int64_t MAX_N = 100000000LL;  /* 100 million */
    int     STEP  = 1;

    if (argc > 1) MAX_N = atoll(argv[1]);
    if (argc > 2) STEP  = atoi(argv[2]);
    if (STEP < 1) STEP = 1;

    int64_t n_points = (MAX_N - 1) / STEP + 1;
    printf("Collatz Scatter: MAX_N=%lld  STEP=%d  (%lld points)\n",
           (long long)MAX_N, STEP, (long long)n_points);

    struct timespec t0, t1, t2;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    /* ── 1. Allocate cache ─────────────────────────────────────────── */
    cache_sz = MAX_N + 1;
    /* For very large MAX_N, cap cache and accept some recomputation */
    if (cache_sz > 500000000LL) cache_sz = 500000000LL;

    stop_cache = calloc(cache_sz, sizeof(int32_t));
    if (!stop_cache) {
        fprintf(stderr, "Cannot allocate %lld bytes for cache\n",
                (long long)(cache_sz * sizeof(int32_t)));
        return 1;
    }

    /* ── 2. Compute stopping times & find max ──────────────────────── */
    printf("  Computing stopping times...\n");
    int max_steps = 0;

    /* First pass: compute all and find max_steps */
    /* We'll store results in stop_cache for n < cache_sz */
    for (int64_t n = 2; n <= MAX_N; n++) {
        if (n < cache_sz && stop_cache[n] > 0) {
            if (stop_cache[n] > max_steps) max_steps = stop_cache[n];
            continue;
        }
        int s = stopping_time_iterative(n);
        if (s > max_steps) max_steps = s;

        if (n % 20000000 == 0) {
            clock_gettime(CLOCK_MONOTONIC, &t1);
            double el = (t1.tv_sec - t0.tv_sec) +
                        (t1.tv_nsec - t0.tv_nsec) * 1e-9;
            printf("    %lld / %lld  (%.1fs)\n",
                   (long long)n, (long long)MAX_N, el);
        }
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double compute_time = (t1.tv_sec - t0.tv_sec) +
                          (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("  Done in %.2fs. max_steps=%d\n", compute_time, max_steps);

    /* ── 3. Accumulate density into pixel grid ─────────────────────── */
    printf("  Accumulating density...\n");
    density = calloc((size_t)PLOT_W * PLOT_H, sizeof(uint32_t));
    if (!density) { fprintf(stderr, "Cannot alloc density\n"); return 1; }

    uint32_t max_density = 0;
    int64_t  max_stop_n  = 0;

    for (int64_t n = 1; n <= MAX_N; n += STEP) {
        int s;
        if (n == 1) s = 0;
        else if (n < cache_sz) s = stop_cache[n];
        else s = stopping_time_iterative(n);

        if (s > 0 && n > max_stop_n && s == max_steps)
            max_stop_n = n;

        /* Map to pixel coordinates */
        int px = (int)((double)(n - 1) / (double)(MAX_N - 1) * (PLOT_W - 1));
        int py = (int)((double)s / (double)(max_steps) * (PLOT_H - 1));
        py = (PLOT_H - 1) - py;  /* flip Y: high steps at top */

        if (px >= 0 && px < PLOT_W && py >= 0 && py < PLOT_H) {
            uint32_t d = ++density[py * PLOT_W + px];
            if (d > max_density) max_density = d;
        }
    }
    printf("  max_density=%u at max_stop n=%lld\n",
           max_density, (long long)max_stop_n);

    /* ── 4. Render with Cairo ──────────────────────────────────────── */
    printf("  Rendering %dx%d...\n", IMG_W, IMG_H);
    cairo_surface_t *surface = cairo_image_surface_create(
        CAIRO_FORMAT_ARGB32, IMG_W, IMG_H);
    cairo_t *cr = cairo_create(surface);

    /* Black background */
    cairo_set_source_rgb(cr, 0, 0, 0);
    cairo_paint(cr);

    /* Render density map as red dots with brightness = log(density) */
    double log_max = log((double)max_density + 1.0);

    /* Get direct pixel access for speed */
    cairo_surface_flush(surface);
    unsigned char *data = cairo_image_surface_get_data(surface);
    int stride = cairo_image_surface_get_stride(surface);

    for (int py = 0; py < PLOT_H; py++) {
        for (int px = 0; px < PLOT_W; px++) {
            uint32_t d = density[py * PLOT_W + px];
            if (d == 0) continue;

            double t = log((double)d + 1.0) / log_max;
            /* Red channel intensity with slight glow effect */
            int r = (int)(40 + 215 * t);
            int g = (int)(5 + 25 * t * t);     /* slight warm tint */
            int b = (int)(5 + 10 * t * t * t);
            if (r > 255) r = 255;
            if (g > 255) g = 255;
            if (b > 255) b = 255;

            int ix = PLOT_L + px;
            int iy = PLOT_T + py;

            /* ARGB32 in native byte order (little-endian: BGRA) */
            unsigned char *p = data + iy * stride + ix * 4;
            p[0] = (unsigned char)b;
            p[1] = (unsigned char)g;
            p[2] = (unsigned char)r;
            p[3] = 255;

            /* Optional: add 1-pixel glow for high-density points */
            if (t > 0.3) {
                int gr = (int)(r * 0.3);
                int gg = (int)(g * 0.3);
                int gb = (int)(b * 0.3);
                int dx[] = {-1, 1, 0, 0};
                int dy[] = {0, 0, -1, 1};
                for (int k = 0; k < 4; k++) {
                    int nx = ix + dx[k], ny = iy + dy[k];
                    if (nx < 0 || nx >= IMG_W || ny < 0 || ny >= IMG_H)
                        continue;
                    unsigned char *q = data + ny * stride + nx * 4;
                    /* Additive blend */
                    int cb = q[0] + gb; if (cb > 255) cb = 255;
                    int cg = q[1] + gg; if (cg > 255) cg = 255;
                    int crr= q[2] + gr; if (crr> 255) crr= 255;
                    q[0] = cb; q[1] = cg; q[2] = crr; q[3] = 255;
                }
            }
        }
    }
    cairo_surface_mark_dirty(surface);

    /* ── 5. Axes and labels ───────────────────────────────────────── */
    /* Axes lines */
    cairo_set_source_rgb(cr, 0.3, 0.3, 0.3);
    cairo_set_line_width(cr, 1.5);
    cairo_move_to(cr, PLOT_L, PLOT_T);
    cairo_line_to(cr, PLOT_L, PLOT_B);
    cairo_line_to(cr, PLOT_R, PLOT_B);
    cairo_stroke(cr);

    /* Tick marks and labels */
    cairo_select_font_face(cr, "monospace",
        CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_NORMAL);
    cairo_set_font_size(cr, 18);
    cairo_set_source_rgb(cr, 0.6, 0.6, 0.6);

    /* X-axis ticks */
    for (int i = 0; i <= 10; i++) {
        double frac = i / 10.0;
        int px = PLOT_L + (int)(frac * PLOT_W);
        cairo_move_to(cr, px, PLOT_B);
        cairo_line_to(cr, px, PLOT_B + 8);
        cairo_stroke(cr);

        char buf[32];
        int64_t val = (int64_t)(frac * MAX_N);
        if (val >= 1000000)
            snprintf(buf, sizeof(buf), "%lldM", (long long)(val / 1000000));
        else if (val >= 1000)
            snprintf(buf, sizeof(buf), "%lldk", (long long)(val / 1000));
        else
            snprintf(buf, sizeof(buf), "%lld", (long long)val);
        cairo_move_to(cr, px - 15, PLOT_B + 28);
        cairo_show_text(cr, buf);
    }

    /* Y-axis ticks */
    int y_step = (max_steps > 500) ? 100 : 50;
    for (int s = 0; s <= max_steps; s += y_step) {
        double frac = (double)s / max_steps;
        int py = PLOT_B - (int)(frac * PLOT_H);
        cairo_move_to(cr, PLOT_L - 8, py);
        cairo_line_to(cr, PLOT_L, py);
        cairo_stroke(cr);

        /* Grid line */
        cairo_set_source_rgba(cr, 0.3, 0.3, 0.3, 0.3);
        cairo_move_to(cr, PLOT_L, py);
        cairo_line_to(cr, PLOT_R, py);
        cairo_stroke(cr);
        cairo_set_source_rgb(cr, 0.6, 0.6, 0.6);

        char buf[16];
        snprintf(buf, sizeof(buf), "%d", s);
        cairo_move_to(cr, PLOT_L - 60, py + 5);
        cairo_show_text(cr, buf);
    }

    /* Axis labels */
    cairo_select_font_face(cr, "serif",
        CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_NORMAL);
    cairo_set_font_size(cr, 20);
    cairo_set_source_rgb(cr, 0.8, 0.8, 0.8);
    cairo_move_to(cr, PLOT_L + PLOT_W / 2 - 80, PLOT_B + 60);
    cairo_show_text(cr, "Starting number n");

    /* Y label (rotated) */
    cairo_save(cr);
    cairo_translate(cr, 30, PLOT_T + PLOT_H / 2 + 100);
    cairo_rotate(cr, -M_PI / 2);
    cairo_move_to(cr, 0, 0);
    cairo_show_text(cr, "Total stopping time (steps to reach 1)");
    cairo_restore(cr);

    /* Title */
    cairo_select_font_face(cr, "serif",
        CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_BOLD);
    cairo_set_font_size(cr, 30);
    cairo_set_source_rgb(cr, 1, 1, 1);
    {
        char title[128];
        if (MAX_N >= 1000000000LL)
            snprintf(title, sizeof(title),
                     "Collatz Total Stopping Times for n = 1 to %lldB",
                     (long long)(MAX_N / 1000000000LL));
        else if (MAX_N >= 1000000LL)
            snprintf(title, sizeof(title),
                     "Collatz Total Stopping Times for n = 1 to %lldM",
                     (long long)(MAX_N / 1000000LL));
        else
            snprintf(title, sizeof(title),
                     "Collatz Total Stopping Times for n = 1 to %lld",
                     (long long)MAX_N);
        cairo_move_to(cr, PLOT_L + PLOT_W / 2 - 280, PLOT_T - 30);
        cairo_show_text(cr, title);
    }

    /* Highlight annotations */
    typedef struct { int64_t n; int steps; const char *label; } Highlight;
    Highlight highlights[] = {
        {837799,   524, "837,799 (524)"},
        {8400511,  685, "8,400,511 (685)"},
        {63728127, 949, "63,728,127 (949)"},
        {0, 0, NULL}
    };

    cairo_set_font_size(cr, 15);
    for (int i = 0; highlights[i].label; i++) {
        int64_t hn = highlights[i].n;
        int     hs = highlights[i].steps;
        if (hn > MAX_N) continue;

        int px = PLOT_L + (int)((double)(hn - 1) / (MAX_N - 1) * (PLOT_W - 1));
        int py = PLOT_B - (int)((double)hs / max_steps * (PLOT_H - 1));

        /* Marker */
        cairo_set_source_rgb(cr, 1, 0.84, 0);
        cairo_arc(cr, px, py, 4, 0, 2 * M_PI);
        cairo_fill(cr);

        /* Label with arrow */
        cairo_set_source_rgb(cr, 1, 0.84, 0);
        cairo_move_to(cr, px + 8, py - 8);
        cairo_show_text(cr, highlights[i].label);
    }

    /* ── 6. Write PNG ─────────────────────────────────────────────── */
    const char *outpath = "collatz_scatter.png";
    cairo_status_t st = cairo_surface_write_to_png(surface, outpath);
    cairo_destroy(cr);
    cairo_surface_destroy(surface);
    free(density);
    free(stop_cache);

    clock_gettime(CLOCK_MONOTONIC, &t2);
    double total = (t2.tv_sec - t0.tv_sec) + (t2.tv_nsec - t0.tv_nsec) * 1e-9;

    if (st == CAIRO_STATUS_SUCCESS)
        printf("  Saved: %s (compute=%.2fs  total=%.2fs)\n",
               outpath, compute_time, total);
    else
        fprintf(stderr, "Error: %s\n", cairo_status_to_string(st));

    return 0;
}
