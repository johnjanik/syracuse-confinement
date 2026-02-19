/*
 * collatz_tree_anim.c — Animated Collatz Tree Growth
 * ====================================================
 * Renders one PNG frame per FRAME_INTERVAL starting points.
 * Uses splitmix64 for prefix-consistent quasi-random starting points:
 *   start[i] is the same for all N >= i, so the first K frames of a
 *   50-frame run are identical to the first K frames of a 500-frame run.
 *
 * Compile:
 *   gcc -O3 -march=native -o collatz_tree_anim collatz_tree_anim.c \
 *       $(pkg-config --cflags --libs cairo) -lm
 *
 * Run:
 *   ./collatz_tree_anim [N] [MAX_START] [SEED] [FRAME_INTERVAL] [OUT_DIR]
 *   defaults: N=100000  MAX_START=10000000  SEED=42  FRAME_INTERVAL=2000  OUT_DIR=frames
 *
 * Then:
 *   ffmpeg -framerate 30 -i frames/frame_%06d.png -c:v libx264 \
 *          -pix_fmt yuv420p -crf 18 collatz_tree.mp4
 */

#include <cairo/cairo.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/stat.h>
#include <sys/types.h>

/* ─── Visual parameters (same as original static version) ────────── */
#define ANGLE_EVEN_DEG   8.65
#define ANGLE_ODD_DEG   16.0
#define EDGE_SCALE_K    12.0
#define THICKNESS_MIN    0.25
#define THICKNESS_MAX    4.0
#define ROTATION_DEG   -50.0

/* Image size — 1920x1080 for animation; recompile with
 *   -DIMG_W=3840 -DIMG_H=2160  for 4K */
#ifndef IMG_W
#define IMG_W  1920
#endif
#ifndef IMG_H
#define IMG_H  1080
#endif

/* Background */
#define BG_R 0.980
#define BG_G 0.973
#define BG_B 0.961

/* ─── splitmix64: prefix-consistent quasi-random generator ───────── *
 * start[i] = f(SEED, i) is deterministic and independent of N,      *
 * so the first K frames are identical whether you render K or 10K.   */
static inline uint64_t splitmix64(uint64_t z)
{
    z += 0x9e3779b97f4a7c15ULL;
    z  = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z  = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static inline int64_t quasi_random_start(uint64_t seed, int64_t index,
                                         int64_t max_start)
{
    uint64_t h = splitmix64(seed * 0x517cc1b727220a95ULL + (uint64_t)index);
    return (int64_t)(h % (uint64_t)max_start) + 1;
}

/* ─── Dynamic int64 vector ───────────────────────────────────────── */
typedef struct { int64_t *d; int len, cap; } i64vec;

static void vec_init(i64vec *v, int c)
{
    v->d = malloc(c * sizeof(int64_t));
    v->len = 0;  v->cap = c;
}
static void vec_push(i64vec *v, int64_t x)
{
    if (v->len == v->cap) {
        v->cap *= 2;
        v->d = realloc(v->d, v->cap * sizeof(int64_t));
    }
    v->d[v->len++] = x;
}
static void vec_free(i64vec *v) { free(v->d); v->d = NULL; }

/* ─── Edge hash table (heap-allocated, open addressing) ──────────── */
typedef struct { int64_t parent, child; int freq; } EdgeEntry;

static EdgeEntry *g_eht;
static int        g_eht_cap, g_eht_mask;
static int        g_eht_used = 0;

static inline uint64_t edge_hash(int64_t a, int64_t b)
{
    return (uint64_t)a * 2654435761ULL ^ (uint64_t)b * 40503ULL;
}

static int edge_add(int64_t parent, int64_t child)
{
    uint64_t h = edge_hash(parent, child) & g_eht_mask;
    for (;;) {
        if (g_eht[h].freq == 0) {
            g_eht[h].parent = parent;
            g_eht[h].child  = child;
            g_eht[h].freq   = 1;
            g_eht_used++;
            return 1;
        }
        if (g_eht[h].parent == parent && g_eht[h].child == child) {
            g_eht[h].freq++;
            return 0;
        }
        h = (h + 1) & g_eht_mask;
    }
}

/* ─── Node position table (heap, cleared & rebuilt each frame) ───── */
typedef struct { int64_t id; double x, y, angle; int filled; } NodeEntry;

static NodeEntry *g_nht;
static int        g_nht_cap, g_nht_mask;

static NodeEntry *node_find(int64_t id)
{
    uint64_t h = (uint64_t)id * 2654435761ULL & g_nht_mask;
    for (;;) {
        if (!g_nht[h].filled) return NULL;
        if (g_nht[h].id == id)  return &g_nht[h];
        h = (h + 1) & g_nht_mask;
    }
}

static NodeEntry *node_insert(int64_t id, double x, double y, double a)
{
    uint64_t h = (uint64_t)id * 2654435761ULL & g_nht_mask;
    for (;;) {
        if (!g_nht[h].filled) {
            g_nht[h].id = id; g_nht[h].x = x; g_nht[h].y = y;
            g_nht[h].angle = a; g_nht[h].filled = 1;
            return &g_nht[h];
        }
        if (g_nht[h].id == id) return &g_nht[h];
        h = (h + 1) & g_nht_mask;
    }
}

/* ─── Children adjacency (dynamic array, sorted for BFS) ────────── */
typedef struct { int64_t parent, child; } ChildPair;

static ChildPair *g_ch;
static int        g_nch = 0, g_chcap;

/* Sort by (parent, child) — deterministic across frames */
static int cmp_child(const void *a, const void *b)
{
    const ChildPair *ca = a, *cb = b;
    if (ca->parent != cb->parent)
        return (ca->parent > cb->parent) - (ca->parent < cb->parent);
    return (ca->child > cb->child) - (ca->child < cb->child);
}

static void child_add(int64_t parent, int64_t child)
{
    if (g_nch == g_chcap) {
        g_chcap *= 2;
        g_ch = realloc(g_ch, g_chcap * sizeof(ChildPair));
    }
    g_ch[g_nch++] = (ChildPair){parent, child};
}

/* ─── Colormap: dark purple → red → orange → gold ────────────────── */
typedef struct { double r, g, b; } RGB;

static const RGB cmap[] = {
    {0.102, 0.039, 0.180},
    {0.239, 0.110, 0.431},
    {0.420, 0.184, 0.627},
    {0.608, 0.137, 0.208},
    {0.769, 0.118, 0.227},
    {0.910, 0.271, 0.110},
    {0.957, 0.518, 0.176},
    {0.961, 0.651, 0.137},
    {0.988, 0.788, 0.388},
    {0.992, 0.910, 0.690},
};
#define CMAP_N 10

static RGB cmap_sample(double t)
{
    if (t <= 0.0) return cmap[0];
    if (t >= 1.0) return cmap[CMAP_N - 1];
    double f = t * (CMAP_N - 1);
    int    i = (int)f;
    double u = f - i;
    if (i >= CMAP_N - 1) return cmap[CMAP_N - 1];
    return (RGB){
        cmap[i].r + u*(cmap[i+1].r - cmap[i].r),
        cmap[i].g + u*(cmap[i+1].g - cmap[i].g),
        cmap[i].b + u*(cmap[i+1].b - cmap[i].b),
    };
}

/* ─── Drawable edge (for sorted rendering) ───────────────────────── */
typedef struct { double x0, y0, x1, y1, freq_log; } DrawEdge;

static int cmp_draw(const void *a, const void *b)
{
    double fa = ((const DrawEdge *)a)->freq_log;
    double fb = ((const DrawEdge *)b)->freq_log;
    return (fa > fb) - (fa < fb);
}

/* ─── Number formatting with commas ──────────────────────────────── */
static void fmt_num(char *buf, int64_t n)
{
    if (n >= 1000000000LL)
        snprintf(buf, 64, "%lld,%03lld,%03lld,%03lld",
                 (long long)(n/1000000000LL), (long long)((n/1000000)%1000),
                 (long long)((n/1000)%1000), (long long)(n%1000));
    else if (n >= 1000000)
        snprintf(buf, 64, "%lld,%03lld,%03lld",
                 (long long)(n/1000000), (long long)((n/1000)%1000),
                 (long long)(n%1000));
    else if (n >= 1000)
        snprintf(buf, 64, "%lld,%03lld",
                 (long long)(n/1000), (long long)(n%1000));
    else
        snprintf(buf, 64, "%lld", (long long)n);
}

/* ─── Next power of 2 >= v ───────────────────────────────────────── */
static int next_pow2(int v)
{
    v--; v|=v>>1; v|=v>>2; v|=v>>4; v|=v>>8; v|=v>>16;
    return v + 1;
}

/* ═══════════════════════════════════════════════════════════════════ */
int main(int argc, char **argv)
{
    /* ── Defaults ─────────────────────────────────────────────────── */
    int     N              = 100000;
    int64_t MAX_START      = 10000000LL;
    int     SEED           = 42;
    int     FRAME_INTERVAL = 2000;
    const char *OUT_DIR    = "frames";

    if (argc > 1) N              = atoi(argv[1]);
    if (argc > 2) MAX_START      = atoll(argv[2]);
    if (argc > 3) SEED           = atoi(argv[3]);
    if (argc > 4) FRAME_INTERVAL = atoi(argv[4]);
    if (argc > 5) OUT_DIR        = argv[5];

    int total_frames = (N + FRAME_INTERVAL - 1) / FRAME_INTERVAL;

    printf("======================================================\n");
    printf("  Collatz Tree Animation\n");
    printf("======================================================\n");
    printf("  N              = %d\n", N);
    printf("  MAX_START      = %lld\n", (long long)MAX_START);
    printf("  SEED           = %d\n", SEED);
    printf("  FRAME_INTERVAL = %d\n", FRAME_INTERVAL);
    printf("  Total frames   = %d\n", total_frames);
    printf("  Image size     = %d x %d\n", IMG_W, IMG_H);
    printf("  Output dir     = %s/\n", OUT_DIR);
    printf("======================================================\n");

    struct timespec t0, t_frame;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    /* ── Create output directory ──────────────────────────────────── */
    mkdir(OUT_DIR, 0755);

    /* ── Allocate hash tables (sized for < 25%% load) ─────────────── */
    int ht_size = next_pow2(N < 250000 ? (1 << 20) : N * 4);
    if (ht_size > (1 << 26)) ht_size = (1 << 26);

    g_eht_cap = ht_size;  g_eht_mask = ht_size - 1;
    g_nht_cap = ht_size;  g_nht_mask = ht_size - 1;

    g_eht = calloc(g_eht_cap, sizeof(EdgeEntry));
    g_nht = calloc(g_nht_cap, sizeof(NodeEntry));
    if (!g_eht || !g_nht) {
        fprintf(stderr, "Failed to allocate hash tables (%d entries)\n", ht_size);
        return 1;
    }

    g_chcap = N < 250000 ? (1 << 20) : N * 4;
    g_ch    = malloc(g_chcap * sizeof(ChildPair));

    int bfs_cap = ht_size;
    int64_t *bfs_q = malloc(bfs_cap * sizeof(int64_t));

    printf("  Hash table buckets: %d  (edge %.0f MB, node %.0f MB)\n",
           ht_size,
           ht_size * (double)sizeof(EdgeEntry) / (1<<20),
           ht_size * (double)sizeof(NodeEntry) / (1<<20));

    /* ── Precomputed constants ────────────────────────────────────── */
    double angle_even = ANGLE_EVEN_DEG * M_PI / 180.0;
    double angle_odd  = ANGLE_ODD_DEG  * M_PI / 180.0;
    double rot        = ROTATION_DEG   * M_PI / 180.0;
    double cosR = cos(rot), sinR = sin(rot);

    /* ── Running state ────────────────────────────────────────────── */
    int64_t longest_start = 0;
    int     longest_len   = 0;
    int     starts_done   = 0;
    int     frame_num     = 0;

    /* Running bounding box — only grows → smooth camera */
    double rbb_xmin =  1e18, rbb_xmax = -1e18;
    double rbb_ymin =  1e18, rbb_ymax = -1e18;

    i64vec seq;
    vec_init(&seq, 2048);

    /* ═══ MAIN LOOP ═══════════════════════════════════════════════ */
    while (starts_done < N) {
        clock_gettime(CLOCK_MONOTONIC, &t_frame);

        int batch = FRAME_INTERVAL;
        if (starts_done + batch > N) batch = N - starts_done;

        /* ── 1. Process this batch: generate starts, trace, add edges */
        for (int bi = 0; bi < batch; bi++) {
            int64_t n = quasi_random_start(SEED, starts_done + bi, MAX_START);

            seq.len = 0;
            vec_push(&seq, n);
            int64_t cur = n;
            while (cur != 1) {
                cur = (cur & 1) ? 3*cur + 1 : cur >> 1;
                vec_push(&seq, cur);
            }

            int plen = seq.len - 1;
            if (plen > longest_len) {
                longest_len   = plen;
                longest_start = n;
            }

            /* Reversed edges: 1 → ... → n */
            for (int i = seq.len - 1; i > 0; i--) {
                int64_t par = seq.d[i], chi = seq.d[i-1];
                if (edge_add(par, chi))
                    child_add(par, chi);
            }
        }
        starts_done += batch;
        frame_num++;

        /* ── 2. Sort children for deterministic BFS ──────────────── */
        qsort(g_ch, g_nch, sizeof(ChildPair), cmp_child);

        /* ── 3. BFS from root → positions ────────────────────────── */
        memset(g_nht, 0, (size_t)g_nht_cap * sizeof(NodeEntry));

        node_insert(1, 0.0, 0.0, M_PI / 2.0);
        int qh = 0, qt = 0;
        bfs_q[qt++] = 1;

        while (qh < qt) {
            int64_t nd = bfs_q[qh++];
            NodeEntry *pn = node_find(nd);
            if (!pn) continue;
            double px = pn->x, py = pn->y, hd = pn->angle;

            /* binary search for first child of nd */
            int lo = 0, hi = g_nch;
            while (lo < hi) {
                int mid = (lo + hi) >> 1;
                if (g_ch[mid].parent < nd) lo = mid + 1;
                else hi = mid;
            }
            for (int ci = lo; ci < g_nch && g_ch[ci].parent == nd; ci++) {
                int64_t ch = g_ch[ci].child;
                if (node_find(ch)) continue;

                double nh = (ch % 2 == 0)
                          ? hd + angle_even
                          : hd - angle_odd;
                double el = EDGE_SCALE_K / log10((double)ch + 1.0);
                double cx = px + el * cos(nh);
                double cy = py + el * sin(nh);

                node_insert(ch, cx, cy, nh);
                if (qt < bfs_cap) bfs_q[qt++] = ch;
            }
        }
        int n_nodes = qt;

        /* ── 4. Rotate all coordinates ───────────────────────────── */
        for (int i = 0; i < g_nht_cap; i++) {
            if (!g_nht[i].filled) continue;
            double x = g_nht[i].x, y = g_nht[i].y;
            g_nht[i].x = x*cosR - y*sinR;
            g_nht[i].y = x*sinR + y*cosR;
        }

        /* ── 5. Update running bounding box (monotone growth) ─────  */
        for (int i = 0; i < g_nht_cap; i++) {
            if (!g_nht[i].filled) continue;
            double x = g_nht[i].x, y = g_nht[i].y;
            if (x < rbb_xmin) rbb_xmin = x;
            if (x > rbb_xmax) rbb_xmax = x;
            if (y < rbb_ymin) rbb_ymin = y;
            if (y > rbb_ymax) rbb_ymax = y;
        }

        double xr = rbb_xmax - rbb_xmin;
        double yr = rbb_ymax - rbb_ymin;
        if (xr < 1.0) xr = 1.0;
        if (yr < 1.0) yr = 1.0;

        double pad = 0.06;
        double vx0 = rbb_xmin - xr*pad, vx1 = rbb_xmax + xr*pad;
        double vy0 = rbb_ymin - yr*pad, vy1 = rbb_ymax + yr*pad;
        double vxr = vx1 - vx0, vyr = vy1 - vy0;

        double sx = (IMG_W - 40.0) / vxr;
        double sy = (IMG_H - 40.0) / vyr;
        double sc = sx < sy ? sx : sy;
        double ox = 20.0 + ((IMG_W - 40) - vxr*sc) / 2.0;
        double oy = 20.0 + ((IMG_H - 40) - vyr*sc) / 2.0;

        /* coordinate mapping macros (scope: this iteration only) */
        #define MX(wx) (ox + ((wx) - vx0) * sc)
        #define MY(wy) (oy + (vy1 - (wy)) * sc)

        /* ── 6. Collect drawable edges ───────────────────────────── */
        DrawEdge *draw = malloc(g_eht_used * sizeof(DrawEdge));
        int n_draw = 0;
        double max_fl = 0;

        for (int i = 0; i < g_eht_cap; i++) {
            if (g_eht[i].freq == 0) continue;
            NodeEntry *np = node_find(g_eht[i].parent);
            NodeEntry *nc = node_find(g_eht[i].child);
            if (!np || !nc) continue;

            double fl = log10((double)g_eht[i].freq + 1.0);
            if (fl > max_fl) max_fl = fl;
            draw[n_draw++] = (DrawEdge){np->x, np->y, nc->x, nc->y, fl};
        }
        /* low-freq first → high-freq drawn on top */
        qsort(draw, n_draw, sizeof(DrawEdge), cmp_draw);

        /* ── 7. Render with Cairo ────────────────────────────────── */
        cairo_surface_t *surf = cairo_image_surface_create(
            CAIRO_FORMAT_ARGB32, IMG_W, IMG_H);
        cairo_t *cr = cairo_create(surf);

        /* background */
        cairo_set_source_rgb(cr, BG_R, BG_G, BG_B);
        cairo_paint(cr);
        cairo_set_line_cap(cr, CAIRO_LINE_CAP_ROUND);
        cairo_set_antialias(cr, CAIRO_ANTIALIAS_FAST);

        /* draw edges */
        for (int i = 0; i < n_draw; i++) {
            double t  = max_fl > 0 ? draw[i].freq_log / max_fl : 0;
            double lw = THICKNESS_MIN + (THICKNESS_MAX - THICKNESS_MIN)*t;
            RGB c     = cmap_sample(t);
            cairo_set_line_width(cr, lw);
            cairo_set_source_rgba(cr, c.r, c.g, c.b, 0.85);
            cairo_move_to(cr, MX(draw[i].x0), MY(draw[i].y0));
            cairo_line_to(cr, MX(draw[i].x1), MY(draw[i].y1));
            cairo_stroke(cr);
        }

        /* highlight longest path */
        {
            i64vec hl; vec_init(&hl, 1024);
            int64_t c2 = longest_start;
            vec_push(&hl, c2);
            while (c2 != 1) {
                c2 = (c2 & 1) ? 3*c2 + 1 : c2 >> 1;
                vec_push(&hl, c2);
            }
            cairo_set_line_width(cr, 1.0);
            cairo_set_source_rgba(cr, 0.769, 0.118, 0.227, 0.50);
            for (int i = hl.len - 1; i > 0; i--) {
                NodeEntry *na = node_find(hl.d[i]);
                NodeEntry *nb = node_find(hl.d[i-1]);
                if (na && nb) {
                    cairo_move_to(cr, MX(na->x), MY(na->y));
                    cairo_line_to(cr, MX(nb->x), MY(nb->y));
                    cairo_stroke(cr);
                }
            }
            vec_free(&hl);
        }

        /* ── 8. Annotations ──────────────────────────────────────── */
        /* title — upper left */
        cairo_select_font_face(cr, "sans-serif",
            CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_BOLD);
        cairo_set_font_size(cr, 28);
        cairo_set_source_rgb(cr, 0.102, 0.039, 0.180);
        cairo_move_to(cr, 20, 36);
        cairo_show_text(cr, "Collatz conjecture paths");

        /* progress info — below title */
        cairo_set_font_size(cr, 16);
        cairo_set_source_rgb(cr, 0.239, 0.110, 0.431);
        {
            char s1[64], s2[64], s3[64], s4[64], info[320];
            fmt_num(s1, starts_done);
            fmt_num(s2, (int64_t)N);
            fmt_num(s3, MAX_START);
            fmt_num(s4, (int64_t)g_eht_used);
            snprintf(info, sizeof(info),
                "%s / %s paths  |  range [1, %s]  |  %s edges  |  %d nodes",
                s1, s2, s3, s4, n_nodes);
            cairo_move_to(cr, 20, 58);
            cairo_show_text(cr, info);
        }

        /* longest path label at its tip */
        {
            NodeEntry *ne = node_find(longest_start);
            if (ne) {
                cairo_set_source_rgb(cr, 0.831, 0.627, 0.090);
                cairo_set_font_size(cr, 13);
                char buf[128];
                snprintf(buf, sizeof(buf), "%lld (%d steps)",
                         (long long)longest_start, longest_len);
                cairo_move_to(cr, MX(ne->x)+6, MY(ne->y));
                cairo_show_text(cr, buf);
            }
        }

        /* frame counter — lower right */
        cairo_set_font_size(cr, 14);
        cairo_set_source_rgba(cr, 0.353, 0.239, 0.478, 0.7);
        {
            char fb[64];
            snprintf(fb, sizeof(fb), "frame %d / %d", frame_num, total_frames);
            cairo_text_extents_t ext;
            cairo_text_extents(cr, fb, &ext);
            cairo_move_to(cr, IMG_W - ext.width - 16, IMG_H - 12);
            cairo_show_text(cr, fb);
        }

        /* progress bar — bottom edge */
        {
            double frac = (double)starts_done / (double)N;
            cairo_set_source_rgba(cr, 0.420, 0.184, 0.627, 0.35);
            cairo_rectangle(cr, 20, IMG_H - 6, (IMG_W - 40)*frac, 4);
            cairo_fill(cr);
        }

        /* ── 9. Write PNG ────────────────────────────────────────── */
        char path[512];
        snprintf(path, sizeof(path), "%s/frame_%06d.png",
                 OUT_DIR, frame_num);
        cairo_surface_write_to_png(surf, path);
        cairo_destroy(cr);
        cairo_surface_destroy(surf);
        free(draw);

        #undef MX
        #undef MY

        /* ── 10. Progress to stdout ──────────────────────────────── */
        struct timespec now;
        clock_gettime(CLOCK_MONOTONIC, &now);
        double elapsed = (now.tv_sec  - t0.tv_sec)
                       + (now.tv_nsec - t0.tv_nsec) * 1e-9;
        double ft      = (now.tv_sec  - t_frame.tv_sec)
                       + (now.tv_nsec - t_frame.tv_nsec) * 1e-9;
        double eta     = elapsed / frame_num * (total_frames - frame_num);

        printf("  frame %4d/%-4d  starts=%-9d  edges=%-8d  "
               "nodes=%-8d  %.2fs/fr  ETA %.0fs\n",
               frame_num, total_frames, starts_done,
               g_eht_used, n_nodes, ft, eta);
    }

    /* ═══ Done ════════════════════════════════════════════════════ */
    struct timespec t1;
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double total = (t1.tv_sec  - t0.tv_sec)
                 + (t1.tv_nsec - t0.tv_nsec) * 1e-9;

    printf("\n  %d frames written to %s/  (%.1fs total)\n\n",
           frame_num, OUT_DIR, total);
    printf("  To create video:\n\n");
    printf("    ffmpeg -framerate 30 -i %s/frame_%%06d.png \\\n", OUT_DIR);
    printf("           -c:v libx264 -pix_fmt yuv420p -crf 18 \\\n");
    printf("           collatz_tree.mp4\n\n");
    printf("  For slower/dramatic playback (3x slower):\n\n");
    printf("    ffmpeg -framerate 10 -i %s/frame_%%06d.png \\\n", OUT_DIR);
    printf("           -c:v libx264 -pix_fmt yuv420p -crf 18 \\\n");
    printf("           -vf \"fps=30\" collatz_tree_slow.mp4\n\n");

    vec_free(&seq);
    free(g_eht); free(g_nht); free(g_ch); free(bfs_q);
    return 0;
}
