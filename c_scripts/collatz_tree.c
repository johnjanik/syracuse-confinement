/*
 * collatz_tree.c — Collatz Conjecture Path Tree Visualization
 * ============================================================
 * Pure C with cairo for anti-aliased rendering.
 *
 * Compile:
 *   gcc -O3 -march=native -o collatz_tree collatz_tree.c \
 *       $(pkg-config --cflags --libs cairo) -lm
 *
 * Run:
 *   ./collatz_tree [N] [MAX_START] [SEED]
 *   defaults: N=5000  MAX_START=1000000  SEED=42
 */

#include <cairo/cairo.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* ─── Parameters ──────────────────────────────────────────────────── */
#define ANGLE_EVEN_DEG   8.65
#define ANGLE_ODD_DEG   16.0
#define EDGE_SCALE_K    12.0
#define THICKNESS_MIN    0.3
#define THICKNESS_MAX    4.5
#define ROTATION_DEG   -50.0

#define IMG_W  4800
#define IMG_H  2700

/* Background colour */
#define BG_R 0.980
#define BG_G 0.973
#define BG_B 0.961



/* ─── Dynamic array for full sequences ────────────────────────────── */
typedef struct { int64_t *d; int len, cap; } i64vec;

static void vec_init(i64vec *v, int cap)
{
    v->d   = malloc(cap * sizeof(int64_t));
    v->len = 0;
    v->cap = cap;
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

/* ─── Edge hash table (open addressing) ───────────────────────────── */
#define EDGE_HT_CAP (1 << 20)  /* ~1 M buckets */
#define EDGE_HT_MASK (EDGE_HT_CAP - 1)

typedef struct {
    int64_t parent, child;
    int     freq;
} EdgeEntry;

static EdgeEntry edge_ht[EDGE_HT_CAP];
static int       edge_ht_used = 0;

static uint64_t edge_hash(int64_t a, int64_t b)
{
    uint64_t h = (uint64_t)a * 2654435761ULL ^ (uint64_t)b * 40503ULL;
    return h;
}

static int edge_add(int64_t parent, int64_t child)
{
    uint64_t h = edge_hash(parent, child) & EDGE_HT_MASK;
    for (;;) {
        if (edge_ht[h].freq == 0) {
            edge_ht[h].parent = parent;
            edge_ht[h].child  = child;
            edge_ht[h].freq   = 1;
            edge_ht_used++;
            return 1;
        }
        if (edge_ht[h].parent == parent && edge_ht[h].child == child) {
            edge_ht[h].freq++;
            return 0;
        }
        h = (h + 1) & EDGE_HT_MASK;
    }
}

/* ─── Node position hash table ────────────────────────────────────── */
#define NODE_HT_CAP (1 << 20)
#define NODE_HT_MASK (NODE_HT_CAP - 1)

typedef struct {
    int64_t id;
    double  x, y, angle;
    int     filled;
} NodeEntry;

static NodeEntry node_ht[NODE_HT_CAP];

static NodeEntry *node_find(int64_t id)
{
    uint64_t h = (uint64_t)id * 2654435761ULL & NODE_HT_MASK;
    for (;;) {
        if (!node_ht[h].filled) return NULL;
        if (node_ht[h].id == id) return &node_ht[h];
        h = (h + 1) & NODE_HT_MASK;
    }
}

static NodeEntry *node_insert(int64_t id, double x, double y, double angle)
{
    uint64_t h = (uint64_t)id * 2654435761ULL & NODE_HT_MASK;
    for (;;) {
        if (!node_ht[h].filled) {
            node_ht[h].id     = id;
            node_ht[h].x      = x;
            node_ht[h].y      = y;
            node_ht[h].angle  = angle;
            node_ht[h].filled = 1;
            return &node_ht[h];
        }
        if (node_ht[h].id == id) return &node_ht[h];
        h = (h + 1) & NODE_HT_MASK;
    }
}

/* ─── Children adjacency (for BFS) — sorted by parent for binary search */
#define MAX_CHILDREN 800000
typedef struct { int64_t parent; int64_t child; } ChildPair;
static ChildPair children[MAX_CHILDREN];
static int       n_children = 0;

static int cmp_child_pair(const void *a, const void *b)
{
    int64_t da = ((const ChildPair *)a)->parent;
    int64_t db = ((const ChildPair *)b)->parent;
    return (da > db) - (da < db);
}

/* ─── BFS queue ───────────────────────────────────────────────────── */
#define QUEUE_CAP (1 << 20)
static int64_t bfs_queue[QUEUE_CAP];

/* ─── Colormap: dark purple → red → orange → gold ─────────────────── */
typedef struct { double r, g, b; } RGB;

static const RGB cmap[] = {
    {0.102, 0.039, 0.180},  /* #1a0a2e  very dark purple */
    {0.239, 0.110, 0.431},  /* #3d1c6e  dark purple      */
    {0.420, 0.184, 0.627},  /* #6b2fa0  purple            */
    {0.608, 0.137, 0.208},  /* #9b2335  dark red          */
    {0.769, 0.118, 0.227},  /* #c41e3a  red               */
    {0.910, 0.271, 0.110},  /* #e8451c  red-orange        */
    {0.957, 0.518, 0.176},  /* #f4842d  orange            */
    {0.961, 0.651, 0.137},  /* #f5a623  dark gold         */
    {0.988, 0.788, 0.388},  /* #fcc963  gold              */
    {0.992, 0.910, 0.690},  /* #fde8b0  light gold        */
};
#define CMAP_N 10

static RGB cmap_sample(double t)
{
    /* t in [0,1] */
    if (t <= 0.0) return cmap[0];
    if (t >= 1.0) return cmap[CMAP_N - 1];
    double f = t * (CMAP_N - 1);
    int    i = (int)f;
    double u = f - i;
    if (i >= CMAP_N - 1) return cmap[CMAP_N - 1];
    return (RGB){
        cmap[i].r + u * (cmap[i+1].r - cmap[i].r),
        cmap[i].g + u * (cmap[i+1].g - cmap[i].g),
        cmap[i].b + u * (cmap[i+1].b - cmap[i].b),
    };
}

/* ─── Collected edges for sorted rendering ────────────────────────── */
typedef struct {
    double x0, y0, x1, y1;
    double freq_log;
} DrawEdge;

static int cmp_draw_edge(const void *a, const void *b)
{
    double fa = ((const DrawEdge *)a)->freq_log;
    double fb = ((const DrawEdge *)b)->freq_log;
    return (fa > fb) - (fa < fb);
}

/* ─── Fisher-Yates partial shuffle for sampling without replacement ── */
static void sample_unique(int *out, int n, int max_val, unsigned seed)
{
    /* Fill [0..max_val-1], shuffle first n */
    int *pool = malloc(max_val * sizeof(int));
    for (int i = 0; i < max_val; i++) pool[i] = i + 1;

    srand(seed);
    for (int i = 0; i < n && i < max_val; i++) {
        int j    = i + rand() % (max_val - i);
        int tmp  = pool[i];
        pool[i]  = pool[j];
        pool[j]  = tmp;
        out[i]   = pool[i];
    }
    free(pool);
}

/* ================================================================== */
int main(int argc, char **argv)
{
    int N         = 5000;
    int MAX_START = 1000000;
    int SEED      = 42;

    if (argc > 1) N         = atoi(argv[1]);
    if (argc > 2) MAX_START = atoi(argv[2]);
    if (argc > 3) SEED      = atoi(argv[3]);

    printf("Collatz Tree: N=%d  MAX_START=%d  SEED=%d\n", N, MAX_START, SEED);
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    /* ── 1. Select starting points ─────────────────────────────────── */
    int *starts = malloc(N * sizeof(int));
    sample_unique(starts, N, MAX_START, SEED);

    /* Ensure 837799 is included */
    int found = 0;
    for (int i = 0; i < N; i++)
        if (starts[i] == 837799) { found = 1; break; }
    if (!found) starts[N - 1] = 837799;

    /* ── 2. Compute sequences & edge frequencies ───────────────────── */
    printf("  Computing sequences...\n");
    memset(edge_ht, 0, sizeof(edge_ht));

    int64_t longest_start = 0;
    int     longest_len   = 0;
    i64vec  seq;
    vec_init(&seq, 1024);

    for (int si = 0; si < N; si++) {
        int64_t n = starts[si];
        seq.len = 0;
        vec_push(&seq, n);

        int64_t cur = n;
        while (cur != 1) {
            cur = (cur & 1) ? 3 * cur + 1 : cur >> 1;
            vec_push(&seq, cur);
        }
        int path_len = seq.len - 1;
        if (path_len > longest_len) {
            longest_len   = path_len;
            longest_start = n;
        }

        /* Reversed edges: walk 1 → ... → n */
        for (int i = seq.len - 1; i > 0; i--) {
            int64_t parent = seq.d[i];
            int64_t child  = seq.d[i - 1];
            int is_new = edge_add(parent, child);
            if (is_new && n_children < MAX_CHILDREN) {
                children[n_children].parent = parent;
                children[n_children].child  = child;
                n_children++;
            }
        }
    }
    vec_free(&seq);
    printf("  Longest path: %lld (%d steps)\n",
           (long long)longest_start, longest_len);
    printf("  Unique edges: %d\n", edge_ht_used);

    /* ── 3. BFS from root to assign positions ──────────────────────── */
    printf("  Positioning nodes...\n");
    memset(node_ht, 0, sizeof(node_ht));

    double angle_even = ANGLE_EVEN_DEG * M_PI / 180.0;
    double angle_odd  = ANGLE_ODD_DEG  * M_PI / 180.0;

    /* Sort children by parent for fast lookup */
    qsort(children, n_children, sizeof(ChildPair), cmp_child_pair);

    node_insert(1, 0.0, 0.0, M_PI / 2.0);

    int qhead = 0, qtail = 0;
    bfs_queue[qtail++] = 1;

    while (qhead < qtail) {
        int64_t nd = bfs_queue[qhead++];
        NodeEntry *pn = node_find(nd);
        if (!pn) continue;

        double px = pn->x, py = pn->y, heading = pn->angle;

        /* Binary search for first child of nd in sorted children[] */
        int lo = 0, hi = n_children;
        while (lo < hi) {
            int mid = (lo + hi) / 2;
            if (children[mid].parent < nd) lo = mid + 1;
            else hi = mid;
        }
        /* Iterate all children of nd */
        for (int ci = lo; ci < n_children && children[ci].parent == nd; ci++) {
            int64_t ch = children[ci].child;
            if (node_find(ch)) continue;  /* already placed */

            double new_heading;
            if (ch % 2 == 0)
                new_heading = heading + angle_even;
            else
                new_heading = heading - angle_odd;

            double edge_len = EDGE_SCALE_K / log10((double)ch + 1.0);
            double cx = px + edge_len * cos(new_heading);
            double cy = py + edge_len * sin(new_heading);

            node_insert(ch, cx, cy, new_heading);
            if (qtail < QUEUE_CAP)
                bfs_queue[qtail++] = ch;
        }
    }
    int n_nodes = qtail;
    printf("  Positioned %d nodes\n", n_nodes);

    /* ── 3b. (adjacency already optimised via sorted array + bsearch) */

    /* ── 4. Rotate all coordinates ────────────────────────────────── */
    double rot = ROTATION_DEG * M_PI / 180.0;
    double cr = cos(rot), sr = sin(rot);

    for (int i = 0; i < NODE_HT_CAP; i++) {
        if (!node_ht[i].filled) continue;
        double x = node_ht[i].x, y = node_ht[i].y;
        node_ht[i].x = x * cr - y * sr;
        node_ht[i].y = x * sr + y * cr;
    }

    /* ── 5. Collect drawable edges ────────────────────────────────── */
    printf("  Collecting drawable edges...\n");
    DrawEdge *draw = malloc(edge_ht_used * sizeof(DrawEdge));
    int n_draw = 0;
    double max_freq_log = 0;

    for (int i = 0; i < EDGE_HT_CAP; i++) {
        if (edge_ht[i].freq == 0) continue;
        NodeEntry *np = node_find(edge_ht[i].parent);
        NodeEntry *nc = node_find(edge_ht[i].child);
        if (!np || !nc) continue;

        double fl = log10((double)edge_ht[i].freq + 1.0);
        if (fl > max_freq_log) max_freq_log = fl;

        draw[n_draw].x0 = np->x;
        draw[n_draw].y0 = np->y;
        draw[n_draw].x1 = nc->x;
        draw[n_draw].y1 = nc->y;
        draw[n_draw].freq_log = fl;
        n_draw++;
    }
    printf("  %d drawable edges, max_freq_log=%.3f\n", n_draw, max_freq_log);

    /* Sort: low frequency first (drawn first, high freq on top) */
    qsort(draw, n_draw, sizeof(DrawEdge), cmp_draw_edge);

    /* ── 6. Compute bounding box & mapping ────────────────────────── */
    double xmin = 1e18, xmax = -1e18, ymin = 1e18, ymax = -1e18;
    for (int i = 0; i < NODE_HT_CAP; i++) {
        if (!node_ht[i].filled) continue;
        if (node_ht[i].x < xmin) xmin = node_ht[i].x;
        if (node_ht[i].x > xmax) xmax = node_ht[i].x;
        if (node_ht[i].y < ymin) ymin = node_ht[i].y;
        if (node_ht[i].y > ymax) ymax = node_ht[i].y;
    }
    double xrange = xmax - xmin, yrange = ymax - ymin;
    double pad = 0.04;
    xmin -= xrange * pad; xmax += xrange * pad;
    ymin -= yrange * pad; ymax += yrange * pad;
    xrange = xmax - xmin; yrange = ymax - ymin;

    /* Fit into image maintaining aspect ratio */
    double scale_x = (IMG_W - 40) / xrange;
    double scale_y = (IMG_H - 40) / yrange;
    double scale   = (scale_x < scale_y) ? scale_x : scale_y;

    double off_x = 20 + ((IMG_W - 40) - xrange * scale) / 2.0;
    double off_y = 20 + ((IMG_H - 40) - yrange * scale) / 2.0;

    #define MAP_X(wx) (off_x + ((wx) - xmin) * scale)
    #define MAP_Y(wy) (off_y + (ymax - (wy)) * scale)  /* flip Y */

    /* ── 7. Render with Cairo ─────────────────────────────────────── */
    printf("  Rendering %dx%d...\n", IMG_W, IMG_H);
    cairo_surface_t *surface = cairo_image_surface_create(
        CAIRO_FORMAT_ARGB32, IMG_W, IMG_H);
    cairo_t *cr2 = cairo_create(surface);

    /* Background */
    cairo_set_source_rgb(cr2, BG_R, BG_G, BG_B);
    cairo_paint(cr2);

    cairo_set_line_cap(cr2, CAIRO_LINE_CAP_ROUND);
    cairo_set_line_join(cr2, CAIRO_LINE_JOIN_ROUND);
    cairo_set_antialias(cr2, CAIRO_ANTIALIAS_BEST);

    /* Draw edges */
    for (int i = 0; i < n_draw; i++) {
        double t = (max_freq_log > 0)
                 ? draw[i].freq_log / max_freq_log : 0;
        double lw = THICKNESS_MIN + (THICKNESS_MAX - THICKNESS_MIN) * t;
        RGB col = cmap_sample(t);

        cairo_set_line_width(cr2, lw);
        cairo_set_source_rgba(cr2, col.r, col.g, col.b, 0.85);
        cairo_move_to(cr2, MAP_X(draw[i].x0), MAP_Y(draw[i].y0));
        cairo_line_to(cr2, MAP_X(draw[i].x1), MAP_Y(draw[i].y1));
        cairo_stroke(cr2);
    }

    /* ── 8. Highlight longest path ────────────────────────────────── */
    {
        i64vec hl;
        vec_init(&hl, 1024);
        int64_t cur = longest_start;
        vec_push(&hl, cur);
        while (cur != 1) {
            cur = (cur & 1) ? 3 * cur + 1 : cur >> 1;
            vec_push(&hl, cur);
        }
        /* Draw reversed (1 → ... → longest_start) */
        cairo_set_line_width(cr2, 1.2);
        cairo_set_source_rgba(cr2, 0.769, 0.118, 0.227, 0.55);
        for (int i = hl.len - 1; i > 0; i--) {
            NodeEntry *na = node_find(hl.d[i]);
            NodeEntry *nb = node_find(hl.d[i - 1]);
            if (na && nb) {
                cairo_move_to(cr2, MAP_X(na->x), MAP_Y(na->y));
                cairo_line_to(cr2, MAP_X(nb->x), MAP_Y(nb->y));
                cairo_stroke(cr2);
            }
        }
        vec_free(&hl);
    }

    /* ── 9. Annotations ───────────────────────────────────────────── */
    cairo_select_font_face(cr2, "serif",
        CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_BOLD);

    /* Key node labels */
    int64_t labels[] = {1, 2, 4, 16, 40, 22, 130, 94};
    int n_labels = sizeof(labels) / sizeof(labels[0]);
    cairo_set_font_size(cr2, 16);
    cairo_set_source_rgb(cr2, 0.176, 0.106, 0.306);
    for (int i = 0; i < n_labels; i++) {
        NodeEntry *ne = node_find(labels[i]);
        if (!ne) continue;
        char buf[32];
        snprintf(buf, sizeof(buf), "%lld", (long long)labels[i]);
        cairo_move_to(cr2, MAP_X(ne->x) + 4, MAP_Y(ne->y) - 4);
        cairo_show_text(cr2, buf);
    }

    /* Title */
    cairo_select_font_face(cr2, "serif",
        CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_BOLD);
    cairo_set_font_size(cr2, 48);
    cairo_set_source_rgb(cr2, 0.102, 0.039, 0.180);

    /* Place title in lower-center region */
    double tx = MAP_X(xmin + xrange * 0.32);
    double ty = MAP_Y(ymin + yrange * 0.10);
    cairo_move_to(cr2, tx, ty);
    cairo_show_text(cr2, "Collatz conjecture paths");

    cairo_set_font_size(cr2, 22);
    cairo_set_source_rgb(cr2, 0.239, 0.110, 0.431);
    cairo_move_to(cr2, tx, ty + 32);
    {
        char sub[128];
        snprintf(sub, sizeof(sub),
                 "for %d random starting points below %d", N, MAX_START);
        cairo_show_text(cr2, sub);
    }

    /* Description */
    cairo_select_font_face(cr2, "serif",
        CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_NORMAL);
    cairo_set_font_size(cr2, 15);
    cairo_set_source_rgb(cr2, 0.353, 0.239, 0.478);
    const char *desc[] = {
        "Starting from the tree root, the path turns left by 8.65\xc2\xb0 to even nodes",
        "and right by 16\xc2\xb0 to odd nodes. The length of each edge scales as 1 over",
        "the logarithm of its node further from the root. The color and the thickness",
        "depend linearly on the log\xe2\x82\x81\xe2\x82\x80 of how often the edge was traversed.",
        NULL
    };
    for (int i = 0; desc[i]; i++) {
        cairo_move_to(cr2, tx, ty + 60 + i * 20);
        cairo_show_text(cr2, desc[i]);
    }

    /* Longest path label */
    {
        NodeEntry *ne = node_find(longest_start);
        if (ne) {
            cairo_set_source_rgb(cr2, 0.831, 0.627, 0.090);
            cairo_set_font_size(cr2, 16);
            char buf[128];
            snprintf(buf, sizeof(buf), "%lld", (long long)longest_start);
            double lx = MAP_X(ne->x), ly = MAP_Y(ne->y);
            cairo_move_to(cr2, lx + 8, ly);
            cairo_show_text(cr2, buf);
            cairo_move_to(cr2, lx + 8, ly + 18);
            cairo_show_text(cr2, "The longest path");
            snprintf(buf, sizeof(buf), "below %d", MAX_START);
            cairo_move_to(cr2, lx + 8, ly + 36);
            cairo_show_text(cr2, buf);
        }
    }

    /* 2^19 label */
    {
        int64_t v = 524288;  /* 2^19 */
        NodeEntry *ne = node_find(v);
        if (ne) {
            cairo_set_source_rgb(cr2, 0.831, 0.627, 0.090);
            cairo_set_font_size(cr2, 14);
            cairo_move_to(cr2, MAP_X(ne->x) - 100, MAP_Y(ne->y) - 4);
            cairo_show_text(cr2, "2\xc2\xb9\xe2\x81\xb9 = 524,288");
        }
    }

    /* ── 10. Write PNG ────────────────────────────────────────────── */
    const char *outpath = "collatz_tree.png";
    cairo_status_t status = cairo_surface_write_to_png(surface, outpath);
    cairo_destroy(cr2);
    cairo_surface_destroy(surface);
    free(draw);
    free(starts);

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;

    if (status == CAIRO_STATUS_SUCCESS)
        printf("  Saved: %s (%.2fs total)\n", outpath, elapsed);
    else
        fprintf(stderr, "Error writing PNG: %s\n",
                cairo_status_to_string(status));

    return 0;
}
