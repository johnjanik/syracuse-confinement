#include "io_csv.h"
#include <time.h>
#include <string.h>

static void git_commit(char *buf, size_t n) {
    buf[0] = '\0';
    FILE *p = popen("git rev-parse --short HEAD 2>/dev/null", "r");
    if (!p) { strncpy(buf, "unknown", n); return; }
    if (fgets(buf, (int)n, p)) {
        size_t L = strlen(buf);
        if (L && buf[L-1] == '\n') buf[L-1] = '\0';
    }
    if (buf[0] == '\0') strncpy(buf, "unknown", n);
    pclose(p);
}

FILE *csv_open(const char *path, const char *experiment,
               const char *header, int argc, char **argv) {
    FILE *f = fopen(path, "w");
    if (!f) return NULL;

    char commit[64]; git_commit(commit, sizeof commit);

    char ts[32]; time_t t = time(NULL);
    struct tm tmv; gmtime_r(&t, &tmv);
    strftime(ts, sizeof ts, "%Y-%m-%dT%H:%M:%SZ", &tmv);

    fprintf(f, "# experiment=%s\n", experiment);
    fprintf(f, "# git_commit=%s\n", commit);
    fprintf(f, "# compiler=%s\n", __VERSION__);
    fprintf(f, "# build_profile=%s\n", BUILD_PROFILE_STR);
    fprintf(f, "# command=");
    for (int i = 0; i < argc; i++) fprintf(f, "%s%s", argv[i], i+1 < argc ? " " : "");
    fprintf(f, "\n");
    fprintf(f, "# timestamp_utc=%s\n", ts);
    fprintf(f, "%s\n", header);
    return f;
}
