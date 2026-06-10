/* main.c — collatz_tests: subcommand dispatch.
 * Spec Section "Command-Line Interface". */
#include "experiments.h"
#include "io_csv.h"
#include <stdio.h>
#include <string.h>

static void usage(const char *prog) {
    fprintf(stderr,
        "collatz_tests — numerical suite for the Collatz deterministic defect cocycle\n"
        "build profile: %s\n\n"
        "usage: %s <subcommand> [options]\n\n"
        "subcommands:\n"
        "  congruence-check   Experiment H: verify the mod 3^r sliding-window identity (GATE)\n"
        "  scan-height        Experiment A: height-tail & critical-event census\n"
        "  tilt-law           Experiment B: empirical Cramer-tilt law on critical excursions\n"
        "  defect-windows     Experiment C: windowed defect sums W_{n,l}(x;chi,s)\n"
        "  post-exit          Experiment D: post-exit taboo / entropy-space repulsion\n"
        "  spectral-gaps      Experiment E: rho(L_{s,Q,L,chi}) and sector gaps\n"
        "  fourier-compare    Experiment F: exact gap vs annealed Fourier prediction\n"
        "  trace-det          Experiment G: finite trace/determinant shadows\n"
        "  shadow-search      Experiment I: quenched spectral-shadow search\n\n"
        "common options: --seed N --start N --end N --max-steps N --output-dir DIR\n"
        "                --windows L,.. --moduli Q,.. --tilts s,.. --apertures A,..\n"
        "                --r-max R --n-samples N --L N --R N --bmax N --delta D\n",
        BUILD_PROFILE_STR, prog);
}

int main(int argc, char **argv) {
    if (argc < 2) { usage(argv[0]); return 1; }
    const char *cmd = argv[1];

    config_t c; config_defaults(&c);
    if (config_parse(&c, argc, argv, 2) != 0) return 1;

    if      (!strcmp(cmd, "congruence-check")) return exp_congruence(&c, argc, argv);
    else if (!strcmp(cmd, "scan-height"))      return exp_scan_height(&c, argc, argv);
    else if (!strcmp(cmd, "tilt-law"))         return exp_tilt_law(&c, argc, argv);
    else if (!strcmp(cmd, "defect-windows"))   return exp_defect_windows(&c, argc, argv);
    else if (!strcmp(cmd, "post-exit"))        return exp_post_exit(&c, argc, argv);
    else if (!strcmp(cmd, "spectral-gaps"))    return exp_spectral_gaps(&c, argc, argv);
    else if (!strcmp(cmd, "fourier-compare"))  return exp_fourier_compare(&c, argc, argv);
    else if (!strcmp(cmd, "trace-det"))        return exp_trace_det(&c, argc, argv);
    else if (!strcmp(cmd, "shadow-search"))    return exp_shadow_search(&c, argc, argv);
    else if (!strcmp(cmd, "-h") || !strcmp(cmd, "--help")) { usage(argv[0]); return 0; }

    fprintf(stderr, "unknown subcommand: %s\n\n", cmd);
    usage(argv[0]);
    return 1;
}
