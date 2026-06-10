/* io_csv.h — streaming CSV writers with reproducibility metadata headers.
 * Spec Section "Data Formats": every output file starts with commented
 * provenance lines (git commit, compiler, build profile, command, timestamp).
 */
#ifndef AIPM_IO_CSV_H
#define AIPM_IO_CSV_H

#include <stdio.h>

#define BUILD_PROFILE_STR (USE_GMP_PROFILE ? "GMP" : "FAST128")
#ifdef USE_GMP
#  define USE_GMP_PROFILE 1
#else
#  define USE_GMP_PROFILE 0
#endif

/* Open `path`, write the metadata header block, return the stream.
 * `experiment` is the experiment tag (e.g. "congruence_checks").
 * `header` is the CSV column line (without trailing newline). */
FILE *csv_open(const char *path, const char *experiment,
               const char *header, int argc, char **argv);

#endif /* AIPM_IO_CSV_H */
