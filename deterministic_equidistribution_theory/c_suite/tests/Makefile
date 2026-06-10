# tests/Makefile — unit checks. Invoked by `make test` from project root.
CC     ?= cc
CFLAGS := -std=c11 -Wall -Wextra -O2 -D_POSIX_C_SOURCE=200809L -I../include
LDLIBS := -lm

CORE := ../src/modarith.c ../src/orbit_scan.c ../src/bigval.c ../src/sparse_matrix.c

.PHONY: run
run: test_runner
	./test_runner

test_runner: test_runner.c $(CORE)
	$(CC) $(CFLAGS) -o $@ $^ $(LDLIBS)
