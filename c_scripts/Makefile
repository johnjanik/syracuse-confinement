CC      = gcc
CFLAGS  = -O3 -march=native -Wall
CAIRO   = $(shell pkg-config --cflags --libs cairo)
LIBS    = -lm

all: collatz_tree collatz_scatter parity_sft profinite_compat branch_locus v2_danger deficit_analysis

collatz_tree: collatz_tree.c
	$(CC) $(CFLAGS) -o $@ $< $(CAIRO) $(LIBS)

collatz_scatter: collatz_scatter.c
	$(CC) $(CFLAGS) -o $@ $< $(CAIRO) $(LIBS)

parity_sft: parity_sft.c
	$(CC) $(CFLAGS) -o $@ $< $(LIBS)

profinite_compat: profinite_compat.c
	$(CC) $(CFLAGS) -o $@ $< $(LIBS)

branch_locus: branch_locus.c
	$(CC) $(CFLAGS) -fopenmp -o $@ $< $(LIBS)

run-sft: parity_sft
	./parity_sft 1000000

run-profinite: profinite_compat
	./profinite_compat 10000000

run-tree: collatz_tree
	./collatz_tree 5000 1000000 42

run-scatter: collatz_scatter
	./collatz_scatter 100000000 1

run-branch: branch_locus
	./branch_locus 10000000

run-branch-10B: branch_locus
	./branch_locus 10000000000

run-branch-100B: branch_locus
	./branch_locus 100000000000

resume-branch-100B: branch_locus
	./branch_locus --resume 100000000000

v2_danger: v2_danger.c
	$(CC) $(CFLAGS) -fopenmp -o $@ $< $(LIBS)

deficit_analysis: deficit_analysis.c
	$(CC) $(CFLAGS) -fopenmp -o $@ $< $(LIBS)

run-deficit-1B: deficit_analysis
	./deficit_analysis 1000000000

run-deficit-10B: deficit_analysis
	./deficit_analysis 10000000000

gpu_branch: gpu_branch_host.c gpu_branch_kernel.cl
	$(CC) $(CFLAGS) -o $@ gpu_branch_host.c -lOpenCL $(LIBS)

run-gpu-compare: gpu_branch
	./gpu_branch --compare 1000000

run-gpu-branch: gpu_branch
	./gpu_branch --branch 100000000

run-gpu-fast: gpu_branch
	./gpu_branch --fast 1000000000

run-gpu-verify: gpu_branch
	./gpu_branch --verify 1000000000

run-v2danger: v2_danger
	./v2_danger --N 100000 --k 5

run-v2danger-1M: v2_danger
	./v2_danger --N 1000000 --k 7

run-v2danger-10M: v2_danger
	./v2_danger --N 10000000 --k 7

clean:
	rm -f collatz_tree collatz_scatter parity_sft profinite_compat branch_locus v2_danger deficit_analysis *.png *.csv

.PHONY: all clean run-tree run-scatter run-sft run-profinite run-branch run-branch-10B run-branch-100B resume-branch-100B run-v2danger run-v2danger-1M run-v2danger-10M run-gpu-compare run-gpu-branch run-gpu-fast run-gpu-verify run-deficit-1B run-deficit-10B
