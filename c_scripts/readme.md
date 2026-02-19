C scripts for visualizing the Collatz conjecture. Both use cairo for anti-aliased rendering with the same visual encoding. The sole dependency is libcairo2-dev. Build with make all, run with make run-tree / make run-scatter, or pass custom parameters directly:


./collatz_tree  [N] [MAX_START] [SEED]
./collatz_scatter [MAX_N] [STEP]


For the Collatz Tree Animation:

gcc -O3 -march=native -o collatz_tree_anim collatz_tree_anim.c \
    $(pkg-config --cflags --libs cairo) -lm

# 100K starts, 2K per frame → 50 frames, ~30s
./collatz_tree_anim 100000 10000000 42 2000 frames

# Big run: 1M starts, 10K per frame → 100 frames
./collatz_tree_anim 1000000 100000000 42 10000 frames

# 4K resolution (recompile):
gcc -O3 -DIMG_W=3840 -DIMG_H=2160 ...

# Then ffmpeg:
ffmpeg -framerate 30 -i frames/frame_%06d.png \
       -c:v libx264 -pix_fmt yuv420p -crf 18 collatz_tree.mp4
