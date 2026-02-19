#!/usr/bin/env python3
"""
Collatz Conjecture – Total Stopping Time Scatter Plot
======================================================
Plots the number of iterations to reach 1 for each starting integer n.
Style: red diamond markers on black background, matching reference image.
Uses memoized computation for efficiency.
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import Normalize
import time

# ─── Parameters ───────────────────────────────────────────────────────
MAX_N = 100_000_000    # upper limit
STEP  = 1             # compute every STEP-th number (1 = all)

FIG_WIDTH  = 20
FIG_HEIGHT = 14
DPI        = 200

BG_COLOR   = '#FFFFFF' #'#000000'
DOT_COLOR  = '#000000' #'#FF1A1A'
DOT_SIZE   = 0.08      # marker size
DOT_ALPHA  = 0.35

# ─── Compute stopping times with memoization ─────────────────────────
print(f"Computing stopping times for n = 1 to {MAX_N:,} (step={STEP})...")
t0 = time.time()

# Pre-allocate cache array (0 = not computed, except index 1)
cache_size = MAX_N * 4  # sequences can overshoot MAX_N
cache = np.zeros(cache_size + 1, dtype=np.int32)
cache[1] = 0  # 1 → 0 steps

def stopping_time(n):
    """Compute total stopping time with memoization."""
    if n < len(cache) and cache[n] > 0:
        return cache[n]
    if n == 1:
        return 0
    
    # Walk the sequence, collecting uncached values
    path = []
    curr = n
    while curr != 1:
        if curr < len(cache) and cache[curr] > 0:
            # Found cached value; backfill
            steps = cache[curr]
            for i, val in enumerate(reversed(path)):
                steps += 1
                if val < len(cache):
                    cache[val] = steps
            return steps + len(path) - len(path)  # already counted
        path.append(curr)
        if curr % 2 == 0:
            curr = curr // 2
        else:
            curr = 3 * curr + 1
    
    # curr == 1; backfill from end
    steps = 0
    for val in reversed(path):
        steps += 1
        if val < len(cache):
            cache[val] = steps
    return steps

# Vectorized approach: compute all stopping times
ns = np.arange(1, MAX_N + 1, STEP, dtype=np.int64)
stopping_times = np.zeros(len(ns), dtype=np.int32)

# Efficient iterative computation with dict cache for overflow values
cache_dict = {1: 0}

for idx in range(len(ns)):
    n = int(ns[idx])
    if n in cache_dict:
        stopping_times[idx] = cache_dict[n]
        continue
    
    path = []
    curr = n
    while curr not in cache_dict:
        path.append(curr)
        if curr % 2 == 0:
            curr = curr >> 1  # faster division by 2
        else:
            curr = 3 * curr + 1
    
    # Backfill
    steps = cache_dict[curr]
    for val in reversed(path):
        steps += 1
        cache_dict[val] = steps
    
    stopping_times[idx] = cache_dict[n]
    
    if idx % 2_000_000 == 0 and idx > 0:
        elapsed = time.time() - t0
        print(f"  {idx:,}/{len(ns):,} computed ({elapsed:.1f}s)")

elapsed = time.time() - t0
print(f"  Done in {elapsed:.1f}s. Max stopping time: {stopping_times.max()} "
      f"at n={ns[np.argmax(stopping_times)]:,}")

# ─── Render scatter plot ──────────────────────────────────────────────
print("Rendering scatter plot...")

fig, ax = plt.subplots(1, 1, figsize=(FIG_WIDTH, FIG_HEIGHT), dpi=DPI)
fig.patch.set_facecolor(BG_COLOR)
ax.set_facecolor(BG_COLOR)

# Plot as tiny diamond markers
ax.scatter(ns, stopping_times,
           s=DOT_SIZE, c=DOT_COLOR, marker='d',
           alpha=DOT_ALPHA, edgecolors='none',
           rasterized=True)

# Axes styling
ax.set_xlabel('Starting number n', color='#CCCCCC', fontsize=13, fontfamily='serif')
ax.set_ylabel('Total stopping time (steps to reach 1)', color='#CCCCCC', fontsize=13, fontfamily='serif')
ax.set_title(f'Collatz Total Stopping Times for n = 1 to {MAX_N:,}',
             color='#FFFFFF', fontsize=18, fontweight='bold', fontfamily='serif',
             pad=15)

ax.tick_params(colors='#999999', which='both')
ax.spines['bottom'].set_color('#444444')
ax.spines['left'].set_color('#444444')
ax.spines['top'].set_visible(False)
ax.spines['right'].set_visible(False)

# Grid
ax.grid(True, alpha=0.15, color='#666666', linewidth=0.5)

# Highlight record holders
records = [
    (837799, "837,799 (524 steps)"),
    (8400511, "8,400,511 (685 steps)"),
]
for val, label in records:
    if val <= MAX_N:
        idx_rec = val // STEP - (1 if STEP == 1 else 0)
        if 0 <= idx_rec < len(ns) and ns[idx_rec] == val:
            st = stopping_times[idx_rec]
        else:
            st = cache_dict.get(val, None)
        if st is not None:
            ax.annotate(label, (val, st),
                        fontsize=9, color='#FFD700',
                        fontweight='bold', fontfamily='serif',
                        ha='left', va='bottom',
                        xytext=(10, 10), textcoords='offset points',
                        arrowprops=dict(arrowstyle='->', color='#FFD700',
                                        lw=0.8))

ax.set_xlim(0, MAX_N * 1.02)
ax.set_ylim(0, stopping_times.max() * 1.08)

plt.tight_layout(pad=1.0)
outpath = '/home/john/Projects/collatz/collatz_scatter.png'
fig.savefig(outpath, dpi=DPI, facecolor=BG_COLOR,
            bbox_inches='tight', pad_inches=0.3)
plt.close()
print(f"Saved: {outpath}")
