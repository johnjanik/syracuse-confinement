#!/usr/bin/env python3
"""
Collatz Conjecture Tree Visualization
======================================
Draws paths for N random starting numbers from root (1) outward,
replicating the style of the classic Collatz tree visualization.

Turning rules:
  - Even child: turn LEFT by 8.65°
  - Odd child:  turn RIGHT by 16°

Edge length scales as k / log10(child_value + 1).
Color and thickness encode log10(traversal_count).
"""

import random
import math
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.collections as mc
from matplotlib.colors import Normalize
from collections import defaultdict

# ─── Parameters ───────────────────────────────────────────────────────
N = 50000              # number of random starting points
MAX_START = 10_000_000 # upper bound for starting numbers
SEED = 42             # reproducibility

ANGLE_EVEN = 8.65     # degrees, turn LEFT for even child
ANGLE_ODD  = 16.0     # degrees, turn RIGHT for odd child

EDGE_SCALE_K   = 12.0    # global scaling constant for edge length
THICKNESS_MIN  = 0.05
THICKNESS_MAX  = 3.5

FIG_WIDTH  = 32       # inches
FIG_HEIGHT = 18

BG_COLOR = '#FAF8F5'  # warm off-white

# ─── Step 1: Generate Collatz sequences ───────────────────────────────
print("Generating Collatz sequences...")
random.seed(SEED)
starts = random.sample(range(2, MAX_START + 1), N)

# Always include the record holder
if 837799 not in starts:
    starts[-1] = 837799

# Compute all forward sequences (n → 1) with memoization
seq_cache = {}

def collatz_sequence(n):
    """Return the full Collatz sequence from n down to 1."""
    if n in seq_cache:
        return seq_cache[n]
    seq = [n]
    curr = n
    visited = []
    while curr != 1:
        visited.append(curr)
        if curr % 2 == 0:
            curr = curr // 2
        else:
            curr = 3 * curr + 1
        seq.append(curr)
        if curr in seq_cache:
            seq.extend(seq_cache[curr][1:])
            break
    # Cache subsequences
    for i, v in enumerate(visited):
        if v not in seq_cache:
            seq_cache[v] = seq[i:]
    if n not in seq_cache:
        seq_cache[n] = seq
    return seq_cache[n]

# Compute all sequences and collect edge frequencies
edge_freq = defaultdict(int)  # (parent, child) → count, in REVERSED direction
all_reversed_paths = []

longest_path_len = 0
longest_path_start = 0

for s in starts:
    fwd = collatz_sequence(s)
    path_len = len(fwd) - 1
    if path_len > longest_path_len:
        longest_path_len = path_len
        longest_path_start = s
    
    # Reverse: 1 → 2 → 4 → ... → s
    rev = list(reversed(fwd))
    all_reversed_paths.append(rev)
    
    for i in range(len(rev) - 1):
        parent = rev[i]
        child = rev[i + 1]
        edge_freq[(parent, child)] += 1

print(f"  Sequences computed. Longest path: {longest_path_start} ({longest_path_len} steps)")
print(f"  Total unique edges: {len(edge_freq)}")

# ─── Step 2: Assign positions via tree traversal ──────────────────────
print("Computing node positions...")

# For each edge, we need to know the direction (angle) at which to draw it.
# We walk each reversed path from root, accumulating angle.
# Since many paths share prefixes, we can cache the angle at each node.
# But the angle at a node depends on the PATH taken to reach it, which is
# unique (each number has exactly one Collatz predecessor path to 1).
# Actually in the forward direction each number has a unique path to 1,
# so in the reversed tree each node has a unique path FROM 1.

# We'll compute positions by walking the unique edges in the tree.
# The reversed Collatz tree is: from node n, children are:
#   - 2*n (always, this is even)
#   - (n-1)/3 if (n-1) % 3 == 0 and (n-1)/3 is odd and (n-1)/3 >= 2

# But we only need edges that actually appear in our sampled paths.
# Let's build a tree structure from the edges.

# For each node, store its parent (in the reversed tree = toward root 1)
node_parent = {}  # child → parent
for (parent, child), freq in edge_freq.items():
    if child not in node_parent:
        node_parent[child] = parent

# Now compute positions. Start at root = 1.
# Each node stores (x, y, angle) where angle is the current heading.
node_pos = {}    # node → (x, y)
node_angle = {}  # node → heading angle in radians

# Root position
node_pos[1] = (0.0, 0.0)
node_angle[1] = math.pi / 2  # start pointing UP; rotation applied later

# We need to traverse the tree in BFS order from root
from collections import deque

# Build adjacency: parent → list of children
children_map = defaultdict(set)
for (parent, child) in edge_freq:
    children_map[parent].add(child)

# BFS from root
queue = deque([1])
visited_nodes = {1}

while queue:
    node = queue.popleft()
    px, py = node_pos[node]
    heading = node_angle[node]
    
    for child in children_map[node]:
        if child in visited_nodes:
            continue
        visited_nodes.add(child)
        
        # Determine turn direction based on child parity
        if child % 2 == 0:
            # Even: turn LEFT
            new_heading = heading + math.radians(ANGLE_EVEN)
        else:
            # Odd: turn RIGHT
            new_heading = heading - math.radians(ANGLE_ODD)
        
        # Edge length: scales inversely with log10(child + 1)
        edge_len = EDGE_SCALE_K / math.log10(child + 1)
        
        cx = px + edge_len * math.cos(new_heading)
        cy = py + edge_len * math.sin(new_heading)
        
        node_pos[child] = (cx, cy)
        node_angle[child] = new_heading
        
        queue.append(child)

print(f"  Positioned {len(node_pos)} nodes")

# ─── Step 2b: Rotate entire tree for landscape orientation ────────────
# Reference image has root at bottom-left, tree sweeps right and up
ROTATION_DEG = -50  # rotate clockwise to get landscape sweep
rot_rad = math.radians(ROTATION_DEG)
cos_r, sin_r = math.cos(rot_rad), math.sin(rot_rad)

for node in node_pos:
    x, y = node_pos[node]
    node_pos[node] = (x * cos_r - y * sin_r, x * sin_r + y * cos_r)

# ─── Step 3: Build line segments with visual properties ───────────────
print("Building line segments...")

# Compute log frequencies
max_freq_log = 0
edge_data = []  # list of ((x0,y0,x1,y1), freq_log)

for (parent, child), freq in edge_freq.items():
    if parent not in node_pos or child not in node_pos:
        continue
    freq_log = math.log10(freq + 1)
    if freq_log > max_freq_log:
        max_freq_log = freq_log
    x0, y0 = node_pos[parent]
    x1, y1 = node_pos[child]
    edge_data.append(((x0, y0, x1, y1), freq_log))

print(f"  {len(edge_data)} drawable edges, max_freq_log = {max_freq_log:.3f}")

# Sort by frequency: draw low-frequency edges first (so high-freq on top)
edge_data.sort(key=lambda e: e[1])

# ─── Step 4: Render ──────────────────────────────────────────────────
print("Rendering...")

fig, ax = plt.subplots(1, 1, figsize=(FIG_WIDTH, FIG_HEIGHT), dpi=150)
fig.patch.set_facecolor(BG_COLOR)
ax.set_facecolor(BG_COLOR)
ax.set_aspect('equal')
ax.axis('off')

# Colormap: dark purple → red → orange → light gold (matching reference image)
from matplotlib.colors import LinearSegmentedColormap
colors_list = [
    '#1a0a2e',  # very dark purple
    '#3d1c6e',  # dark purple  
    '#6b2fa0',  # purple
    '#9b2335',  # dark red
    '#c41e3a',  # red
    '#e8451c',  # red-orange
    '#f4842d',  # orange
    '#f5a623',  # dark gold
    '#fcc963',  # gold
    '#fde8b0',  # light gold
]
cmap = LinearSegmentedColormap.from_list('collatz', colors_list, N=256)

norm = Normalize(vmin=0, vmax=max_freq_log)

# Draw edges as line segments
# Batch by approximate thickness for efficiency
BATCH_SIZE = 500
batch_lines = []
batch_colors = []
batch_lw = []

for i, (coords, freq_log) in enumerate(edge_data):
    x0, y0, x1, y1 = coords
    t = freq_log / max_freq_log if max_freq_log > 0 else 0
    lw = THICKNESS_MIN + (THICKNESS_MAX - THICKNESS_MIN) * t
    color = cmap(norm(freq_log))
    
    ax.plot([x0, x1], [y0, y1],
            color=color, linewidth=lw,
            solid_capstyle='round', alpha=0.85)

# ─── Highlight the longest path (837,799) ─────────────────────────────
print("Highlighting longest path...")
highlight_seq = collatz_sequence(longest_path_start)
highlight_rev = list(reversed(highlight_seq))

for i in range(len(highlight_rev) - 1):
    p = highlight_rev[i]
    c = highlight_rev[i + 1]
    if p in node_pos and c in node_pos:
        x0, y0 = node_pos[p]
        x1, y1 = node_pos[c]
        ax.plot([x0, x1], [y0, y1],
                color='#c41e3a', linewidth=1.0,
                solid_capstyle='round', alpha=0.6)

# ─── Annotations ──────────────────────────────────────────────────────
# Label key nodes
key_labels = {1: '1', 2: '2', 4: '4', 8: '8', 16: '16', 40: '40', 
              22: '22', 130: '130', 94: '94'}

for node, label in key_labels.items():
    if node in node_pos:
        x, y = node_pos[node]
        ax.annotate(label, (x, y), fontsize=8, fontweight='bold',
                    color='#2d1b4e', ha='center', va='bottom',
                    xytext=(0, 3), textcoords='offset points')

# Title and description
# Find bounding box for placement
all_x = [pos[0] for pos in node_pos.values()]
all_y = [pos[1] for pos in node_pos.values()]
x_min, x_max = min(all_x), max(all_x)
y_min, y_max = min(all_y), max(all_y)

# Place title in lower-center area
title_x = x_min + (x_max - x_min) * 0.35
title_y = y_min + (y_max - y_min) * 0.08

ax.text(title_x, title_y, 'Collatz conjecture paths',
        fontsize=28, fontweight='bold', color='#1a0a2e',
        fontfamily='serif', ha='left', va='bottom')

ax.text(title_x, title_y - (y_max - y_min) * 0.03,
        f'for {N} random starting points below {MAX_START:,}',
        fontsize=14, color='#3d1c6e',
        fontfamily='serif', ha='left', va='top')

desc_text = (
    "Starting from the tree root, the path turns left by 8.65° to even nodes\n"
    "and right by 16° to odd nodes. The length of each edge scales as 1 over\n"
    "the logarithm of its node further from the root. The color and the thickness\n"
    "depend linearly on the log₁₀ of how often the edge was traversed."
)
ax.text(title_x, title_y - (y_max - y_min) * 0.06,
        desc_text, fontsize=9, color='#5a3d7a',
        fontfamily='serif', ha='left', va='top',
        linespacing=1.5)

# Label for 837,799
if longest_path_start in node_pos:
    lx, ly = node_pos[longest_path_start]
    ax.annotate(f'{longest_path_start:,}\nThe longest path\nbelow {MAX_START:,}',
                (lx, ly), fontsize=9, color='#d4a017',
                fontweight='bold', ha='center', va='top',
                xytext=(15, -10), textcoords='offset points',
                fontfamily='serif')

# Label for 2^19 = 524,288
val_2_19 = 2**19
if val_2_19 in node_pos:
    px, py = node_pos[val_2_19]
    ax.annotate(f'2¹⁹ = {val_2_19:,}', (px, py),
                fontsize=8, color='#d4a017',
                ha='right', va='bottom',
                xytext=(-5, 3), textcoords='offset points')

# Padding
pad_x = (x_max - x_min) * 0.03
pad_y = (y_max - y_min) * 0.03
ax.set_xlim(x_min - pad_x, x_max + pad_x)
ax.set_ylim(y_min - pad_y, y_max + pad_y)

plt.tight_layout(pad=0.5)
outpath = '/home/john/Projects/collatz/collatz_tree.png'
fig.savefig(outpath, dpi=150, facecolor=BG_COLOR,
            bbox_inches='tight', pad_inches=0.3)
plt.close()
print(f"Saved: {outpath}")
