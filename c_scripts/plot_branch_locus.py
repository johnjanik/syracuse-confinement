#!/usr/bin/env python3
"""
Companion plotting script for branch_locus (C version).
Reads CSV data files written by ./branch_locus and generates
4 PNG figures.

Usage: python3 plot_branch_locus.py [data_dir] [output_dir]
  data_dir   - directory containing CSV files (default: .)
  output_dir - directory for PNG output   (default: .)
"""

import sys
import os
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import TwoSlopeNorm
from matplotlib.patches import Rectangle

data_dir   = sys.argv[1] if len(sys.argv) > 1 else '.'
output_dir = sys.argv[2] if len(sys.argv) > 2 else '.'

LOG2_3     = 1.58496250072115618
INV_LOG2_3 = 1.0 / LOG2_3

# ── Load data ────────────────────────────────────────────────────────

def load_params():
    params = {}
    with open(os.path.join(data_dir, 'branch_params.csv')) as f:
        next(f)  # skip header
        for line in f:
            k, v = line.strip().split(',', 1)
            try:
                params[k] = int(v)
            except ValueError:
                params[k] = float(v)
    return params

par = load_params()
N   = par['N']
global_p_odd = par['global_p_odd']

summary = np.genfromtxt(os.path.join(data_dir, 'branch_summary.csv'),
                        delimiter=',', names=True)

# Load per-cell data into dicts keyed by k
cells = {}
with open(os.path.join(data_dir, 'branch_cells.csv')) as f:
    next(f)
    for line in f:
        parts = line.strip().split(',')
        k = int(parts[0])
        r2, r3 = int(parts[1]), int(parts[2])
        if k not in cells:
            cells[k] = {
                'p_odd':     np.zeros((k, k)),
                'entropy':   np.zeros((k, k)),
                'slope_dev': np.zeros((k, k)),
                'total':     np.zeros((k, k), dtype=np.int64),
                'cell_type': np.full((k, k), '', dtype=object),
            }
        cells[k]['p_odd'][r2, r3]     = float(parts[6])
        cells[k]['entropy'][r2, r3]   = float(parts[9])
        cells[k]['slope_dev'][r2, r3] = float(parts[8])
        cells[k]['total'][r2, r3]     = int(parts[5])
        cells[k]['cell_type'][r2, r3] = parts[10]

# Load foliation data
foliation = {}
with open(os.path.join(data_dir, 'branch_foliation.csv')) as f:
    next(f)
    for line in f:
        parts = line.strip().split(',')
        k = int(parts[0])
        r2, r3 = int(parts[1]), int(parts[2])
        if k not in foliation:
            foliation[k] = {
                'dist_unstable': np.zeros((k, k)),
                'dist_stable':   np.zeros((k, k)),
            }
        foliation[k]['dist_unstable'][r2, r3] = float(parts[3])
        foliation[k]['dist_stable'][r2, r3]   = float(parts[4])


# ── Helper: draw foliation lines on torus ────────────────────────────

def draw_foliation(ax, k, slope, color, label, linestyle='--'):
    """Draw wrapped foliation lines on a k x k torus."""
    n_lines = min(k, 5)
    offsets = np.linspace(0, k, n_lines, endpoint=False)
    first = True
    for c in offsets:
        xs = np.linspace(-0.5, k - 0.5, 1000)
        ys = (slope * xs + c) % k
        # Find wrap-around discontinuities
        breaks = np.where(np.abs(np.diff(ys)) > k / 2)[0] + 1
        xs_parts = np.split(xs, breaks)
        ys_parts = np.split(ys, breaks)
        # Join with NaN separators for a single plot call
        xs_joined = np.concatenate([np.append(s, np.nan) for s in xs_parts])
        ys_joined = np.concatenate([np.append(s, np.nan) for s in ys_parts])
        lbl = label if first else None
        ax.plot(xs_joined, ys_joined, color=color, linestyle=linestyle,
                linewidth=0.8, alpha=0.6, label=lbl)
        first = False


# ── Select panel k values ────────────────────────────────────────────

panel_ks = [k for k in [108, 216, 324, 432, 648, 1296] if k in cells]
n_panels = len(panel_ks)
ncols = 4
nrows = max(1, (n_panels + ncols - 1) // ncols)


# ── Figure 1: Parity heatmaps ───────────────────────────────────────

fig, axes = plt.subplots(nrows, ncols, figsize=(16, 4 * nrows))
if nrows == 1:
    axes = axes.reshape(1, -1)
axes = axes.flatten()

for idx, k in enumerate(panel_ks):
    ax = axes[idx]
    grid = cells[k]['p_odd'].copy()
    mask_empty = cells[k]['total'] == 0
    grid_plot = np.ma.array(grid, mask=mask_empty)

    if grid_plot.count() > 0:
        p_min = float(grid_plot.min())
        p_max = float(grid_plot.max())
        vmin_p = min(p_min, global_p_odd - 0.01)
        vmax_p = max(p_max, global_p_odd + 0.01)
    else:
        vmin_p, vmax_p = 0.0, 1.0

    norm = TwoSlopeNorm(vcenter=global_p_odd, vmin=vmin_p, vmax=vmax_p)
    im = ax.imshow(grid_plot.T, origin='lower', aspect='equal',
                   cmap='RdYlBu_r', norm=norm, interpolation='nearest')

    # Cell annotations for k <= 4
    if k <= 4:
        for i in range(k):
            for j in range(k):
                if cells[k]['total'][i, j] > 0:
                    val = cells[k]['p_odd'][i, j]
                    ax.text(i, j, f'{val:.3f}', ha='center', va='center',
                            fontsize=max(6, 10 - k), color='black')
                else:
                    ax.text(i, j, '\u2014', ha='center', va='center',
                            fontsize=8, color='gray')

    # Foliation overlay (only for small k where lines are visible)
    if k <= 72:
        draw_foliation(ax, k, LOG2_3, 'red', 'Unstable', '--')
        draw_foliation(ax, k, -INV_LOG2_3, 'blue', 'Stable', ':')

    # Panel title
    mask_k = summary['k'] == k
    if np.any(mask_k):
        a_lev = int(summary['a'][mask_k][0])
        b_lev = int(summary['b'][mask_k][0])
        label = f'k = {k}  ($2^{a_lev} \\cdot 3^{b_lev}$)'
    else:
        label = f'k = {k}'

    ax.set_title(label, fontsize=10)
    ax.set_xlabel('$\\nu_2$ mod k')
    ax.set_ylabel('$\\nu_3$ mod k')
    plt.colorbar(im, ax=ax, shrink=0.8)
    if idx == 0:
        ax.legend(fontsize=6, loc='upper right')

for idx in range(n_panels, len(axes)):
    axes[idx].set_visible(False)

fig.suptitle(f'Branch Parity $p_{{odd}}$ on Finite Tori  (N = {N:,})',
             fontsize=14, y=1.01)
fig.tight_layout()
out = os.path.join(output_dir, 'branch_parity_heatmaps.png')
fig.savefig(out, dpi=150, bbox_inches='tight')
plt.close(fig)
print(f'  Saved {out}')


# ── Figure 2: Entropy heatmaps ──────────────────────────────────────

fig, axes = plt.subplots(nrows, ncols, figsize=(16, 4 * nrows))
if nrows == 1:
    axes = axes.reshape(1, -1)
axes = axes.flatten()

for idx, k in enumerate(panel_ks):
    ax = axes[idx]
    grid = cells[k]['entropy'].copy()
    mask_empty = cells[k]['total'] == 0
    grid_plot = np.ma.array(grid, mask=mask_empty)

    im = ax.imshow(grid_plot.T, origin='lower', aspect='equal',
                   cmap='viridis', interpolation='nearest',
                   vmin=0, vmax=1)

    if k <= 4:
        for i in range(k):
            for j in range(k):
                if cells[k]['total'][i, j] > 0:
                    val = cells[k]['entropy'][i, j]
                    ax.text(i, j, f'{val:.3f}', ha='center', va='center',
                            fontsize=max(6, 10 - k), color='white')

    mask_k = summary['k'] == k
    if np.any(mask_k):
        a_lev = int(summary['a'][mask_k][0])
        b_lev = int(summary['b'][mask_k][0])
        label = f'k = {k}  ($2^{a_lev} \\cdot 3^{b_lev}$)'
    else:
        label = f'k = {k}'

    ax.set_title(label, fontsize=10)
    ax.set_xlabel('$\\nu_2$ mod k')
    ax.set_ylabel('$\\nu_3$ mod k')
    plt.colorbar(im, ax=ax, shrink=0.8, label='$H(p_{odd})$')

for idx in range(n_panels, len(axes)):
    axes[idx].set_visible(False)

fig.suptitle(f'Binary Entropy of Parity  (N = {N:,})',
             fontsize=14, y=1.01)
fig.tight_layout()
out = os.path.join(output_dir, 'branch_entropy_heatmaps.png')
fig.savefig(out, dpi=150, bbox_inches='tight')
plt.close(fig)
print(f'  Saved {out}')


# ── Figure 3: Slope deviation heatmaps ──────────────────────────────

fig, axes = plt.subplots(nrows, ncols, figsize=(16, 4 * nrows))
if nrows == 1:
    axes = axes.reshape(1, -1)
axes = axes.flatten()

for idx, k in enumerate(panel_ks):
    ax = axes[idx]
    grid = cells[k]['slope_dev'].copy()
    mask_empty = cells[k]['total'] == 0
    mask_pure  = (cells[k]['cell_type'] != 'branch')
    grid_plot  = np.ma.array(grid, mask=mask_empty | mask_pure)

    im = ax.imshow(grid_plot.T, origin='lower', aspect='equal',
                   cmap='hot', interpolation='nearest')

    # Mark singular cells with red borders
    mask_k = summary['k'] == k
    if np.any(mask_k):
        mean_dev  = float(summary['mean_slope_dev'][mask_k][0])
        std_dev   = float(summary['std_slope_dev'][mask_k][0])
        threshold = mean_dev + 2 * std_dev
        a_lev = int(summary['a'][mask_k][0])
        b_lev = int(summary['b'][mask_k][0])
        label = f'k = {k}  ($2^{a_lev} \\cdot 3^{b_lev}$)'

        for i in range(k):
            for j in range(k):
                if (cells[k]['cell_type'][i, j] == 'branch' and
                        cells[k]['slope_dev'][i, j] > threshold):
                    rect = Rectangle((i - 0.5, j - 0.5), 1, 1,
                                     linewidth=1.5, edgecolor='red',
                                     facecolor='none')
                    ax.add_patch(rect)
    else:
        label = f'k = {k}'

    ax.set_title(label, fontsize=10)
    ax.set_xlabel('$\\nu_2$ mod k')
    ax.set_ylabel('$\\nu_3$ mod k')
    plt.colorbar(im, ax=ax, shrink=0.8,
                 label='$|slope - 1/\\log_2 3|$')

for idx in range(n_panels, len(axes)):
    axes[idx].set_visible(False)

fig.suptitle(f'Slope Deviation from Foliation  (N = {N:,})',
             fontsize=14, y=1.01)
fig.tight_layout()
out = os.path.join(output_dir, 'branch_slope_heatmaps.png')
fig.savefig(out, dpi=150, bbox_inches='tight')
plt.close(fig)
print(f'  Saved {out}')


# ── Figure 4: Summary panels ────────────────────────────────────────

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

mask = summary['k'] > 1
ks      = summary['k'][mask].astype(int)
br_frac = summary['branch_fraction'][mask]
sing    = summary['singular_cells'][mask].astype(int)

x = np.arange(len(ks))

ax1.bar(x, br_frac, color='steelblue', alpha=0.8)
ax1.set_xticks(x)
ax1.set_xticklabels([str(k) for k in ks], rotation=45, fontsize=7)
ax1.set_ylabel('Branch fraction')
ax1.set_xlabel('Level $k$')
ax1.set_title('Branch Cell Fraction vs Level')
ax1.grid(True, alpha=0.3)
ax1.set_ylim(0, 1.05)

ax2.bar(x, sing, color='coral', alpha=0.8)
ax2.set_xticks(x)
ax2.set_xticklabels([str(k) for k in ks], rotation=45, fontsize=7)
ax2.set_ylabel('Singular cell count')
ax2.set_xlabel('Level $k$')
ax2.set_title('Singular Cells (slope dev > $2\\sigma$) vs Level')
ax2.grid(True, alpha=0.3)

fig.suptitle(f'Branch Locus Summary  (N = {N:,})', fontsize=13)
fig.tight_layout(rect=[0, 0, 1, 0.94])
out = os.path.join(output_dir, 'branch_summary.png')
fig.savefig(out, dpi=150, bbox_inches='tight')
plt.close(fig)
print(f'  Saved {out}')


print('\nDone.')
