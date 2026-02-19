#!/usr/bin/env python3
"""
Companion plotting script for profinite_compat (C version).
Reads CSV data files written by ./profinite_compat and generates
4 PNG figures.

Usage: python3 plot_profinite.py [data_dir] [output_dir]
  data_dir   - directory containing CSV files (default: .)
  output_dir - directory for PNG output   (default: .)
"""

import sys
import os
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import LogNorm
from matplotlib.patches import Rectangle

data_dir   = sys.argv[1] if len(sys.argv) > 1 else '.'
output_dir = sys.argv[2] if len(sys.argv) > 2 else '.'

# ── Load data ────────────────────────────────────────────────────────

def load_params():
    params = {}
    with open(os.path.join(data_dir, 'profinite_params.csv')) as f:
        next(f)  # skip header
        for line in f:
            k, v = line.strip().split(',', 1)
            try:
                params[k] = int(v)
            except ValueError:
                params[k] = float(v)
    return params

par  = load_params()
N    = par['N']

diag = np.genfromtxt(os.path.join(data_dir, 'profinite_diagnostics.csv'),
                     delimiter=',', names=True)

# Load mu_k grids from cell-per-row CSV
mu = {}
with open(os.path.join(data_dir, 'profinite_mu_k.csv')) as f:
    next(f)  # skip header
    for line in f:
        parts = line.strip().split(',')
        k, i, j, count = int(parts[0]), int(parts[1]), int(parts[2]), int(parts[3])
        if k not in mu:
            mu[k] = np.zeros((k, k), dtype=np.int64)
        mu[k][i, j] = count

# Load checkpoints
chk_file = os.path.join(data_dir, 'profinite_checkpoints.csv')
chk = None
if os.path.exists(chk_file) and os.path.getsize(chk_file) > 30:
    chk = np.genfromtxt(chk_file, delimiter=',', names=True)
    if chk.ndim == 0:
        chk = np.array([chk])

# ── Figure 1: Heatmaps of mu_k for k <= 36 ──────────────────────────

small_ks = sorted(mu.keys())
n_panels = len(small_ks)
ncols = 4
nrows = (n_panels + ncols - 1) // ncols

fig, axes = plt.subplots(nrows, ncols, figsize=(16, 4 * nrows))
axes = axes.flatten()

for idx, k in enumerate(small_ks):
    ax = axes[idx]
    grid = mu[k].astype(float)
    grid_plot = grid.copy()
    grid_plot[grid_plot == 0] = np.nan

    if k <= 4:
        im = ax.imshow(grid_plot.T, origin='lower', aspect='equal',
                       cmap='YlOrRd', interpolation='nearest')
        for i in range(k):
            for j in range(k):
                val = mu[k][i, j]
                ax.text(i, j, f'{val}', ha='center', va='center',
                        fontsize=max(6, 10 - k), color='black')
    else:
        vmin = np.nanmin(grid_plot[grid_plot > 0]) if np.any(grid_plot > 0) else 1
        vmax = np.nanmax(grid_plot)
        if vmin == vmax:
            vmin = max(1, vmax - 1)
        im = ax.imshow(grid_plot.T, origin='lower', aspect='equal',
                       cmap='YlOrRd', interpolation='nearest',
                       norm=LogNorm(vmin=vmin, vmax=vmax))

    # Find (a,b) for this k from diagnostics
    mask = diag['k'] == k
    if np.any(mask):
        a_lev = int(diag['a'][mask][0])
        b_lev = int(diag['b'][mask][0])
        label = f'k = {k}  ($2^{a_lev} \\cdot 3^{b_lev}$)'
    else:
        label = f'k = {k}'

    ax.set_title(label, fontsize=10)
    ax.set_xlabel('$\\nu_2$ mod k')
    ax.set_ylabel('$\\nu_3$ mod k')
    plt.colorbar(im, ax=ax, shrink=0.8)

for idx in range(n_panels, len(axes)):
    axes[idx].set_visible(False)

fig.suptitle(f'Torus Residue Distributions $\\mu_k$  (N = {N:,})',
             fontsize=14, y=1.01)
fig.tight_layout()
out = os.path.join(output_dir, 'profinite_heatmaps.png')
fig.savefig(out, dpi=150, bbox_inches='tight')
plt.close(fig)
print(f'  Saved {out}')


# ── Figure 2: Entropy and zero-cell fraction ─────────────────────────

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

# Filter out k=1
mask = diag['k'] > 1
ks      = diag['k'][mask].astype(int)
H_ratio = diag['H_ratio'][mask]
zf      = diag['zero_frac'][mask]

x = np.arange(len(ks))

ax1.bar(x, H_ratio, color='steelblue', alpha=0.8)
ax1.set_xticks(x)
ax1.set_xticklabels([str(k) for k in ks], rotation=45, fontsize=7)
ax1.set_ylabel('$H(\\mu_k) / \\log_2(k^2)$')
ax1.set_xlabel('Level $k$')
ax1.set_title('Normalised Entropy of $\\mu_k$')
ax1.axhline(y=1.0, color='red', linestyle='--', alpha=0.5,
            label='Uniform (Haar)')
ax1.legend()
ax1.set_ylim(0, 1.05)
ax1.grid(True, alpha=0.3)

ax2.bar(x, zf * 100, color='coral', alpha=0.8)
ax2.set_xticks(x)
ax2.set_xticklabels([str(k) for k in ks], rotation=45, fontsize=7)
ax2.set_ylabel('Zero-cell fraction (%)')
ax2.set_xlabel('Level $k$')
ax2.set_title('Empty Cells in $(\\mathbb{Z}/k\\mathbb{Z})^2$')
ax2.grid(True, alpha=0.3)

fig.suptitle('Entropy Decay and Support Sparsification',
             fontsize=13)
fig.tight_layout(rect=[0, 0, 1, 0.94])
out = os.path.join(output_dir, 'profinite_entropy.png')
fig.savefig(out, dpi=150, bbox_inches='tight')
plt.close(fig)
print(f'  Saved {out}')


# ── Figure 3: Forbidden cells ────────────────────────────────────────

fig = plt.figure(figsize=(14, 5))

# Left panel: mu_3 heatmap with (1,1) highlighted
ax1 = fig.add_subplot(121)
if 3 in mu:
    grid3 = mu[3].astype(float)
    im = ax1.imshow(grid3.T, origin='lower', aspect='equal',
                    cmap='YlOrRd', interpolation='nearest')
    for i in range(3):
        for j in range(3):
            val = mu[3][i, j]
            color = 'red' if (i == 1 and j == 1) else 'black'
            weight = 'bold' if (i == 1 and j == 1) else 'normal'
            ax1.text(i, j, f'{val:,}', ha='center', va='center',
                     fontsize=11, color=color, fontweight=weight)

    # Highlight the forbidden cell
    rect = Rectangle((0.5, 0.5), 1, 1, linewidth=3,
                      edgecolor='red', facecolor='none', linestyle='--')
    ax1.add_patch(rect)
    ax1.set_xticks([0, 1, 2])
    ax1.set_yticks([0, 1, 2])
    ax1.set_xlabel('$\\nu_2$ mod 3')
    ax1.set_ylabel('$\\nu_3$ mod 3')
    ax1.set_title('$\\mu_3$: The Forbidden Cell $(1,1)$')
    plt.colorbar(im, ax=ax1, shrink=0.8)

# Right panel: forbidden cell count vs k
ax2 = fig.add_subplot(122)
forbidden_counts = diag['zero_cells'][mask].astype(int)
ax2.bar(x, forbidden_counts, color='firebrick', alpha=0.8)
ax2.set_xticks(x)
ax2.set_xticklabels([str(k) for k in ks], rotation=45, fontsize=7)
ax2.set_ylabel('Number of zero cells')
ax2.set_xlabel('Level $k$')
ax2.set_title('Forbidden Cell Count vs Level')
ax2.set_yscale('symlog', linthresh=1)
ax2.grid(True, alpha=0.3)

fig.suptitle(f'Forbidden Cells in Torus Residue Distributions  (N = {N:,})',
             fontsize=13)
fig.tight_layout(rect=[0, 0, 1, 0.94])
out = os.path.join(output_dir, 'profinite_forbidden.png')
fig.savefig(out, dpi=150, bbox_inches='tight')
plt.close(fig)
print(f'  Saved {out}')


# ── Figure 4: Checkpoints — mu_3(1,1) persistence ───────────────────

fig, ax = plt.subplots(figsize=(8, 5))

if chk is not None and len(chk) > 0:
    chk_ns = chk['checkpoint_N']
    chk_vals = chk['mu3_11']

    ax.plot(chk_ns, chk_vals, 'ro-', markersize=10, linewidth=2,
            label='$\\mu_3(1,1)$')
    ax.set_xscale('log')
    ax.set_xlabel('$N$ (number of starting values)')
    ax.set_ylabel('$\\mu_3(1,1)$ count')
    ax.set_title('Persistence of the Forbidden Cell $\\mu_3(1,1) = 0$')

    # Add annotation
    for i, (xv, yv) in enumerate(zip(chk_ns, chk_vals)):
        ax.annotate(f'{int(yv)}', (xv, yv),
                    textcoords="offset points", xytext=(0, 15),
                    ha='center', fontsize=12, fontweight='bold',
                    color='red')

    ax.axhline(y=0, color='gray', linestyle='--', alpha=0.5)
    ax.legend(fontsize=12)
    ax.grid(True, alpha=0.3)

    # Add expected count under uniformity
    ax2 = ax.twinx()
    expected = chk_ns / 9.0  # N/9 expected under uniform mu_3
    ax2.plot(chk_ns, expected, 'b--', alpha=0.5, linewidth=1.5,
             label='Expected under uniformity (N/9)')
    ax2.set_ylabel('Expected count under Haar', color='blue')
    ax2.tick_params(axis='y', labelcolor='blue')
    ax2.legend(loc='center right', fontsize=9)
else:
    ax.text(0.5, 0.5, 'No checkpoint data available\n(run with N >= 1000000)',
            ha='center', va='center', transform=ax.transAxes, fontsize=14)
    ax.set_title('Persistence of the Forbidden Cell $\\mu_3(1,1) = 0$')

fig.tight_layout()
out = os.path.join(output_dir, 'profinite_checkpoints.png')
fig.savefig(out, dpi=150, bbox_inches='tight')
plt.close(fig)
print(f'  Saved {out}')


print('\nDone.')
