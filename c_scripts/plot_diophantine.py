#!/usr/bin/env python3
"""
Diophantine foliation analysis for branch_locus data.

Visualises how Diophantine best-approximant levels (k=729=3^6)
relate to the branch locus and foliation structure.
Includes transition valence, SFT "11" verification, and shadow offset plots.

Usage: python3 plot_diophantine.py [data_dir] [output_dir]
"""

import sys
import os
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import TwoSlopeNorm, Normalize
from matplotlib.patches import FancyArrowPatch
import matplotlib.gridspec as gridspec

data_dir   = sys.argv[1] if len(sys.argv) > 1 else '.'
output_dir = sys.argv[2] if len(sys.argv) > 2 else '.'

LOG2_3     = 1.58496250072115618
INV_LOG2_3 = 1.0 / LOG2_3

# ── Load data ────────────────────────────────────────────────────────

def load_params():
    params = {}
    with open(os.path.join(data_dir, 'branch_params.csv')) as f:
        next(f)
        for line in f:
            k, v = line.strip().split(',', 1)
            try:    params[k] = int(v)
            except: params[k] = float(v)
    return params

par = load_params()
N   = par['N']
global_p_odd = par['global_p_odd']

summary = np.genfromtxt(os.path.join(data_dir, 'branch_summary.csv'),
                        delimiter=',', names=True)

# Load per-cell data into dicts keyed by k
cells = {}
print("Loading branch_cells.csv...")
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
                'even':      np.zeros((k, k), dtype=np.int64),
                'odd':       np.zeros((k, k), dtype=np.int64),
                'cell_type': np.full((k, k), '', dtype=object),
            }
        cells[k]['p_odd'][r2, r3]     = float(parts[6])
        cells[k]['entropy'][r2, r3]   = float(parts[9])
        cells[k]['slope_dev'][r2, r3] = float(parts[8])
        cells[k]['total'][r2, r3]     = int(parts[5])
        cells[k]['even'][r2, r3]      = int(parts[3])
        cells[k]['odd'][r2, r3]       = int(parts[4])
        cells[k]['cell_type'][r2, r3] = parts[10]

# Load foliation distances
foliation = {}
print("Loading branch_foliation.csv...")
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


# ── Helper: torus distance from foliation ─────────────────────────────

def torus_fol_dist(r2, r3, slope, k):
    delta = r3 - slope * r2
    delta = delta % k
    if delta > k / 2: delta -= k
    if delta < -k / 2: delta += k
    return abs(delta) / np.sqrt(1 + slope**2)


# ── Helper: draw foliation lines on axes ──────────────────────────────

def draw_foliation(ax, k, slope, color, label, linestyle='--', alpha=0.6):
    n_lines = min(k, 8)
    offsets = np.linspace(0, k, n_lines, endpoint=False)
    first = True
    for c in offsets:
        xs = np.linspace(-0.5, k - 0.5, 2000)
        ys = (slope * xs + c) % k
        breaks = np.where(np.abs(np.diff(ys)) > k / 2)[0] + 1
        xs_parts = np.split(xs, breaks)
        ys_parts = np.split(ys, breaks)
        for xp, yp in zip(xs_parts, ys_parts):
            if len(xp) > 1:
                ax.plot(xp, yp, color=color, linestyle=linestyle,
                        linewidth=0.5, alpha=alpha,
                        label=label if first else None)
                first = False


# ══════════════════════════════════════════════════════════════════════
# Figure 1: k=729 branch cell topology (main result)
# ══════════════════════════════════════════════════════════════════════

print("\nGenerating diophantine_branch_k729.png...")
fig = plt.figure(figsize=(18, 14))
gs = gridspec.GridSpec(2, 3, figure=fig, hspace=0.3, wspace=0.35)

# ── Panel (0,0): k=81 reference — fully saturated ────────────────────
ax1 = fig.add_subplot(gs[0, 0])
k81 = 81
if k81 in cells:
    data = cells[k81]
    mask = data['cell_type'] == 'branch'
    img = np.where(mask, data['p_odd'], np.nan)
    vmin, vmax = np.nanmin(img), np.nanmax(img)
    vcen = global_p_odd
    norm = TwoSlopeNorm(vmin=vmin, vcenter=vcen, vmax=vmax)
    im = ax1.imshow(img, origin='lower', cmap='RdYlBu_r', norm=norm,
                    interpolation='nearest', aspect='equal')
    # Mark singular cells
    thresh = np.mean(data['slope_dev'][mask]) + 2*np.std(data['slope_dev'][mask])
    sing_mask = mask & (data['slope_dev'] > thresh)
    sr2, sr3 = np.where(sing_mask)
    ax1.scatter(sr3, sr2, s=2, c='lime', marker='s', linewidths=0, zorder=3)
    draw_foliation(ax1, k81, INV_LOG2_3, 'green', r'slope $\log_3 2$', alpha=0.4)
    ax1.set_title(f'k = 81 = $3^4$  (100% branch)\n{np.sum(sing_mask)} singular cells',
                  fontsize=11)
    ax1.set_xlabel(r'$\nu_3$ mod 81')
    ax1.set_ylabel(r'$\nu_2$ mod 81')
    ax1.set_xlim(-0.5, k81 - 0.5)
    ax1.set_ylim(-0.5, k81 - 0.5)

# ── Panel (0,1): k=729 branch cells colored by p_odd ─────────────────
ax2 = fig.add_subplot(gs[0, 1])
k729 = 729
if k729 in cells:
    data = cells[k729]
    branch_mask = (data['cell_type'] == 'branch')
    br2, br3 = np.where(branch_mask)
    p_vals = data['p_odd'][branch_mask]
    n_branch = len(br2)

    norm2 = TwoSlopeNorm(vmin=np.min(p_vals), vcenter=global_p_odd,
                         vmax=np.max(p_vals))
    sc = ax2.scatter(br3, br2, c=p_vals, cmap='RdYlBu_r', norm=norm2,
                     s=0.3, linewidths=0, zorder=2)

    # Foliation lines
    draw_foliation(ax2, k729, INV_LOG2_3, 'green', r'slope $\log_3 2$',
                   linestyle='--', alpha=0.3)
    draw_foliation(ax2, k729, LOG2_3, 'red', r'slope $\log_2 3$',
                   linestyle=':', alpha=0.3)

    plt.colorbar(sc, ax=ax2, label=r'$p_{\rm odd}$', shrink=0.8)
    ax2.set_title(f'k = 729 = $3^6$  (Diophantine)\n'
                  f'{n_branch} branch cells / {k729**2} = {100*n_branch/k729**2:.2f}%',
                  fontsize=11)
    ax2.set_xlabel(r'$\nu_3$ mod 729')
    ax2.set_ylabel(r'$\nu_2$ mod 729')
    ax2.set_xlim(-0.5, k729 - 0.5)
    ax2.set_ylim(-0.5, k729 - 0.5)
    ax2.set_aspect('equal')

# ── Panel (0,2): k=729 cell type map (branch/pure_even/pure_odd/empty)
ax3 = fig.add_subplot(gs[0, 2])
if k729 in cells:
    data = cells[k729]
    # Show non-empty cells by type
    pe_mask = data['cell_type'] == 'pure_even'
    po_mask = data['cell_type'] == 'pure_odd'
    br_mask = data['cell_type'] == 'branch'

    pe_r2, pe_r3 = np.where(pe_mask)
    po_r2, po_r3 = np.where(po_mask)
    br_r2, br_r3 = np.where(br_mask)

    ax3.scatter(pe_r3, pe_r2, s=0.15, c='steelblue', alpha=0.5, linewidths=0,
                label=f'pure_even ({len(pe_r2)})')
    ax3.scatter(po_r3, po_r2, s=0.15, c='firebrick', alpha=0.5, linewidths=0,
                label=f'pure_odd ({len(po_r2)})')
    ax3.scatter(br_r3, br_r2, s=0.15, c='gold', alpha=0.7, linewidths=0,
                label=f'branch ({len(br_r2)})')

    draw_foliation(ax3, k729, INV_LOG2_3, 'green', None, alpha=0.25)

    ax3.legend(loc='upper right', fontsize=8, markerscale=10)
    ax3.set_title(f'k = 729: cell type map\n'
                  f'{np.sum(data["total"] > 0)} non-empty / {k729**2} total',
                  fontsize=11)
    ax3.set_xlabel(r'$\nu_3$ mod 729')
    ax3.set_ylabel(r'$\nu_2$ mod 729')
    ax3.set_xlim(-0.5, k729 - 0.5)
    ax3.set_ylim(-0.5, k729 - 0.5)
    ax3.set_aspect('equal')

# ── Panel (1,0): Distance from unstable foliation — branch vs all ─────
ax4 = fig.add_subplot(gs[1, 0])
if k729 in foliation and k729 in cells:
    data = cells[k729]
    fol = foliation[k729]
    du = fol['dist_unstable']

    # All non-empty cells
    nonempty = data['total'] > 0
    branch   = data['cell_type'] == 'branch'

    du_nonempty = du[nonempty]
    du_branch   = du[branch]

    max_dist = k729 / (2 * np.sqrt(1 + INV_LOG2_3**2))
    bins = np.linspace(0, min(max_dist, 200), 80)

    ax4.hist(du_nonempty, bins=bins, density=True, alpha=0.5, color='gray',
             label=f'all non-empty ({np.sum(nonempty)})')
    ax4.hist(du_branch, bins=bins, density=True, alpha=0.7, color='gold',
             label=f'branch ({np.sum(branch)})')
    ax4.axvline(0.5, color='green', linestyle='--', linewidth=1,
                label='foliation threshold (0.5)')
    ax4.set_xlabel('Distance from unstable foliation')
    ax4.set_ylabel('Density')
    ax4.set_title('k = 729: foliation distance distribution', fontsize=11)
    ax4.legend(fontsize=8)

# ── Panel (1,1): Same for k=81 (comparison) ──────────────────────────
ax5 = fig.add_subplot(gs[1, 1])
if k81 in foliation and k81 in cells:
    data = cells[k81]
    fol = foliation[k81]
    du = fol['dist_unstable']

    nonempty = data['total'] > 0
    branch   = data['cell_type'] == 'branch'

    # For k=81, compute singular cell distances
    thresh81 = np.mean(data['slope_dev'][branch]) + 2*np.std(data['slope_dev'][branch])
    singular = branch & (data['slope_dev'] > thresh81)

    du_branch   = du[branch]
    du_singular = du[singular]

    max_dist = k81 / (2 * np.sqrt(1 + INV_LOG2_3**2))
    bins = np.linspace(0, max_dist, 40)

    ax5.hist(du_branch, bins=bins, density=True, alpha=0.5, color='gold',
             label=f'branch ({np.sum(branch)})')
    ax5.hist(du_singular, bins=bins, density=True, alpha=0.7, color='lime',
             label=f'singular ({np.sum(singular)})')
    ax5.axvline(0.5, color='green', linestyle='--', linewidth=1)
    ax5.set_xlabel('Distance from unstable foliation')
    ax5.set_ylabel('Density')
    ax5.set_title('k = 81: foliation distance (reference)', fontsize=11)
    ax5.legend(fontsize=8)

# ── Panel (1,2): Summary — branch count & enrichment vs k ────────────
ax6 = fig.add_subplot(gs[1, 2])

# Extract from summary
ks_all = summary['k'].astype(int)
br_all = summary['branch_cells'].astype(int)
sing_all = summary['singular_cells'].astype(int)

# Only plot levels with meaningful data
mask_plot = br_all > 0
ks_p = ks_all[mask_plot]
br_p = br_all[mask_plot]

ax6.semilogy(range(len(ks_p)), br_p, 'o-', color='gold', markersize=5,
             label='branch cells')

# Horizontal line at 13688
ax6.axhline(13688, color='gray', linestyle=':', alpha=0.5,
            label='asymptotic: 13,688')

# Highlight Diophantine levels
for i, k in enumerate(ks_p):
    if k == 729:
        ax6.plot(i, br_p[i], 'D', color='red', markersize=8, zorder=5)
    if k == 81:
        ax6.plot(i, br_p[i], 's', color='lime', markersize=8, zorder=5)

ax6.set_xticks(range(len(ks_p)))
ax6.set_xticklabels([str(k) for k in ks_p], rotation=70, fontsize=7)
ax6.set_xlabel('Level k')
ax6.set_ylabel('Branch cell count')
ax6.set_title('Branch count freezes at k > 108', fontsize=11)
ax6.legend(fontsize=8, loc='lower right')
ax6.grid(True, alpha=0.3)

fig.suptitle(f'Diophantine Foliation Analysis — N = {N:.2e}\n'
             f'Best approximant: 460/729 (err 7.2e-5)',
             fontsize=13, fontweight='bold', y=0.98)

plt.savefig(os.path.join(output_dir, 'diophantine_branch_k729.png'),
            dpi=150, bbox_inches='tight')
plt.close()
print("  Saved diophantine_branch_k729.png")


# ══════════════════════════════════════════════════════════════════════
# Figure 2: k=729 zoom — branch cell structure near foliation
# ══════════════════════════════════════════════════════════════════════

print("\nGenerating diophantine_k729_zoom.png...")
fig, axes = plt.subplots(1, 3, figsize=(18, 6))

if k729 in cells:
    data = cells[k729]
    branch_mask = data['cell_type'] == 'branch'
    br2, br3 = np.where(branch_mask)
    p_vals = data['p_odd'][branch_mask]

    # Zoom windows centered on different torus regions
    zooms = [
        (0, 150, 0, 150, 'Origin region'),
        (200, 400, 100, 350, 'Mid-torus'),
        (460, 600, 290, 430, 'Near lattice point (460,729)')
    ]

    for ax, (r2lo, r2hi, r3lo, r3hi, title) in zip(axes, zooms):
        # Filter branch cells in this window
        in_win = (br2 >= r2lo) & (br2 < r2hi) & (br3 >= r3lo) & (br3 < r3hi)
        if np.any(in_win):
            norm_z = TwoSlopeNorm(vmin=np.min(p_vals), vcenter=global_p_odd,
                                  vmax=np.max(p_vals))
            ax.scatter(br3[in_win], br2[in_win], c=p_vals[in_win],
                       cmap='RdYlBu_r', norm=norm_z, s=4, linewidths=0)

        # Draw foliation lines
        xs = np.linspace(r3lo - 0.5, r3hi - 0.5, 1000)
        for c_off in range(-5, 6):
            ys_u = INV_LOG2_3 * xs + c_off * k729
            ys_s = -LOG2_3 * xs + c_off * k729
            ax.plot(xs, ys_u, 'g--', linewidth=0.8, alpha=0.4,
                    label=r'$\log_3 2$' if c_off == 0 else None)
            ax.plot(xs, ys_s, 'r:', linewidth=0.8, alpha=0.3,
                    label=r'$\log_2 3$' if c_off == 0 else None)

        # Also mark pure_even and pure_odd in lighter colors
        pe = data['cell_type'] == 'pure_even'
        po = data['cell_type'] == 'pure_odd'
        pe2, pe3 = np.where(pe)
        po2, po3 = np.where(po)
        pe_in = (pe2 >= r2lo) & (pe2 < r2hi) & (pe3 >= r3lo) & (pe3 < r3hi)
        po_in = (po2 >= r2lo) & (po2 < r2hi) & (po3 >= r3lo) & (po3 < r3hi)
        if np.any(pe_in):
            ax.scatter(pe3[pe_in], pe2[pe_in], s=1, c='steelblue', alpha=0.3,
                       linewidths=0, zorder=1)
        if np.any(po_in):
            ax.scatter(po3[po_in], po2[po_in], s=1, c='firebrick', alpha=0.3,
                       linewidths=0, zorder=1)

        ax.set_xlim(r3lo - 0.5, r3hi - 0.5)
        ax.set_ylim(r2lo - 0.5, r2hi - 0.5)
        ax.set_aspect('equal')
        ax.set_title(title, fontsize=11)
        ax.set_xlabel(r'$\nu_3$')
        ax.set_ylabel(r'$\nu_2$')
        if ax == axes[0]:
            ax.legend(fontsize=8, loc='upper right')

fig.suptitle(f'k = 729 = $3^6$: Zoomed branch cell structure\n'
             f'Gold = branch (both parities), Blue = pure even, Red = pure odd',
             fontsize=12, fontweight='bold')
plt.savefig(os.path.join(output_dir, 'diophantine_k729_zoom.png'),
            dpi=150, bbox_inches='tight')
plt.close()
print("  Saved diophantine_k729_zoom.png")


# ══════════════════════════════════════════════════════════════════════
# Figure 3: Foliation depletion analysis
# ══════════════════════════════════════════════════════════════════════

print("\nGenerating diophantine_foliation_depletion.png...")
fig, axes = plt.subplots(1, 3, figsize=(18, 5.5))

# Panel 1: Enrichment vs k for all levels
ax = axes[0]
# Compute enrichment for each level
enrich_data = []
for row in summary:
    k = int(row['k'])
    if k not in cells or k not in foliation:
        continue
    data_k = cells[k]
    fol_k = foliation[k]

    branch = data_k['cell_type'] == 'branch'
    on_u = fol_k['dist_unstable'] < 0.5
    n_branch = np.sum(branch)
    n_on_u = np.sum(on_u)
    n_both = np.sum(branch & on_u)
    ncells = k * k

    expected = n_branch * n_on_u / ncells if ncells > 0 else 0
    enrichment = n_both / expected if expected > 0 else np.nan

    enrich_data.append((k, enrichment, n_branch, n_on_u, n_both))

if enrich_data:
    e_ks = [d[0] for d in enrich_data]
    e_en = [d[1] for d in enrich_data]

    colors = ['red' if k in (729,) else 'lime' if k == 81 else 'steelblue'
              for k in e_ks]
    sizes = [80 if k in (729, 81) else 30 for k in e_ks]

    ax.scatter(range(len(e_ks)), e_en, c=colors, s=sizes, zorder=3)
    ax.plot(range(len(e_ks)), e_en, 'k-', alpha=0.3, zorder=1)
    ax.axhline(1.0, color='gray', linestyle=':', alpha=0.5, label='random expectation')
    ax.set_xticks(range(len(e_ks)))
    ax.set_xticklabels([str(k) for k in e_ks], rotation=70, fontsize=7)
    ax.set_ylabel('Foliation enrichment (obs/expected)')
    ax.set_xlabel('Level k')
    ax.set_title('Branch-foliation enrichment\n'
                 '(green=k=81, red=k=729)', fontsize=11)
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    ax.set_ylim(0, 1.2)

# Panel 2: p_odd distribution for branch cells at k=729 vs k=81
ax = axes[1]
if k729 in cells and k81 in cells:
    p729 = cells[k729]['p_odd'][cells[k729]['cell_type'] == 'branch']
    p81  = cells[k81]['p_odd'][cells[k81]['cell_type'] == 'branch']

    bins = np.linspace(0, 0.7, 60)
    ax.hist(p81, bins=bins, density=True, alpha=0.5, color='lime',
            label=f'k=81 (n={len(p81)})')
    ax.hist(p729, bins=bins, density=True, alpha=0.5, color='red',
            label=f'k=729 (n={len(p729)})')
    ax.axvline(global_p_odd, color='black', linestyle='--', linewidth=1,
               label=f'global $p_{{odd}}$ = {global_p_odd:.4f}')
    ax.set_xlabel(r'$p_{\rm odd}$')
    ax.set_ylabel('Density')
    ax.set_title(r'Branch cell $p_{\rm odd}$ distribution', fontsize=11)
    ax.legend(fontsize=8)

# Panel 3: Diophantine approximation quality vs singular density
ax = axes[2]
# Best approximations for pure 3-adic levels
dioph_approx = {
    3:   (2,     3),
    9:   (17,    27),    # same best approx as 27, 81
    27:  (17,    27),
    81:  (17,    27),
    729: (460,   729),
}

pure3_levels = []
for row in summary:
    k = int(row['k'])
    a = int(row['a'])
    if a != 0:  # pure 3-adic only
        continue
    b_cells = int(row['branch_cells'])
    s_cells = int(row['singular_cells'])
    bf = float(row['branch_fraction'])
    if b_cells == 0:
        continue

    if k in dioph_approx:
        p, q = dioph_approx[k]
        err = abs(p/q - INV_LOG2_3)
    else:
        # Compute best approximation for this 3^b
        best_p = round(k * INV_LOG2_3)
        err = abs(best_p / k - INV_LOG2_3)

    sing_density = s_cells / b_cells if b_cells > 0 else 0
    pure3_levels.append((k, err, sing_density, s_cells, b_cells, bf))

if pure3_levels:
    p3_ks = [d[0] for d in pure3_levels]
    p3_err = [d[1] for d in pure3_levels]
    p3_sd = [d[2] for d in pure3_levels]
    p3_sc = [d[3] for d in pure3_levels]
    p3_bf = [d[5] for d in pure3_levels]

    # Color by branch fraction
    sc = ax.scatter(p3_err, p3_sd, c=p3_bf, cmap='viridis', s=80,
                    edgecolors='black', linewidths=0.5, zorder=3)
    for i, k in enumerate(p3_ks):
        ax.annotate(f'$3^{{{int(np.log(k)/np.log(3)+0.5)}}}$={k}',
                    (p3_err[i], p3_sd[i]),
                    textcoords='offset points', xytext=(8, 4), fontsize=8)

    plt.colorbar(sc, ax=ax, label='Branch fraction', shrink=0.8)
    ax.set_xscale('log')
    ax.set_xlabel('Diophantine error  $|p/3^b - \\log_3 2|$')
    ax.set_ylabel('Singular cell density (singular / branch)')
    ax.set_title('Approximation quality vs\nsingular density (pure $3^b$ levels)',
                 fontsize=11)
    ax.grid(True, alpha=0.3)

fig.suptitle(f'Diophantine Foliation Depletion — N = {N:.2e}',
             fontsize=13, fontweight='bold', y=1.02)
plt.savefig(os.path.join(output_dir, 'diophantine_foliation_depletion.png'),
            dpi=150, bbox_inches='tight')
plt.close()
print("  Saved diophantine_foliation_depletion.png")


# ══════════════════════════════════════════════════════════════════════
# Figure 4: k=729 non-empty cell structure vs Diophantine foliation
# ══════════════════════════════════════════════════════════════════════

print("\nGenerating diophantine_k729_structure.png...")
fig, axes = plt.subplots(1, 2, figsize=(14, 6.5))

if k729 in cells and k729 in foliation:
    data = cells[k729]
    fol = foliation[k729]

    nonempty = data['total'] > 0
    ne_r2, ne_r3 = np.where(nonempty)
    ne_du = fol['dist_unstable'][nonempty]

    # Panel 1: All non-empty cells colored by distance from unstable foliation
    ax = axes[0]
    sc = ax.scatter(ne_r3, ne_r2, c=ne_du, cmap='hot_r', s=0.2,
                    linewidths=0, vmin=0, vmax=50)
    plt.colorbar(sc, ax=ax, label='Dist. from unstable foliation', shrink=0.8)

    # Mark the Diophantine lattice point: 460/729 line
    # The "near-integer" point is (729, 460) on the extended plane
    # On the torus, the foliation ν₃ = (460/729)·ν₂ passes through (0,0)
    # and wraps. Mark the closest lattice points.
    for m in range(4):
        r2_pt = int(round(729 * m / INV_LOG2_3)) % 729
        r3_pt = int(round(r2_pt * INV_LOG2_3)) % 729
        ax.plot(r3_pt, r2_pt, 'g*', markersize=10, zorder=5,
                label='Foliation lattice pts' if m == 0 else None)

    ax.set_title(f'k=729: non-empty cells colored by\ndistance from unstable foliation',
                 fontsize=11)
    ax.set_xlabel(r'$\nu_3$ mod 729')
    ax.set_ylabel(r'$\nu_2$ mod 729')
    ax.set_aspect('equal')
    ax.legend(fontsize=8, loc='upper right')

    # Panel 2: Radial density profile from unstable foliation
    ax = axes[1]

    # Bin cells by foliation distance
    max_d = 200
    dbins = np.linspace(0, max_d, 100)
    d_centers = 0.5 * (dbins[:-1] + dbins[1:])

    # All cells — expected count per bin (annular area on torus)
    # Approximate: number of cells at distance d is proportional to k
    # (each foliation line has ~k cells within distance dd)

    # Count non-empty and branch cells per distance bin
    ne_hist, _ = np.histogram(ne_du, bins=dbins)

    branch = data['cell_type'] == 'branch'
    br_du = fol['dist_unstable'][branch]
    br_hist, _ = np.histogram(br_du, bins=dbins)

    # Compute expected density (uniform on torus)
    # Total cells at each distance bin
    all_du = fol['dist_unstable'].ravel()
    all_hist, _ = np.histogram(all_du, bins=dbins)

    # Fraction non-empty
    with np.errstate(divide='ignore', invalid='ignore'):
        ne_frac = np.where(all_hist > 0, ne_hist / all_hist, 0)
        br_frac = np.where(all_hist > 0, br_hist / all_hist, 0)

    ax.plot(d_centers, ne_frac, 'gray', linewidth=1.5, label='non-empty fraction')
    ax.plot(d_centers, br_frac, 'gold', linewidth=2, label='branch fraction')
    ax.axvline(0.5, color='green', linestyle='--', linewidth=1, alpha=0.7,
               label='foliation threshold')

    # Expected branch fraction if uniform
    total_br = np.sum(branch)
    total_ne = np.sum(nonempty)
    ax.axhline(total_ne / (k729**2), color='gray', linestyle=':', alpha=0.5,
               label=f'overall non-empty: {100*total_ne/k729**2:.1f}%')
    ax.axhline(total_br / (k729**2), color='gold', linestyle=':', alpha=0.5,
               label=f'overall branch: {100*total_br/k729**2:.2f}%')

    ax.set_xlabel('Distance from unstable foliation')
    ax.set_ylabel('Fraction of cells')
    ax.set_title('k=729: radial profile from foliation', fontsize=11)
    ax.legend(fontsize=7, loc='upper right')
    ax.set_xlim(0, max_d)
    ax.grid(True, alpha=0.3)

fig.suptitle(f'k = 729 = $3^6$: Spatial Structure vs Foliation — N = {N:.2e}',
             fontsize=13, fontweight='bold')
plt.savefig(os.path.join(output_dir, 'diophantine_k729_structure.png'),
            dpi=150, bbox_inches='tight')
plt.close()
print("  Saved diophantine_k729_structure.png")

# ══════════════════════════════════════════════════════════════════════
# Figure 5: Transition / Valence / SFT / Shadow offset
# ══════════════════════════════════════════════════════════════════════

# Load transition data
trans = {}
print("\nLoading branch_transitions.csv...")
trans_path = os.path.join(data_dir, 'branch_transitions.csv')
if os.path.exists(trans_path):
    with open(trans_path) as f:
        next(f)
        for line in f:
            parts = line.strip().split(',')
            k = int(parts[0])
            r2, r3 = int(parts[1]), int(parts[2])
            if k not in trans:
                trans[k] = {
                    'ee':      np.zeros((k, k), dtype=np.int64),
                    'eo':      np.zeros((k, k), dtype=np.int64),
                    'oe':      np.zeros((k, k), dtype=np.int64),
                    'oo':      np.zeros((k, k), dtype=np.int64),
                    'valence': np.zeros((k, k), dtype=int),
                    'entry_type': np.full((k, k), '', dtype=object),
                }
            trans[k]['ee'][r2, r3]      = int(parts[3])
            trans[k]['eo'][r2, r3]      = int(parts[4])
            trans[k]['oe'][r2, r3]      = int(parts[5])
            trans[k]['oo'][r2, r3]      = int(parts[6])
            trans[k]['valence'][r2, r3] = int(parts[7])
            trans[k]['entry_type'][r2, r3] = parts[8]
    print(f"  Loaded transitions for k = {sorted(trans.keys())}")
else:
    print("  branch_transitions.csv not found, skipping transition plots")

# Load shadow data
shadow = {}
print("Loading branch_shadow.csv...")
shadow_path = os.path.join(data_dir, 'branch_shadow.csv')
if os.path.exists(shadow_path):
    with open(shadow_path) as f:
        next(f)
        for line in f:
            parts = line.strip().split(',')
            k = int(parts[0])
            r2, r3 = int(parts[1]), int(parts[2])
            if k not in shadow:
                shadow[k] = {
                    'dist_irrational': np.zeros((k, k)),
                    'dist_rational':   np.zeros((k, k)),
                    'shadow_offset':   np.zeros((k, k)),
                    'p_odd':           np.zeros((k, k)),
                    'cell_type':       np.full((k, k), '', dtype=object),
                }
            shadow[k]['dist_irrational'][r2, r3] = float(parts[3])
            shadow[k]['dist_rational'][r2, r3]   = float(parts[4])
            shadow[k]['shadow_offset'][r2, r3]   = float(parts[5])
            shadow[k]['p_odd'][r2, r3]           = float(parts[6])
            shadow[k]['cell_type'][r2, r3]       = parts[7]
    print(f"  Loaded shadow data for k = {sorted(shadow.keys())}")
else:
    print("  branch_shadow.csv not found, skipping shadow plots")

if trans or shadow:
    print("\nGenerating diophantine_transitions.png...")
    fig, axes = plt.subplots(2, 3, figsize=(24, 14))

    # ── Panel (0,0): k=729 transition valence map ─────────────────────
    ax = axes[0, 0]
    if k729 in trans and k729 in cells:
        td = trans[k729]
        cd = cells[k729]

        # Show cells with any transitions, colored by valence
        nonempty = cd['total'] > 0
        ne_r2, ne_r3 = np.where(nonempty)
        vals = td['valence'][nonempty]

        cmap_val = plt.cm.get_cmap('YlOrRd', 4)  # 0,1,2,3
        sc = ax.scatter(ne_r3, ne_r2, c=vals, cmap=cmap_val,
                        vmin=-0.5, vmax=3.5, s=0.2, linewidths=0, zorder=2)

        draw_foliation(ax, k729, INV_LOG2_3, 'green', r'slope $\log_3 2$',
                       linestyle='--', alpha=0.3)

        cb = plt.colorbar(sc, ax=ax, label='Transition valence', shrink=0.8,
                          ticks=[0, 1, 2, 3])
        cb.set_ticklabels(['0 (empty)', '1', '2', '3 (mixed)'])
        ax.set_title(f'k = 729: transition valence map\n'
                     f'(# distinct transition types ee/eo/oe per cell)',
                     fontsize=11)
        ax.set_xlabel(r'$\nu_3$ mod 729')
        ax.set_ylabel(r'$\nu_2$ mod 729')
        ax.set_xlim(-0.5, k729 - 0.5)
        ax.set_ylim(-0.5, k729 - 0.5)
        ax.set_aspect('equal')
    else:
        ax.text(0.5, 0.5, 'No k=729 transition data', transform=ax.transAxes,
                ha='center', va='center')

    # ── Panel (0,1): k=729 "11" successor analysis ────────────────────
    ax = axes[0, 1]
    if k729 in cells:
        cd = cells[k729]
        odd_mask = cd['odd'] > 0

        # For each odd-visited cell, classify successor (r2, (r3+1)%k)
        succ_type_map = np.full((k729, k729), '', dtype=object)
        odd_r2, odd_r3 = np.where(odd_mask)
        for r2i, r3i in zip(odd_r2, odd_r3):
            sr3 = (r3i + 1) % k729
            st = cd['cell_type'][r2i, sr3]
            succ_type_map[r2i, r3i] = st

        # Color by successor type
        colors_map = {'branch': 'gold', 'pure_even': 'steelblue',
                      'pure_odd': 'firebrick', 'empty': 'gray'}
        for stype, color in colors_map.items():
            mask_st = succ_type_map == stype
            if np.any(mask_st):
                sr2, sr3 = np.where(mask_st)
                ax.scatter(sr3, sr2, s=0.3, c=color, linewidths=0,
                           alpha=0.6, label=f'succ={stype} ({len(sr2)})')

        draw_foliation(ax, k729, INV_LOG2_3, 'red',
                       r'irrational ($\log_3 2$)', linestyle='--', alpha=0.4)
        draw_foliation(ax, k729, 460.0 / 729.0, 'lime',
                       r'rational (460/729)', linestyle=':', alpha=0.4)
        ax.legend(loc='upper right', fontsize=7, markerscale=10)
        ax.set_title(f'k = 729: "11" successor analysis\n'
                     f'Successor cell type after odd visit (no odd->odd)',
                     fontsize=11)
        ax.set_xlabel(r'$\nu_3$ mod 729')
        ax.set_ylabel(r'$\nu_2$ mod 729')
        ax.set_xlim(-0.5, k729 - 0.5)
        ax.set_ylim(-0.5, k729 - 0.5)
        ax.set_aspect('equal')
    else:
        ax.text(0.5, 0.5, 'No k=729 cell data', transform=ax.transAxes,
                ha='center', va='center')

    # ── Panel (0,2): Shadow offset spatial map (option 2) ─────────────
    ax = axes[0, 2]
    if k729 in shadow:
        sd = shadow[k729]
        branch = sd['cell_type'] == 'branch'

        if np.any(branch):
            br_r2, br_r3 = np.where(branch)
            so_br = sd['shadow_offset'][branch]

            # Diverging colormap centered at 0
            so_abs_max = np.percentile(np.abs(so_br), 99)
            norm_so = TwoSlopeNorm(vmin=-so_abs_max, vcenter=0,
                                   vmax=so_abs_max)
            sc = ax.scatter(br_r3, br_r2, c=so_br, cmap='RdBu_r',
                            norm=norm_so, s=0.3, linewidths=0, zorder=2)

            # Overlay both foliations
            draw_foliation(ax, k729, INV_LOG2_3, 'black',
                           r'irrational ($\log_3 2$)', linestyle='--',
                           alpha=0.3)
            draw_foliation(ax, k729, 460.0 / 729.0, 'lime',
                           r'rational (460/729)', linestyle=':',
                           alpha=0.3)

            cb = plt.colorbar(sc, ax=ax, label='shadow offset '
                              r'($d_{\rm irr} - d_{\rm rat}$)', shrink=0.8)

            n_pos = np.sum(so_br > 0)
            n_neg = np.sum(so_br < 0)
            ax.set_title(f'k = 729: shadow offset spatial map\n'
                         f'red: closer to rational | '
                         f'blue: closer to irrational\n'
                         f'(+{n_pos} / {"-"}{n_neg})',
                         fontsize=10)
        else:
            ax.text(0.5, 0.5, 'No branch cells', transform=ax.transAxes,
                    ha='center', va='center')

        ax.set_xlabel(r'$\nu_3$ mod 729')
        ax.set_ylabel(r'$\nu_2$ mod 729')
        ax.set_xlim(-0.5, k729 - 0.5)
        ax.set_ylim(-0.5, k729 - 0.5)
        ax.set_aspect('equal')
    else:
        ax.text(0.5, 0.5, 'No shadow data for k=729', transform=ax.transAxes,
                ha='center', va='center')

    # ── Panel (1,0): k=81 vs k=729 transition comparison ─────────────
    ax = axes[1, 0]
    compare_ks = [81, 729]
    bar_data = {}
    for ck in compare_ks:
        if ck in trans:
            td = trans[ck]
            total_t = td['ee'].sum() + td['eo'].sum() + td['oe'].sum()
            if total_t > 0:
                bar_data[ck] = {
                    'ee': td['ee'].sum() / total_t,
                    'eo': td['eo'].sum() / total_t,
                    'oe': td['oe'].sum() / total_t,
                }

    if bar_data:
        x_pos = np.arange(len(bar_data))
        width = 0.25
        ks_bar = sorted(bar_data.keys())

        ee_vals = [bar_data[k]['ee'] for k in ks_bar]
        eo_vals = [bar_data[k]['eo'] for k in ks_bar]
        oe_vals = [bar_data[k]['oe'] for k in ks_bar]

        ax.bar(x_pos - width, ee_vals, width, label='ee (even->even)',
               color='steelblue')
        ax.bar(x_pos, eo_vals, width, label='eo (even->odd)',
               color='firebrick')
        ax.bar(x_pos + width, oe_vals, width, label='oe (odd->even)',
               color='gold')

        ax.set_xticks(x_pos)
        ax.set_xticklabels([f'k={k}' for k in ks_bar])
        ax.set_ylabel('Fraction of all transitions')
        ax.set_title('Transition type fractions:\nsaturated (k=81) vs Diophantine (k=729)',
                     fontsize=11)
        ax.legend(fontsize=8)
        ax.grid(True, alpha=0.3, axis='y')

        # Add per-cell valence distribution as inset
        if 729 in trans:
            inax = ax.inset_axes([0.55, 0.5, 0.4, 0.4])
            v729 = trans[729]['valence']
            nonempty729 = cells[729]['total'] > 0 if 729 in cells else v729 > 0
            v_ne = v729[nonempty729]
            counts = [np.sum(v_ne == v) for v in range(4)]
            inax.bar(range(4), counts, color=['gray', 'skyblue', 'orange', 'red'],
                     edgecolor='black', linewidth=0.5)
            inax.set_xticks(range(4))
            inax.set_xticklabels(['0', '1', '2', '3'])
            inax.set_xlabel('Valence', fontsize=8)
            inax.set_ylabel('Cell count', fontsize=8)
            inax.set_title('k=729 valence dist.', fontsize=8)
    else:
        ax.text(0.5, 0.5, 'No transition data for comparison',
                transform=ax.transAxes, ha='center', va='center')

    # ── Panel (1,1): Shadow offset vs foliation position (option 3) ───
    ax = axes[1, 1]
    if k729 in shadow:
        sd = shadow[k729]
        branch = sd['cell_type'] == 'branch'

        if np.any(branch):
            br_r2, br_r3 = np.where(branch)
            so_br = sd['shadow_offset'][branch]
            p_br  = sd['p_odd'][branch]

            # Position along irrational foliation:
            # project (r2, r3) onto direction (1, s)/||(1,s)||
            s = INV_LOG2_3
            norm_fol = np.sqrt(1 + s**2)
            fol_pos = (br_r2 + s * br_r3) / norm_fol

            sc = ax.scatter(fol_pos, so_br, c=p_br, cmap='RdYlBu_r',
                            s=0.8, linewidths=0, alpha=0.7,
                            vmin=np.percentile(p_br, 5),
                            vmax=np.percentile(p_br, 95))
            plt.colorbar(sc, ax=ax, label=r'$p_{\rm odd}$', shrink=0.8)

            ax.axhline(0, color='black', linewidth=0.8, alpha=0.5)

            # Running mean to show trend
            sort_idx = np.argsort(fol_pos)
            fp_sorted = fol_pos[sort_idx]
            so_sorted = so_br[sort_idx]
            win = max(len(fp_sorted) // 50, 10)
            if len(fp_sorted) > win:
                so_smooth = np.convolve(so_sorted, np.ones(win)/win,
                                        mode='valid')
                fp_smooth = np.convolve(fp_sorted, np.ones(win)/win,
                                        mode='valid')
                ax.plot(fp_smooth, so_smooth, 'k-', linewidth=2, alpha=0.8,
                        label=f'running mean (w={win})')
                ax.legend(fontsize=8)

            # Annotate max shadow offset
            so_range = np.max(so_br) - np.min(so_br)
            ax.set_title(f'k = 729: shadow offset along foliation\n'
                         f'range = {so_range:.4f} cell units | '
                         f'max $\\Delta s \\cdot k / \\sqrt{{1+s^2}}$ = '
                         f'{7.16e-5 * 729 / norm_fol:.4f}',
                         fontsize=10)
            ax.set_xlabel(r'Position along foliation  '
                          r'$t = (\nu_2 + s\,\nu_3)/\sqrt{1+s^2}$')
            ax.set_ylabel(r'Shadow offset  '
                          r'$d_{\rm irr} - d_{\rm rat}$')
            ax.grid(True, alpha=0.3)
    else:
        ax.text(0.5, 0.5, 'No shadow data for k=729', transform=ax.transAxes,
                ha='center', va='center')

    # ── Panel (1,2): Shadow offset histogram + cross-section ──────────
    ax = axes[1, 2]
    if k729 in shadow:
        sd = shadow[k729]
        branch = sd['cell_type'] == 'branch'
        nonempty = sd['cell_type'] != 'empty'

        if np.any(branch):
            so_br = sd['shadow_offset'][branch]
            so_ne = sd['shadow_offset'][nonempty]

            bins = np.linspace(np.min(so_ne), np.max(so_ne), 80)
            ax.hist(so_ne, bins=bins, density=True, alpha=0.4, color='gray',
                    label=f'all non-empty ({np.sum(nonempty)})')
            ax.hist(so_br, bins=bins, density=True, alpha=0.7, color='gold',
                    label=f'branch ({np.sum(branch)})')
            ax.axvline(0, color='black', linewidth=1, linestyle='--',
                       alpha=0.7, label='zero offset')

            # Annotate statistics
            ax.axvline(np.mean(so_br), color='red', linewidth=1,
                       linestyle=':', alpha=0.8,
                       label=f'branch mean = {np.mean(so_br):.5f}')
            ax.axvline(np.median(so_br), color='blue', linewidth=1,
                       linestyle=':', alpha=0.8,
                       label=f'branch median = {np.median(so_br):.5f}')

            ax.set_xlabel(r'Shadow offset  $d_{\rm irr} - d_{\rm rat}$')
            ax.set_ylabel('Density')
            ax.set_title(f'k = 729: shadow offset distribution\n'
                         f'std = {np.std(so_br):.5f}',
                         fontsize=10)
            ax.legend(fontsize=7)
            ax.grid(True, alpha=0.3)
    else:
        ax.text(0.5, 0.5, 'No shadow data for k=729', transform=ax.transAxes,
                ha='center', va='center')

    fig.suptitle(f'Transition / Valence / SFT / Shadow Analysis — N = {N:.2e}',
                 fontsize=14, fontweight='bold', y=0.98)
    plt.savefig(os.path.join(output_dir, 'diophantine_transitions.png'),
                dpi=150, bbox_inches='tight')
    plt.close()
    print("  Saved diophantine_transitions.png")

print("\nDone. 5 figures saved.")
