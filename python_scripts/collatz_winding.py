#!/usr/bin/env python3
"""
Collatz Winding Number Explorer
================================
Explores the ν₂/ν₃ equilibrium ratio and its deviations
as a topological invariant of Collatz trajectories.

Each trajectory has ν₂ even steps and ν₃ odd steps.
The ratio ρ = ν₂/ν₃ → log₂(3) ≈ 1.585 for "typical" trajectories.
Deviations from this equilibrium encode dynamically meaningful structure.
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import LogNorm, Normalize
from matplotlib.gridspec import GridSpec
import math, time

# ─── Core computation ─────────────────────────────────────────────────

def collatz_stats(n):
    """Return (total_steps, ν₂, ν₃, max_value) for trajectory from n to 1."""
    cur = n
    nu2, nu3 = 0, 0
    max_val = n
    while cur != 1:
        if cur % 2 == 0:
            cur //= 2
            nu2 += 1
        else:
            cur = 3 * cur + 1
            nu3 += 1
            if cur > max_val:
                max_val = cur
    return nu2 + nu3, nu2, nu3, max_val


def collatz_running(n):
    """Return arrays: (values, cumulative_ν₂, cumulative_ν₃) at each step."""
    vals = [n]
    c_nu2 = [0]
    c_nu3 = [0]
    cur = n
    while cur != 1:
        if cur % 2 == 0:
            cur //= 2
            c_nu2.append(c_nu2[-1] + 1)
            c_nu3.append(c_nu3[-1])
        else:
            cur = 3 * cur + 1
            c_nu2.append(c_nu2[-1])
            c_nu3.append(c_nu3[-1] + 1)
        vals.append(cur)
    return np.array(vals), np.array(c_nu2), np.array(c_nu3)


# ─── Constants ────────────────────────────────────────────────────────
LOG2_3 = math.log2(3)  # 1.58496...
MAX_N = 1_000_000

print(f"Computing trajectory statistics for n = 2..{MAX_N:,}...")
t0 = time.time()

ns = np.arange(2, MAX_N + 1, dtype=np.int64)
total_steps = np.zeros(len(ns), dtype=np.int32)
nu2_arr = np.zeros(len(ns), dtype=np.int32)
nu3_arr = np.zeros(len(ns), dtype=np.int32)
max_vals = np.zeros(len(ns), dtype=np.int64)

for i, n in enumerate(ns):
    ts, n2, n3, mv = collatz_stats(int(n))
    total_steps[i] = ts
    nu2_arr[i] = n2
    nu3_arr[i] = n3
    max_vals[i] = mv

# Ratio ρ = ν₂/ν₃
with np.errstate(divide='ignore', invalid='ignore'):
    rho = np.where(nu3_arr > 0, nu2_arr / nu3_arr, np.nan)
    delta = rho - LOG2_3

valid = np.isfinite(rho) & (nu3_arr > 0)

elapsed = time.time() - t0
print(f"  Done in {elapsed:.1f}s")
print(f"  ρ range: [{rho[valid].min():.4f}, {rho[valid].max():.4f}]")
print(f"  ρ mean:  {rho[valid].mean():.6f}  (log₂3 = {LOG2_3:.6f})")
print(f"  ρ std:   {rho[valid].std():.6f}")

# ─── Identify outliers ───────────────────────────────────────────────
abs_delta = np.abs(delta)
abs_delta_valid = np.where(valid, abs_delta, 0)
top_outliers_idx = np.argsort(abs_delta_valid)[-20:][::-1]

print("\n  Top deviators from equilibrium:")
for idx in top_outliers_idx[:10]:
    n = ns[idx]
    print(f"    n={n:>10,}  ν₂={nu2_arr[idx]:>4}  ν₃={nu3_arr[idx]:>4}  "
          f"ρ={rho[idx]:.4f}  δ={delta[idx]:+.4f}  "
          f"steps={total_steps[idx]}  max={max_vals[idx]:,}")


# ═════════════════════════════════════════════════════════════════════
# FIGURE 1: Six-panel overview
# ═════════════════════════════════════════════════════════════════════
print("\nRendering Figure 1: Six-panel overview...")

BG = '#08080f'
TXT = '#c8c8d8'
GRID_A = 0.15

fig = plt.figure(figsize=(26, 18), facecolor=BG)
gs = GridSpec(2, 3, figure=fig, hspace=0.30, wspace=0.28,
              left=0.055, right=0.97, top=0.93, bottom=0.06)

def style_ax(ax, title, xlabel='', ylabel=''):
    ax.set_facecolor('#0e0e1a')
    ax.set_title(title, color=TXT, fontsize=13, fontweight='bold', pad=10)
    ax.set_xlabel(xlabel, color=TXT, fontsize=10)
    ax.set_ylabel(ylabel, color=TXT, fontsize=10)
    ax.tick_params(colors='#888898')
    for sp in ax.spines.values():
        sp.set_color('#333348')
    ax.grid(True, alpha=GRID_A, color='#444466')


# ── Panel 1: (ν₂, ν₃) lattice scatter ────────────────────────────────
ax1 = fig.add_subplot(gs[0, 0])
style_ax(ax1, '(ν₂, ν₃) Lattice — Winding Number Pairs',
         'ν₃  (odd steps)', 'ν₂  (even steps)')

# 2D histogram for density
h, xedges, yedges = np.histogram2d(
    nu3_arr[valid], nu2_arr[valid],
    bins=[200, 200],
    range=[[0, nu3_arr.max()], [0, nu2_arr.max()]])

ax1.pcolormesh(xedges, yedges, h.T,
               cmap='inferno', norm=LogNorm(vmin=1, vmax=h.max()),
               rasterized=True)

# Equilibrium line: ν₂ = log₂(3) * ν₃
nu3_line = np.array([0, nu3_arr.max()])
ax1.plot(nu3_line, LOG2_3 * nu3_line, '--', color='#00ff88', lw=1.5,
         alpha=0.8, label=f'ν₂ = log₂3 · ν₃')
ax1.legend(fontsize=9, facecolor='#1a1a2e', edgecolor='#333348',
           labelcolor=TXT)


# ── Panel 2: Running ratio ρ(t) for selected trajectories ────────────
ax2 = fig.add_subplot(gs[0, 1])
style_ax(ax2, 'Running Ratio ρ(t) = ν₂(t)/ν₃(t) Along Trajectory',
         'Step t', 'ρ(t)')

# Curated selection: short, medium, long, record-holder, powers of 2
sample_ns = [27, 97, 871, 6171, 77031, 837799, 7, 1023]
cmap_lines = plt.cm.plasma(np.linspace(0.1, 0.9, len(sample_ns)))

for j, sn in enumerate(sample_ns):
    vals, c2, c3 = collatz_running(sn)
    # Running ratio (skip first few steps where ν₃ might be 0)
    mask = c3 > 0
    steps = np.arange(len(vals))
    running_rho = np.full(len(vals), np.nan)
    running_rho[mask] = c2[mask] / c3[mask]

    ax2.plot(steps[mask], running_rho[mask],
             color=cmap_lines[j], lw=0.8, alpha=0.85,
             label=f'n={sn:,}')

ax2.axhline(LOG2_3, color='#00ff88', ls='--', lw=1.2, alpha=0.7,
            label=f'log₂3 ≈ {LOG2_3:.3f}')
ax2.set_ylim(0.5, 3.5)
ax2.legend(fontsize=7, facecolor='#1a1a2e', edgecolor='#333348',
           labelcolor=TXT, ncol=2, loc='upper right')


# ── Panel 3: Deviation δ(n) vs n ─────────────────────────────────────
ax3 = fig.add_subplot(gs[0, 2])
style_ax(ax3, 'Deviation δ = ρ − log₂3  vs  Starting Number',
         'Starting number n', 'δ(n)')

# Subsample for rendering
step = max(1, len(ns) // 80000)
idx_sub = np.arange(0, len(ns), step)
idx_sub = idx_sub[valid[idx_sub]]

sc3 = ax3.scatter(ns[idx_sub], delta[idx_sub],
                  c=total_steps[idx_sub], cmap='magma',
                  s=0.15, alpha=0.4, rasterized=True,
                  norm=Normalize(vmin=0, vmax=np.percentile(total_steps, 99)))
ax3.axhline(0, color='#00ff88', ls='--', lw=1, alpha=0.6)
cb3 = fig.colorbar(sc3, ax=ax3, shrink=0.8, pad=0.02)
cb3.set_label('Total stopping time', color=TXT, fontsize=9)
cb3.ax.tick_params(colors='#888898')


# ── Panel 4: δ vs Stopping Time ──────────────────────────────────────
ax4 = fig.add_subplot(gs[1, 0])
style_ax(ax4, 'Deviation δ  vs  Total Stopping Time',
         'Total stopping time', 'δ(n)')

h4, xe4, ye4 = np.histogram2d(
    total_steps[valid], delta[valid],
    bins=[300, 300],
    range=[[0, np.percentile(total_steps, 99.5)],
           [np.percentile(delta[valid], 0.5),
            np.percentile(delta[valid], 99.5)]])

ax4.pcolormesh(xe4, ye4, h4.T, cmap='inferno',
               norm=LogNorm(vmin=1, vmax=h4.max()),
               rasterized=True)
ax4.axhline(0, color='#00ff88', ls='--', lw=1, alpha=0.6)


# ── Panel 5: Histogram of ρ ──────────────────────────────────────────
ax5 = fig.add_subplot(gs[1, 1])
style_ax(ax5, 'Distribution of ρ = ν₂/ν₃', 'ρ', 'Count')

rho_valid = rho[valid]
# Clip extreme tails for visibility
clip_lo, clip_hi = np.percentile(rho_valid, [0.1, 99.9])
rho_clipped = rho_valid[(rho_valid >= clip_lo) & (rho_valid <= clip_hi)]

ax5.hist(rho_clipped, bins=500, color='#e85d75', alpha=0.85,
         edgecolor='none', density=True)
ax5.axvline(LOG2_3, color='#00ff88', ls='--', lw=2, alpha=0.8,
            label=f'log₂3 = {LOG2_3:.4f}')
ax5.axvline(rho_valid.mean(), color='#ffaa00', ls=':', lw=1.5, alpha=0.8,
            label=f'mean = {rho_valid.mean():.4f}')
ax5.legend(fontsize=9, facecolor='#1a1a2e', edgecolor='#333348',
           labelcolor=TXT)


# ── Panel 6: δ vs log(max excursion) ─────────────────────────────────
ax6 = fig.add_subplot(gs[1, 2])
style_ax(ax6, 'Deviation δ  vs  Peak Altitude log₁₀(max)',
         'log₁₀(peak value)', 'δ(n)')

log_max = np.log10(max_vals[valid].astype(float) + 1)
h6, xe6, ye6 = np.histogram2d(
    log_max, delta[valid],
    bins=[300, 300],
    range=[[np.log10(2), np.percentile(log_max, 99.5)],
           [np.percentile(delta[valid], 0.5),
            np.percentile(delta[valid], 99.5)]])

ax6.pcolormesh(xe6, ye6, h6.T, cmap='inferno',
               norm=LogNorm(vmin=1, vmax=h6.max()),
               rasterized=True)
ax6.axhline(0, color='#00ff88', ls='--', lw=1, alpha=0.6)


# ── Supertitle ────────────────────────────────────────────────────────
fig.suptitle('Collatz Winding Numbers: The ν₂/ν₃ Equilibrium Structure',
             color='#e0e0f0', fontsize=18, fontweight='bold', y=0.975)

outpath = '/home/claude/collatz_winding_overview.png'
fig.savefig(outpath, dpi=180, facecolor=BG, bbox_inches='tight')
plt.close()
print(f"  Saved: {outpath}")


# ═════════════════════════════════════════════════════════════════════
# FIGURE 2: T² torus projection — (ν₂ mod k, ν₃ mod k) structure
# ═════════════════════════════════════════════════════════════════════
print("\nRendering Figure 2: Torus residue structure...")

fig2, axes2 = plt.subplots(2, 4, figsize=(26, 13), facecolor=BG)

moduli = [3, 5, 7, 8, 10, 12, 16, 24]

for i, k in enumerate(moduli):
    ax = axes2[i // 4, i % 4]
    style_ax(ax, f'mod {k}',
             f'ν₂ mod {k}' if i >= 4 else '',
             f'ν₃ mod {k}' if i % 4 == 0 else '')

    nu2_mod = nu2_arr[valid] % k
    nu3_mod = nu3_arr[valid] % k

    # 2D histogram on the discrete torus Z/kZ × Z/kZ
    h, _, _ = np.histogram2d(nu2_mod, nu3_mod,
                              bins=[k, k],
                              range=[[-0.5, k-0.5], [-0.5, k-0.5]])

    im = ax.imshow(h.T, origin='lower', cmap='inferno',
                   norm=LogNorm(vmin=max(1, h[h>0].min()), vmax=h.max()),
                   extent=[-0.5, k-0.5, -0.5, k-0.5],
                   aspect='equal', interpolation='nearest')

    # Mark the equilibrium residue class
    # If log₂3 ≈ p/q, then ν₂ ≈ (p/q)ν₃, so ν₂·q ≈ ν₃·p mod k
    ax.set_xticks(range(0, k, max(1, k//6)))
    ax.set_yticks(range(0, k, max(1, k//6)))

fig2.suptitle('Torus Residue Structure: (ν₂ mod k, ν₃ mod k)  on  ℤ/kℤ × ℤ/kℤ',
              color='#e0e0f0', fontsize=16, fontweight='bold', y=0.98)
fig2.tight_layout(rect=[0, 0, 1, 0.95])

outpath2 = '/home/claude/collatz_torus_residues.png'
fig2.savefig(outpath2, dpi=180, facecolor=BG, bbox_inches='tight')
plt.close()
print(f"  Saved: {outpath2}")


# ═════════════════════════════════════════════════════════════════════
# FIGURE 3: Trajectory paths on the (ν₂, ν₃) plane
# Shows how individual trajectories walk through the lattice
# ═════════════════════════════════════════════════════════════════════
print("\nRendering Figure 3: Trajectory walks on (ν₂, ν₃) plane...")

fig3, ax3m = plt.subplots(1, 1, figsize=(16, 14), facecolor=BG)
style_ax(ax3m, 'Trajectory Walks on the (ν₂, ν₃) Lattice Plane',
         'ν₃ (odd steps)', 'ν₂ (even steps)')

# Draw many faint trajectories + a few highlighted ones
np.random.seed(42)
bg_samples = np.random.choice(ns[valid], size=2000, replace=False)

for sn in bg_samples:
    _, c2, c3 = collatz_running(int(sn))
    ax3m.plot(c3, c2, color='#4444aa', lw=0.1, alpha=0.08)

# Highlighted trajectories
highlight_ns = [27, 97, 871, 6171, 77031, 837799, 1023, 255, 447]
highlight_colors = plt.cm.plasma(np.linspace(0.15, 0.95, len(highlight_ns)))

for j, sn in enumerate(highlight_ns):
    _, c2, c3 = collatz_running(sn)
    ax3m.plot(c3, c2, color=highlight_colors[j], lw=1.2, alpha=0.9,
              label=f'n={sn:,}', zorder=10)
    # Mark start
    ax3m.plot(c3[0], c2[0], 'o', color=highlight_colors[j],
              ms=4, zorder=11)
    # Mark end
    ax3m.plot(c3[-1], c2[-1], 's', color=highlight_colors[j],
              ms=5, zorder=11)

# Equilibrium line
max_nu3_plot = max(nu3_arr[valid].max(), 200)
eq_line = np.array([0, max_nu3_plot])
ax3m.plot(eq_line, LOG2_3 * eq_line, '--', color='#00ff88', lw=2,
          alpha=0.7, label=f'ρ = log₂3', zorder=5)

# Boundary lines: ρ = 1 and ρ = 2 for reference
ax3m.plot(eq_line, 1.0 * eq_line, ':', color='#ff4444', lw=1,
          alpha=0.4, label='ρ = 1')
ax3m.plot(eq_line, 2.0 * eq_line, ':', color='#4444ff', lw=1,
          alpha=0.4, label='ρ = 2')

ax3m.legend(fontsize=9, facecolor='#1a1a2e', edgecolor='#333348',
            labelcolor=TXT, loc='upper left', ncol=2)
ax3m.set_aspect('equal')

outpath3 = '/home/claude/collatz_lattice_walks.png'
fig3.savefig(outpath3, dpi=180, facecolor=BG, bbox_inches='tight')
plt.close()
print(f"  Saved: {outpath3}")


# ═════════════════════════════════════════════════════════════════════
# FIGURE 4: The "winding spectrum" — δ stratified by ν₃
# For each value of ν₃, what is the distribution of δ?
# This reveals whether there are forbidden/preferred winding ratios.
# ═════════════════════════════════════════════════════════════════════
print("\nRendering Figure 4: Winding spectrum (δ stratified by ν₃)...")

fig4, ax4m = plt.subplots(1, 1, figsize=(20, 10), facecolor=BG)
style_ax(ax4m, 'Winding Spectrum: δ Stratified by ν₃',
         'ν₃ (number of odd steps)', 'δ = ρ − log₂3')

# For each ν₃ value, scatter δ values
h4s, xe4s, ye4s = np.histogram2d(
    nu3_arr[valid].astype(float),
    delta[valid],
    bins=[int(nu3_arr[valid].max()) + 1, 400],
    range=[[0, nu3_arr[valid].max() + 1],
           [np.percentile(delta[valid], 0.2),
            np.percentile(delta[valid], 99.8)]])

ax4m.pcolormesh(xe4s, ye4s, h4s.T, cmap='inferno',
                norm=LogNorm(vmin=1, vmax=h4s.max()),
                rasterized=True)
ax4m.axhline(0, color='#00ff88', ls='--', lw=1.5, alpha=0.7)

# Annotate: for small ν₃, δ takes only discrete values
# because ν₂/ν₃ for small ν₃ is highly quantized
ax4m.annotate('Quantized regime\n(small ν₃ → discrete ρ)',
              xy=(8, 0.3), fontsize=10, color='#ffaa44',
              ha='center', fontstyle='italic',
              arrowprops=dict(arrowstyle='->', color='#ffaa44'),
              xytext=(25, 0.5))

outpath4 = '/home/claude/collatz_winding_spectrum.png'
fig4.savefig(outpath4, dpi=180, facecolor=BG, bbox_inches='tight')
plt.close()
print(f"  Saved: {outpath4}")

print("\nDone. All figures saved.")
