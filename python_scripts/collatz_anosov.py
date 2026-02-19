#!/usr/bin/env python3
"""
Collatz–Anosov Structure Explorer
===================================
Visualizes the pseudo-Anosov structure of Collatz dynamics
in the (ν₂, ν₃) winding number plane.

1. Eigenbasis view: u (transverse to equilibrium) vs v (along equilibrium)
2. Step-size distribution and drift analysis
3. Foliation structure on finite tori
4. Running u(t) as a "first-passage" stochastic process
5. Syracuse map action on patches — stretching and folding
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import LogNorm, Normalize, LinearSegmentedColormap
from matplotlib.gridspec import GridSpec
from matplotlib.patches import FancyArrowPatch
import math, time
from collections import Counter, defaultdict

# ─── Core computation ─────────────────────────────────────────────────

LOG2_3 = math.log2(3)

def collatz_running(n):
    """Return (values, cum_ν₂, cum_ν₃) arrays for full trajectory."""
    vals, c2, c3 = [n], [0], [0]
    cur = n
    while cur != 1:
        if cur % 2 == 0:
            cur //= 2
            c2.append(c2[-1] + 1)
            c3.append(c3[-1])
        else:
            cur = 3 * cur + 1
            c2.append(c2[-1])
            c3.append(c3[-1] + 1)
        vals.append(cur)
    return np.array(vals), np.array(c2), np.array(c3)


def syracuse_steps(n):
    """For trajectory from n to 1, return list of Syracuse step sizes k_i.
    Each k_i = number of halvings after the i-th odd step."""
    steps = []
    cur = n
    while cur != 1:
        if cur % 2 == 0:
            cur //= 2
        else:
            cur = 3 * cur + 1
            k = 0
            while cur > 1 and cur % 2 == 0:
                cur //= 2
                k += 1
            steps.append(k)
    return steps


def collatz_stats(n):
    """Return (total_steps, ν₂, ν₃, max_value)."""
    cur, nu2, nu3, mx = n, 0, 0, n
    while cur != 1:
        if cur % 2 == 0:
            cur //= 2; nu2 += 1
        else:
            cur = 3 * cur + 1; nu3 += 1
            if cur > mx: mx = cur
    return nu2 + nu3, nu2, nu3, mx


# ─── Style ────────────────────────────────────────────────────────────
BG = '#08080f'
TXT = '#c8c8d8'
GRID_A = 0.12

def style_ax(ax, title, xlabel='', ylabel=''):
    ax.set_facecolor('#0e0e1a')
    ax.set_title(title, color=TXT, fontsize=12, fontweight='bold', pad=10)
    ax.set_xlabel(xlabel, color=TXT, fontsize=10)
    ax.set_ylabel(ylabel, color=TXT, fontsize=10)
    ax.tick_params(colors='#888898')
    for sp in ax.spines.values(): sp.set_color('#333348')
    ax.grid(True, alpha=GRID_A, color='#444466')


# ─── Compute bulk statistics ──────────────────────────────────────────
MAX_N = 1_000_000
print(f"Computing stats for n = 2..{MAX_N:,}...")
t0 = time.time()

ns = np.arange(2, MAX_N + 1, dtype=np.int64)
nu2_arr = np.zeros(len(ns), dtype=np.int32)
nu3_arr = np.zeros(len(ns), dtype=np.int32)
max_vals = np.zeros(len(ns), dtype=np.int64)

for i, n in enumerate(ns):
    _, n2, n3, mv = collatz_stats(int(n))
    nu2_arr[i] = n2
    nu3_arr[i] = n3
    max_vals[i] = mv

# Eigenbasis coordinates
u_arr = nu2_arr.astype(float) - LOG2_3 * nu3_arr.astype(float)
# v along equilibrium: project onto (1, log₂3) direction, normalized
norm_eq = math.sqrt(1 + LOG2_3**2)
v_arr = (nu2_arr.astype(float) + LOG2_3 * nu3_arr.astype(float)) / norm_eq

valid = nu3_arr > 0
print(f"  Done in {time.time()-t0:.1f}s")
print(f"  u range: [{u_arr[valid].min():.3f}, {u_arr[valid].max():.3f}]")
print(f"  u mean:  {u_arr[valid].mean():.4f}")
print(f"  All u > 0? {np.all(u_arr[valid] > 0)}")

# ─── Compute Syracuse step sizes for sample ───────────────────────────
print("Computing Syracuse step distributions...")
all_k_steps = []
np.random.seed(42)
sample_for_k = np.random.choice(ns, size=min(200000, len(ns)), replace=False)
for n in sample_for_k:
    all_k_steps.extend(syracuse_steps(int(n)))
all_k_steps = np.array(all_k_steps)
print(f"  {len(all_k_steps):,} Syracuse steps collected")
print(f"  Mean k = {all_k_steps.mean():.4f}  (heuristic prediction: 2.0)")


# ═════════════════════════════════════════════════════════════════════
# FIGURE 1: Eigenbasis view — the Anosov coordinates
# ═════════════════════════════════════════════════════════════════════
print("\nRendering Figure 1: Eigenbasis (u, v) view...")

fig = plt.figure(figsize=(26, 20), facecolor=BG)
gs = GridSpec(3, 3, figure=fig, hspace=0.32, wspace=0.30,
              left=0.06, right=0.97, top=0.94, bottom=0.05)

# ── Panel 1: u vs v density (the Anosov phase portrait) ──────────────
ax1 = fig.add_subplot(gs[0, 0])
style_ax(ax1, 'Anosov Eigenbasis: u (transverse) vs v (along equil.)',
         'v  (along equilibrium)', 'u  (transverse displacement)')

h1, xe1, ye1 = np.histogram2d(
    v_arr[valid], u_arr[valid],
    bins=[400, 400],
    range=[[0, np.percentile(v_arr[valid], 99.5)],
           [u_arr[valid].min() - 0.5,
            np.percentile(u_arr[valid], 99.5)]])

ax1.pcolormesh(xe1, ye1, h1.T, cmap='inferno',
               norm=LogNorm(vmin=1, vmax=h1.max()), rasterized=True)
ax1.axhline(0, color='#00ff88', ls='--', lw=1.5, alpha=0.6,
            label='u = 0 (equilibrium)')
ax1.legend(fontsize=8, facecolor='#1a1a2e', edgecolor='#333348',
           labelcolor=TXT)


# ── Panel 2: Syracuse step size k distribution ────────────────────────
ax2 = fig.add_subplot(gs[0, 1])
style_ax(ax2, 'Syracuse Step Size Distribution P(k)',
         'k  (halvings per odd step)', 'Frequency')

k_counts = Counter(all_k_steps)
k_vals = sorted(k_counts.keys())
k_freqs = np.array([k_counts[k] for k in k_vals], dtype=float)
k_freqs /= k_freqs.sum()

ax2.bar(k_vals, k_freqs, color='#e85d75', alpha=0.85, width=0.8)

# Overlay theoretical 2^{-k} prediction
k_theory = np.arange(1, max(k_vals) + 1)
p_theory = 2.0**(-k_theory)
p_theory /= p_theory.sum()
ax2.plot(k_theory, p_theory, 'o-', color='#00ff88', ms=5, lw=1.5,
         alpha=0.8, label='P(k) = 2⁻ᵏ (normalized)')

# Mark the critical step size k* = log₂3
ax2.axvline(LOG2_3, color='#ffaa00', ls=':', lw=2, alpha=0.7,
            label=f'k* = log₂3 ≈ {LOG2_3:.3f}')
ax2.annotate('k < k*: contraction\n(u decreases)',
             xy=(1, k_freqs[0] * 0.6), fontsize=8, color='#ff6666',
             ha='center')
ax2.annotate('k > k*: expansion\n(u increases)',
             xy=(3, k_freqs[2] * 1.3), fontsize=8, color='#66ff66',
             ha='center')
ax2.set_xlim(0.5, 15.5)
ax2.set_yscale('log')
ax2.legend(fontsize=8, facecolor='#1a1a2e', edgecolor='#333348',
           labelcolor=TXT)


# ── Panel 3: u-drift per Syracuse step ────────────────────────────────
ax3 = fig.add_subplot(gs[0, 2])
style_ax(ax3, 'Drift in u per Syracuse Step: Δu = k − log₂3',
         'Δu = k − log₂3', 'Frequency')

du_steps = all_k_steps.astype(float) - LOG2_3
ax3.hist(du_steps, bins=np.arange(-1.5, 15, 1) - 0.5 + (1 - LOG2_3),
         color='#7b68ee', alpha=0.85, edgecolor='none', density=True)
ax3.axvline(0, color='#ff4444', ls='-', lw=2, alpha=0.8,
            label='Δu = 0 (neutral)')
mean_du = du_steps.mean()
ax3.axvline(mean_du, color='#00ff88', ls='--', lw=1.5, alpha=0.8,
            label=f'⟨Δu⟩ = {mean_du:.3f}')
ax3.legend(fontsize=8, facecolor='#1a1a2e', edgecolor='#333348',
           labelcolor=TXT)


# ── Panel 4: Running u(t) for selected trajectories ──────────────────
ax4 = fig.add_subplot(gs[1, 0])
style_ax(ax4, 'Running u(t) Along Trajectory (First-Passage Process)',
         'Step t', 'u(t) = ν₂(t) − log₂3 · ν₃(t)')

sample_ns = [27, 97, 871, 6171, 77031, 837799, 447, 1023]
cmap_lines = plt.cm.plasma(np.linspace(0.1, 0.9, len(sample_ns)))

for j, sn in enumerate(sample_ns):
    _, c2, c3 = collatz_running(sn)
    u_t = c2.astype(float) - LOG2_3 * c3.astype(float)
    steps_t = np.arange(len(u_t))
    ax4.plot(steps_t, u_t, color=cmap_lines[j], lw=0.8, alpha=0.85,
             label=f'n={sn:,}')

ax4.axhline(0, color='#ff4444', ls='-', lw=1.5, alpha=0.6,
            label='u = 0')
ax4.legend(fontsize=7, facecolor='#1a1a2e', edgecolor='#333348',
           labelcolor=TXT, ncol=2, loc='upper left')


# ── Panel 5: u(t) as stochastic process — many faint trajectories ────
ax5 = fig.add_subplot(gs[1, 1])
style_ax(ax5, 'u(t) Ensemble (2000 Random Trajectories)',
         'Step t', 'u(t)')

np.random.seed(123)
bg_ns = np.random.choice(ns[valid], size=2000, replace=False)
for sn in bg_ns:
    _, c2, c3 = collatz_running(int(sn))
    u_t = c2.astype(float) - LOG2_3 * c3.astype(float)
    ax5.plot(np.arange(len(u_t)), u_t,
             color='#6644cc', lw=0.15, alpha=0.08)

# Overlay a few highlighted
for j, sn in enumerate([27, 837799, 6171]):
    _, c2, c3 = collatz_running(sn)
    u_t = c2.astype(float) - LOG2_3 * c3.astype(float)
    ax5.plot(np.arange(len(u_t)), u_t,
             color=['#ff6688', '#ffaa00', '#00ddff'][j],
             lw=1.2, alpha=0.9, label=f'n={sn:,}')

ax5.axhline(0, color='#ff4444', ls='-', lw=1.5, alpha=0.5)
ax5.legend(fontsize=8, facecolor='#1a1a2e', edgecolor='#333348',
           labelcolor=TXT)


# ── Panel 6: Final u vs log₂(n) — testing the identity ───────────────
ax6 = fig.add_subplot(gs[1, 2])
style_ax(ax6, 'Final u = ν₂ − log₂3 · ν₃  vs  log₂(n)',
         'log₂(n)', 'u_final')

log2_n = np.log2(ns[valid].astype(float))

h6, xe6, ye6 = np.histogram2d(
    log2_n, u_arr[valid],
    bins=[300, 300],
    range=[[1, 20],
           [0, np.percentile(u_arr[valid], 99.5)]])

ax6.pcolormesh(xe6, ye6, h6.T, cmap='inferno',
               norm=LogNorm(vmin=1, vmax=h6.max()), rasterized=True)

# Overlay identity line u = log₂(n)  (the leading term)
x_line = np.linspace(1, 20, 100)
ax6.plot(x_line, x_line, '--', color='#00ff88', lw=1.5, alpha=0.7,
         label='u = log₂(n)')
ax6.legend(fontsize=8, facecolor='#1a1a2e', edgecolor='#333348',
           labelcolor=TXT)


# ── Panel 7: Foliation on mod-k torus with eigenvectors ──────────────
ax7 = fig.add_subplot(gs[2, 0])
style_ax(ax7, 'Foliation Structure on T² (mod 12)',
         'ν₂ mod 12', 'ν₃ mod 12')

k = 12
nu2_mod = nu2_arr[valid] % k
nu3_mod = nu3_arr[valid] % k
h7, _, _ = np.histogram2d(nu2_mod, nu3_mod,
                           bins=[k, k],
                           range=[[-0.5, k-0.5], [-0.5, k-0.5]])

ax7.imshow(h7.T, origin='lower', cmap='inferno',
           norm=LogNorm(vmin=max(1, h7[h7>0].min()), vmax=h7.max()),
           extent=[-0.5, k-0.5, -0.5, k-0.5],
           aspect='equal', interpolation='nearest')

# Overlay foliation directions
# Unstable: slope log₂3 ≈ 1.585 in (ν₂, ν₃) plane
# Stable: slope -1/log₂3 ≈ -0.631
for offset in range(-k, 2*k, 2):
    # Unstable foliation leaves
    x_fol = np.linspace(-0.5, k-0.5, 100)
    y_fol = LOG2_3 * (x_fol - offset)
    mask = (y_fol >= -0.5) & (y_fol <= k-0.5)
    ax7.plot(x_fol[mask], y_fol[mask], '-', color='#00ff88',
             lw=0.6, alpha=0.3)
    # Stable foliation leaves
    y_fol2 = -1/LOG2_3 * (x_fol - offset)
    mask2 = (y_fol2 >= -0.5) & (y_fol2 <= k-0.5)
    ax7.plot(x_fol[mask2], y_fol2[mask2], '-', color='#ff4444',
             lw=0.6, alpha=0.3)


# ── Panel 8: Stretching visualization — how Syracuse acts on patches ──
ax8 = fig.add_subplot(gs[2, 1])
style_ax(ax8, 'Syracuse Action on (ν₂, ν₃) Patches',
         'ν₃', 'ν₂')

# Show how a "square" of starting numbers maps forward under Syracuse
# Pick numbers in a narrow ν₃ band and show their next Syracuse step
patch_nu3_target = 30  # focus on trajectories that have ν₃ ≈ 30
patch_width = 3

# Find all n where ν₃ is in our target range
mask_patch = (nu3_arr >= patch_nu3_target - patch_width) & \
             (nu3_arr <= patch_nu3_target + patch_width) & valid

if np.sum(mask_patch) > 0:
    p_nu2 = nu2_arr[mask_patch]
    p_nu3 = nu3_arr[mask_patch]

    ax8.scatter(p_nu3, p_nu2, c='#6644cc', s=1, alpha=0.3, rasterized=True)

    # Overlay the equilibrium line
    nu3_range = np.array([p_nu3.min() - 2, p_nu3.max() + 2])
    ax8.plot(nu3_range, LOG2_3 * nu3_range, '--', color='#00ff88',
             lw=1.5, alpha=0.7)

    # Show Syracuse step vectors for a subsample
    sub_idx = np.where(mask_patch)[0]
    np.random.seed(42)
    if len(sub_idx) > 500:
        sub_idx = np.random.choice(sub_idx, 500, replace=False)

    for idx in sub_idx:
        n = int(ns[idx])
        k_steps = syracuse_steps(n)
        if len(k_steps) > 0:
            # The "next" Syracuse step from end of trajectory
            # Actually, let's show the step AT ν₃ ≈ 30 in the trajectory
            _, c2, c3 = collatz_running(n)
            # Find the Syracuse step near our target ν₃
            for t in range(len(c3) - 1):
                if c3[t] == patch_nu3_target and c3[t+1] > c3[t]:
                    # This is an odd step; count halvings after it
                    k = 0
                    tt = t + 1
                    while tt < len(c3) - 1 and c3[tt+1] == c3[tt]:
                        k += 1
                        tt += 1
                    if k > 0:
                        ax8.annotate('', xy=(c3[tt], c2[tt]),
                                     xytext=(c3[t], c2[t]),
                                     arrowprops=dict(arrowstyle='->', lw=0.3,
                                                     color='#ff8844',
                                                     alpha=0.15))
                    break

    ax8.set_xlim(patch_nu3_target - patch_width - 2,
                 patch_nu3_target + patch_width + 8)
    ax8.set_ylim(int(LOG2_3 * (patch_nu3_target - patch_width)) - 5,
                 int(LOG2_3 * (patch_nu3_target + patch_width)) + 15)


# ── Panel 9: Mapping torus cross-section ──────────────────────────────
# Show u(t) mod 2π as an angular coordinate — literal winding on S¹
ax9 = fig.add_subplot(gs[2, 2], polar=True)
ax9.set_facecolor('#0e0e1a')
ax9.set_title('u(t) mod 2π — Winding on S¹\n(selected trajectories)',
              color=TXT, fontsize=11, fontweight='bold', pad=15)

for j, sn in enumerate([27, 871, 6171, 77031, 837799]):
    _, c2, c3 = collatz_running(sn)
    u_t = c2.astype(float) - LOG2_3 * c3.astype(float)
    theta_t = (u_t * 2 * np.pi / u_t[-1]) % (2 * np.pi)  # normalize to [0, 2π]
    r_t = np.arange(len(u_t)) / len(u_t)  # time as radius

    color = plt.cm.plasma(j / 5)
    ax9.plot(theta_t, r_t, color=color, lw=0.5, alpha=0.7,
             label=f'n={sn:,}')

ax9.set_rmax(1.0)
ax9.tick_params(colors='#666688')
ax9.legend(fontsize=7, facecolor='#1a1a2e', edgecolor='#333348',
           labelcolor=TXT, loc='lower right',
           bbox_to_anchor=(1.3, 0))


# ── Supertitle ────────────────────────────────────────────────────────
fig.suptitle('Collatz–Anosov Structure: Eigenbasis, Drift, and Foliation',
             color='#e0e0f0', fontsize=18, fontweight='bold', y=0.975)

outpath = '/home/claude/collatz_anosov_structure.png'
fig.savefig(outpath, dpi=180, facecolor=BG, bbox_inches='tight')
plt.close()
print(f"\nSaved: {outpath}")


# ═════════════════════════════════════════════════════════════════════
# FIGURE 2: The u(t) first-passage problem in detail
# ═════════════════════════════════════════════════════════════════════
print("\nRendering Figure 2: First-passage and excursion analysis...")

fig2 = plt.figure(figsize=(22, 12), facecolor=BG)
gs2 = GridSpec(2, 3, figure=fig2, hspace=0.30, wspace=0.28,
               left=0.06, right=0.97, top=0.93, bottom=0.06)

# ── Panel A: Distribution of min(u(t)) over trajectory ────────────────
ax_a = fig2.add_subplot(gs2[0, 0])
style_ax(ax_a, 'Distribution of min u(t) Along Trajectory',
         'min u(t)', 'Count')

min_u_per_n = np.zeros(len(ns))
for i, n in enumerate(ns[:200000]):  # first 200K for speed
    _, c2, c3 = collatz_running(int(n))
    u_t = c2.astype(float) - LOG2_3 * c3.astype(float)
    min_u_per_n[i] = u_t.min()

ax_a.hist(min_u_per_n[:200000], bins=300, color='#e85d75', alpha=0.85,
          edgecolor='none')
ax_a.axvline(0, color='#ff4444', ls='-', lw=2, alpha=0.8,
             label='u = 0')
n_negative = np.sum(min_u_per_n[:200000] < 0)
ax_a.annotate(f'{n_negative:,} trajectories\ndip below u=0',
              xy=(min_u_per_n[:200000].min() * 0.5, 1),
              fontsize=10, color='#ffaa44', ha='center')
ax_a.legend(fontsize=9, facecolor='#1a1a2e', edgecolor='#333348',
            labelcolor=TXT)


# ── Panel B: Time spent below u=0 vs total time ──────────────────────
ax_b = fig2.add_subplot(gs2[0, 1])
style_ax(ax_b, 'Fraction of Trajectory Below Equilibrium',
         'Total stopping time', 'Fraction with u(t) < 0')

frac_below = np.zeros(200000)
total_st = np.zeros(200000, dtype=int)
for i, n in enumerate(ns[:200000]):
    _, c2, c3 = collatz_running(int(n))
    u_t = c2.astype(float) - LOG2_3 * c3.astype(float)
    total_st[i] = len(u_t) - 1
    if len(u_t) > 1:
        frac_below[i] = np.sum(u_t < 0) / len(u_t)

h_b, xe_b, ye_b = np.histogram2d(
    total_st, frac_below,
    bins=[200, 200],
    range=[[0, np.percentile(total_st, 99)], [0, 1]])

ax_b.pcolormesh(xe_b, ye_b, h_b.T, cmap='inferno',
                norm=LogNorm(vmin=1, vmax=h_b.max()), rasterized=True)


# ── Panel C: u at the moment ν₃ first reaches j, for each j ──────────
ax_c = fig2.add_subplot(gs2[0, 2])
style_ax(ax_c, 'u Value When ν₃ First Reaches j (Stopping Boundary)',
         'j (odd-step count)', 'u at ν₃ = j')

# For a selection of trajectories, track u at each Syracuse step
np.random.seed(77)
sample_c = np.random.choice(ns[nu3_arr > 30], size=5000, replace=False)

for sn in sample_c:
    _, c2, c3 = collatz_running(int(sn))
    u_t = c2.astype(float) - LOG2_3 * c3.astype(float)
    # Extract u at each new odd step (when ν₃ increments)
    syr_u = []
    syr_j = []
    for t in range(1, len(c3)):
        if c3[t] > c3[t-1]:
            syr_j.append(c3[t])
            syr_u.append(u_t[t])
    if syr_j:
        ax_c.plot(syr_j, syr_u, color='#6644cc', lw=0.1, alpha=0.03)

# Overlay a few highlighted
for sn, col in [(837799, '#ffaa00'), (6171, '#00ddff'), (27, '#ff6688')]:
    _, c2, c3 = collatz_running(sn)
    u_t = c2.astype(float) - LOG2_3 * c3.astype(float)
    syr_u, syr_j = [], []
    for t in range(1, len(c3)):
        if c3[t] > c3[t-1]:
            syr_j.append(c3[t])
            syr_u.append(u_t[t])
    if syr_j:
        ax_c.plot(syr_j, syr_u, color=col, lw=1.2, alpha=0.9,
                  label=f'n={sn:,}')

ax_c.axhline(0, color='#ff4444', ls='-', lw=1.5, alpha=0.5)
ax_c.legend(fontsize=8, facecolor='#1a1a2e', edgecolor='#333348',
            labelcolor=TXT)


# ── Panel D: Autocorrelation of Syracuse steps ────────────────────────
ax_d = fig2.add_subplot(gs2[1, 0])
style_ax(ax_d, 'Autocorrelation of Syracuse Step Sizes k_i',
         'Lag', 'Autocorrelation')

# Compute autocorrelation for a long trajectory
long_n = 837799
k_long = np.array(syracuse_steps(long_n), dtype=float)
k_centered = k_long - k_long.mean()
n_k = len(k_centered)
max_lag = min(80, n_k // 2)
autocorr = np.zeros(max_lag)
var_k = np.var(k_centered)
if var_k > 0:
    for lag in range(max_lag):
        autocorr[lag] = np.mean(k_centered[:n_k-lag] * k_centered[lag:]) / var_k

ax_d.bar(range(max_lag), autocorr, color='#7b68ee', alpha=0.85, width=0.8)
ax_d.axhline(0, color='#888888', lw=1)
# 95% CI for white noise
ci = 1.96 / math.sqrt(n_k)
ax_d.axhline(ci, color='#ffaa00', ls=':', lw=1, alpha=0.7, label='95% CI (white noise)')
ax_d.axhline(-ci, color='#ffaa00', ls=':', lw=1, alpha=0.7)
ax_d.set_xlim(-0.5, max_lag - 0.5)
ax_d.legend(fontsize=8, facecolor='#1a1a2e', edgecolor='#333348',
            labelcolor=TXT)
ax_d.set_title(f'Autocorrelation of k_i  (n={long_n:,}, {n_k} steps)',
               color=TXT, fontsize=12, fontweight='bold', pad=10)


# ── Panel E: Joint distribution (k_i, k_{i+1}) ──────────────────────
ax_e = fig2.add_subplot(gs2[1, 1])
style_ax(ax_e, 'Joint Distribution P(k_i, k_{i+1})',
         'k_i', 'k_{i+1}')

# Collect consecutive Syracuse step pairs from many trajectories
pairs_k = []
np.random.seed(99)
for sn in np.random.choice(ns, 50000, replace=False):
    ks = syracuse_steps(int(sn))
    for j in range(len(ks) - 1):
        pairs_k.append((ks[j], ks[j+1]))

if pairs_k:
    pk = np.array(pairs_k)
    max_k_plot = 12
    h_e, xe_e, ye_e = np.histogram2d(
        pk[:, 0], pk[:, 1],
        bins=[max_k_plot, max_k_plot],
        range=[[0.5, max_k_plot + 0.5], [0.5, max_k_plot + 0.5]])

    ax_e.imshow(h_e.T, origin='lower', cmap='inferno',
                norm=LogNorm(vmin=1, vmax=h_e.max()),
                extent=[0.5, max_k_plot + 0.5, 0.5, max_k_plot + 0.5],
                aspect='equal', interpolation='nearest')

    # If independent, the joint should be product of marginals
    ax_e.set_xticks(range(1, max_k_plot + 1))
    ax_e.set_yticks(range(1, max_k_plot + 1))


# ── Panel F: Winding number w(n) = floor(u_final / (2-log₂3)) ───────
ax_f = fig2.add_subplot(gs2[1, 2])
style_ax(ax_f, 'Winding Number w(n) = ⌊u_final / Δu_mean⌋  vs  n',
         'Starting number n', 'w(n)')

# Winding number: how many "average Syracuse steps" fit in the 
# transverse displacement
mean_du = 2.0 - LOG2_3  # mean transverse drift per Syracuse step
w_arr = np.floor(u_arr[valid] / mean_du).astype(int)

step = max(1, np.sum(valid) // 50000)
idx_sub = np.where(valid)[0][::step]

sc_f = ax_f.scatter(ns[idx_sub], w_arr[idx_sub // 1 if step == 1 else
                     np.searchsorted(np.where(valid)[0], idx_sub)],
                    c=nu3_arr[idx_sub], cmap='viridis',
                    s=0.3, alpha=0.4, rasterized=True,
                    norm=Normalize(vmin=0, vmax=np.percentile(nu3_arr[valid], 99)))
cb_f = fig2.colorbar(sc_f, ax=ax_f, shrink=0.8, pad=0.02)
cb_f.set_label('ν₃', color=TXT, fontsize=9)
cb_f.ax.tick_params(colors='#888898')


fig2.suptitle('Collatz–Anosov: First-Passage Structure and Step Correlations',
              color='#e0e0f0', fontsize=17, fontweight='bold', y=0.98)

outpath2 = '/home/claude/collatz_first_passage.png'
fig2.savefig(outpath2, dpi=180, facecolor=BG, bbox_inches='tight')
plt.close()
print(f"Saved: {outpath2}")

print("\nDone.")
