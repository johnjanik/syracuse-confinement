#!/usr/bin/env python3
"""
6-Adic Ordering Experiment: Testing Odometer Conjugacy
=======================================================

Conjecture (Notes II, Conj. 8.5): There exists a measurable map φ
conjugating the Collatz-induced map F on ℤ₂ × ℤ₃ to a skew product
over the 6-adic odometer τ(x) = x + 1.

TEST: If this holds, the profinite winding number ŵ(n) should be
approximately "locally constant" on 6-adic balls. That is, numbers
n, n' with n ≡ n' (mod 6^m) should have similar winding numbers
(ν₂ mod K, ν₃ mod K) for appropriate K.

PROCEDURE:
1. Compute (ν₂(n), ν₃(n)) for n ∈ [2, 10⁶].
2. Sort n by 6-adic expansion (base-6 digits, least significant first).
3. Plot ŵ(n) along the 6-adic ordering → expect step-function blocks.
4. Quantify: within-ball variance vs between-ball variance (ANOVA).
5. Control: compare 6-adic balls to 5-adic and 7-adic balls (primes
   not involved in Collatz should show no special structure).

Ref: Notes II §10 step 3, Conjecture 8.5
"""

import numpy as np
import time
import sys
from collections import defaultdict

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import Normalize
from matplotlib.gridspec import GridSpec

# ── Parameters ──────────────────────────────────────────────────────
N = 1_000_000

# ── Step 1: Compute winding pairs ───────────────────────────────────
print(f"Computing winding pairs for n ∈ [2, {N}]...")
t0 = time.time()

nu2 = np.zeros(N + 1, dtype=np.int32)
nu3 = np.zeros(N + 1, dtype=np.int32)

for n in range(2, N + 1):
    x = n
    e, o = 0, 0
    while x != 1:
        if x & 1 == 0:
            x >>= 1
            e += 1
        else:
            x = 3 * x + 1
            o += 1
    nu2[n] = e
    nu3[n] = o

t1 = time.time()
print(f"  Done in {t1 - t0:.1f}s.")

# Working arrays: indices 2..N
idx = np.arange(2, N + 1)
v2 = nu2[2:N+1]
v3 = nu3[2:N+1]

# ── Step 2: 6-adic ordering ─────────────────────────────────────────
print("Computing 6-adic ordering...")

def adic_sort_key(n, base, max_digits=10):
    """Return tuple of base-`base` digits, least significant first."""
    digits = []
    x = n
    for _ in range(max_digits):
        digits.append(x % base)
        x //= base
    return tuple(digits)

# For efficiency, compute sort keys as integers with reversed digits
# giving a lexicographic ordering equivalent to 6-adic ordering.
def adic_sort_value(n, base, max_digits=10):
    """Map n to an integer whose natural ordering = base-adic ordering of n."""
    val = 0
    x = n
    for i in range(max_digits):
        val += (x % base) * (base ** (max_digits - 1 - i))
        x //= base
    return val

t2 = time.time()
# Vectorised: compute 6-adic sort keys for all n in [2, N]
max_d = 8  # 6^8 = 1,679,616 > 10^6
sort_keys_6 = np.zeros(len(idx), dtype=np.int64)
temp = idx.copy()
for i in range(max_d):
    sort_keys_6 += (temp % 6).astype(np.int64) * (6 ** (max_d - 1 - i))
    temp //= 6

order_6 = np.argsort(sort_keys_6)
t3 = time.time()
print(f"  6-adic sort: {t3 - t2:.2f}s")

# Also compute 5-adic and 7-adic orderings as controls
sort_keys_5 = np.zeros(len(idx), dtype=np.int64)
temp = idx.copy()
max_d5 = 9  # 5^9 = 1,953,125 > 10^6
for i in range(max_d5):
    sort_keys_5 += (temp % 5).astype(np.int64) * (5 ** (max_d5 - 1 - i))
    temp //= 5
order_5 = np.argsort(sort_keys_5)

sort_keys_7 = np.zeros(len(idx), dtype=np.int64)
temp = idx.copy()
max_d7 = 8  # 7^8 = 5,764,801 > 10^6
for i in range(max_d7):
    sort_keys_7 += (temp % 7).astype(np.int64) * (7 ** (max_d7 - 1 - i))
    temp //= 7
order_7 = np.argsort(sort_keys_7)

# Natural ordering (control)
order_nat = np.arange(len(idx))

t4 = time.time()
print(f"  All orderings computed: {t4 - t2:.2f}s")

# ── Step 3: Local constancy test (ANOVA-style) ─────────────────────
print("\n" + "="*72)
print("LOCAL CONSTANCY TEST ON p-ADIC BALLS")
print("="*72)
print()
print("For base b and level m, partition [2,N] into residue classes mod b^m.")
print("Compute within-class variance of (ν₂ mod K, ν₃ mod K).")
print("Compare ratio: Var_within / Var_total.  Lower = more locally constant.")
print()

def local_constancy_test(values, labels, base, max_level):
    """
    Test local constancy of `values` on `base`-adic balls.

    values: array of shape (n,) — the observable to test
    labels: array of shape (n,) — the n values (integers 2..N)
    base: the p-adic base
    max_level: test mod base^1 through base^max_level

    Returns list of (level, n_balls, var_within/var_total, ball_size).
    """
    total_var = np.var(values)
    if total_var == 0:
        return [(m, 0, 0.0, 0) for m in range(1, max_level + 1)]

    results = []
    for m in range(1, max_level + 1):
        modulus = base ** m
        if modulus > N:
            break

        residues = labels % modulus
        unique_res = np.unique(residues)
        n_balls = len(unique_res)

        # Within-group variance (pooled)
        ss_within = 0.0
        n_total = 0
        for r in unique_res:
            mask = (residues == r)
            grp = values[mask]
            if len(grp) > 1:
                ss_within += np.var(grp) * len(grp)
                n_total += len(grp)

        var_within = ss_within / n_total if n_total > 0 else 0
        ratio = var_within / total_var
        ball_size = N // modulus

        results.append((m, n_balls, ratio, ball_size))
    return results

# Test multiple observables
observables = {
    'ν₂ mod 6':  v2 % 6,
    'ν₃ mod 6':  v3 % 6,
    'ν₂ mod 12': v2 % 12,
    'ν₃ mod 9':  v3 % 9,
    'ν₂ mod 24': v2 % 24,
    'ν₃ mod 27': v3 % 27,
    'ν₂ (raw)':  v2,
    'ν₃ (raw)':  v3,
}

bases = [6, 5, 7, 10]
base_names = {6: '6-adic', 5: '5-adic (control)', 7: '7-adic (control)',
              10: 'decimal (control)'}

# Store all results for plotting
all_results = {}

for obs_name, obs_vals in observables.items():
    print(f"\nObservable: {obs_name}")
    print(f"  {'base':>6s}  {'level':>5s}  {'mod':>8s}  {'balls':>7s}  "
          f"{'ball_sz':>7s}  {'Vw/Vt':>8s}  {'1-Vw/Vt':>8s}")
    print(f"  {'─'*60}")

    for base in bases:
        max_lev = 8 if base == 6 else 7
        results = local_constancy_test(obs_vals, idx, base, max_lev)
        key = (obs_name, base)
        all_results[key] = results

        for m, n_balls, ratio, ball_sz in results:
            reduction = 1 - ratio
            marker = "  ◄" if base == 6 and reduction > 0.05 else ""
            print(f"  {base:>6d}  {m:>5d}  {base**m:>8d}  {n_balls:>7d}  "
                  f"{ball_sz:>7d}  {ratio:>8.5f}  {reduction:>8.5f}{marker}")

# ── Step 4: Quantitative summary ────────────────────────────────────
print(f"\n{'='*72}")
print("QUANTITATIVE SUMMARY: 6-ADIC vs CONTROLS")
print(f"{'='*72}")
print()
print("Variance reduction (1 - Vw/Vt) at each level for key observables:")
print("Higher = more locally constant on p-adic balls.\n")

key_obs = ['ν₂ mod 12', 'ν₃ mod 9', 'ν₂ (raw)', 'ν₃ (raw)']
for obs_name in key_obs:
    print(f"  {obs_name}:")
    print(f"    {'level':>5s}", end="")
    for base in bases:
        print(f"  {base_names[base]:>18s}", end="")
    print()

    # Find common levels (by ball size, approximately)
    r6 = all_results.get((obs_name, 6), [])
    for m6, _, ratio6, bs6 in r6:
        print(f"    6^{m6:<2d} ", end="")
        print(f"  {1-ratio6:>18.5f}", end="")
        # For controls, find level with closest ball size
        for base in bases[1:]:
            rp = all_results.get((obs_name, base), [])
            # Find level m such that base^m ≈ 6^m6
            target = 6**m6
            best = None
            for mp, _, ratiop, bsp in rp:
                if best is None or abs(base**mp - target) < abs(base**best[0] - target):
                    best = (mp, ratiop)
            if best:
                print(f"  {1-best[1]:>18.5f}", end="")
            else:
                print(f"  {'—':>18s}", end="")
        print()
    print()

# ── Step 5: Visualisations ──────────────────────────────────────────
print(f"\n{'='*72}")
print("GENERATING VISUALISATIONS")
print(f"{'='*72}")

# ─── Figure 1: ŵ(n) along 6-adic ordering (main result) ───
fig = plt.figure(figsize=(18, 16))
gs = GridSpec(4, 2, figure=fig, hspace=0.35, wspace=0.25)

# Panel (a): ν₂ mod 12 along 6-adic order
ax = fig.add_subplot(gs[0, 0])
y_vals = (v2 % 12)[order_6]
# Subsample for plotting
step = max(1, len(y_vals) // 20000)
xs = np.arange(0, len(y_vals), step)
ax.scatter(xs, y_vals[::step], s=0.1, alpha=0.3, c='steelblue', rasterized=True)
ax.set_xlabel('6-adic index')
ax.set_ylabel('ν₂ mod 12')
ax.set_title('(a) ν₂ mod 12,  6-adic ordering')

# Panel (b): ν₃ mod 9 along 6-adic order
ax = fig.add_subplot(gs[0, 1])
y_vals = (v3 % 9)[order_6]
ax.scatter(xs, y_vals[::step], s=0.1, alpha=0.3, c='coral', rasterized=True)
ax.set_xlabel('6-adic index')
ax.set_ylabel('ν₃ mod 9')
ax.set_title('(b) ν₃ mod 9,  6-adic ordering')

# Panel (c): same as (a) but natural ordering (control)
ax = fig.add_subplot(gs[1, 0])
y_vals_nat = (v2 % 12)[order_nat]
ax.scatter(xs, y_vals_nat[::step], s=0.1, alpha=0.3, c='steelblue', rasterized=True)
ax.set_xlabel('natural index (n)')
ax.set_ylabel('ν₂ mod 12')
ax.set_title('(c) ν₂ mod 12,  natural ordering (control)')

# Panel (d): same as (b) but 7-adic ordering (control)
ax = fig.add_subplot(gs[1, 1])
y_vals_7 = (v3 % 9)[order_7]
ax.scatter(xs, y_vals_7[::step], s=0.1, alpha=0.3, c='coral', rasterized=True)
ax.set_xlabel('7-adic index')
ax.set_ylabel('ν₃ mod 9')
ax.set_title('(d) ν₃ mod 9,  7-adic ordering (control)')

# Panel (e): Zoom into first 6^4 = 1296 elements under 6-adic order
ax = fig.add_subplot(gs[2, 0])
zoom_n = 6**4  # 1296
idx_zoom = order_6[:zoom_n]
v2_zoom = v2[idx_zoom]
v3_zoom = v3[idx_zoom]
x_zoom = np.arange(zoom_n)

# Color by ν₂ mod 3
colors_mod3 = v2_zoom % 3
cmap = plt.cm.Set1
ax.scatter(x_zoom, v2_zoom % 12, s=2, c=colors_mod3, cmap='Set1',
           alpha=0.6, rasterized=True)
ax.set_xlabel('6-adic index (first 1296)')
ax.set_ylabel('ν₂ mod 12')
ax.set_title('(e) Zoom: first 6⁴ elements,  colored by ν₂ mod 3')

# Add vertical lines at 6-adic ball boundaries
for m in range(1, 5):
    step_m = 6**m
    for j in range(0, zoom_n, step_m):
        ax.axvline(x=j, color='gray', alpha=0.15 * m, linewidth=0.5)

# Panel (f): Zoom ν₃ mod 9
ax = fig.add_subplot(gs[2, 1])
colors_mod3_v3 = v3_zoom % 3
ax.scatter(x_zoom, v3_zoom % 9, s=2, c=colors_mod3_v3, cmap='Set1',
           alpha=0.6, rasterized=True)
ax.set_xlabel('6-adic index (first 1296)')
ax.set_ylabel('ν₃ mod 9')
ax.set_title('(f) Zoom: first 6⁴ elements,  colored by ν₃ mod 3')
for m in range(1, 5):
    step_m = 6**m
    for j in range(0, zoom_n, step_m):
        ax.axvline(x=j, color='gray', alpha=0.15 * m, linewidth=0.5)

# Panel (g): Variance reduction comparison across bases
ax = fig.add_subplot(gs[3, 0])
obs_plot = 'ν₂ mod 12'
for base in bases:
    results = all_results.get((obs_plot, base), [])
    if not results:
        continue
    levels = [r[0] for r in results]
    reductions = [1 - r[2] for r in results]
    label = base_names[base]
    marker = 'o-' if base == 6 else 's--'
    lw = 2.0 if base == 6 else 1.0
    ax.plot(levels, reductions, marker, label=label, linewidth=lw, markersize=4)
ax.set_xlabel('Level m  (ball = residue class mod b^m)')
ax.set_ylabel('Variance reduction  (1 − V_within/V_total)')
ax.set_title(f'(g) Local constancy: {obs_plot}')
ax.legend(fontsize=8)
ax.set_ylim(-0.01, None)
ax.grid(True, alpha=0.3)

# Panel (h): Same for ν₃ mod 9
ax = fig.add_subplot(gs[3, 1])
obs_plot = 'ν₃ mod 9'
for base in bases:
    results = all_results.get((obs_plot, base), [])
    if not results:
        continue
    levels = [r[0] for r in results]
    reductions = [1 - r[2] for r in results]
    label = base_names[base]
    marker = 'o-' if base == 6 else 's--'
    lw = 2.0 if base == 6 else 1.0
    ax.plot(levels, reductions, marker, label=label, linewidth=lw, markersize=4)
ax.set_xlabel('Level m  (ball = residue class mod b^m)')
ax.set_ylabel('Variance reduction  (1 − V_within/V_total)')
ax.set_title(f'(h) Local constancy: {obs_plot}')
ax.legend(fontsize=8)
ax.set_ylim(-0.01, None)
ax.grid(True, alpha=0.3)

fig.suptitle('6-Adic Ordering Experiment: Testing Odometer Conjugacy\n'
             f'N = {N:,}  |  Ref: Notes II, Conjecture 8.5', fontsize=14, y=0.995)
fig.savefig('/home/claude/sixadic_ordering.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved sixadic_ordering.png")

# ─── Figure 2: Heatmap of mean ŵ within 6-adic balls ───
print("  Computing ball-level heatmaps...")

fig, axes = plt.subplots(2, 3, figsize=(18, 11))

for col, (m, ball_mod) in enumerate([(1, 6), (2, 36), (3, 216)]):
    # For each residue class r mod ball_mod, compute mean ν₂ and mean ν₃
    mean_v2 = np.zeros(ball_mod)
    mean_v3 = np.zeros(ball_mod)
    counts = np.zeros(ball_mod)

    residues = idx % ball_mod
    for r in range(ball_mod):
        mask = (residues == r)
        if mask.sum() > 0:
            mean_v2[r] = v2[mask].mean()
            mean_v3[r] = v3[mask].mean()
            counts[r] = mask.sum()

    # Reshape into 2D grid: (6-adic digit decomposition)
    # For m=1: just 6 values
    # For m=2: 6×6 grid (digit_0 × digit_1)
    # For m=3: show as 6×36 or 36×6

    ax_v2 = axes[0, col]
    ax_v3 = axes[1, col]

    if m == 1:
        ax_v2.bar(range(ball_mod), mean_v2, color='steelblue')
        ax_v2.set_xlabel('n mod 6')
        ax_v2.set_ylabel('Mean ν₂')
        ax_v2.set_title(f'Mean ν₂ by residue mod 6')

        ax_v3.bar(range(ball_mod), mean_v3, color='coral')
        ax_v3.set_xlabel('n mod 6')
        ax_v3.set_ylabel('Mean ν₃')
        ax_v3.set_title(f'Mean ν₃ by residue mod 6')

    elif m == 2:
        # 6×6 grid: r = d0 + 6*d1, so d0 = r%6, d1 = r//6
        grid_v2 = mean_v2.reshape(6, 6)  # (d1, d0)
        grid_v3 = mean_v3.reshape(6, 6)

        im = ax_v2.imshow(grid_v2.T, origin='lower', aspect='equal', cmap='viridis')
        ax_v2.set_xlabel('digit₀ (n mod 6)')
        ax_v2.set_ylabel('digit₁ ((n//6) mod 6)')
        ax_v2.set_title(f'Mean ν₂ by residue mod 36')
        plt.colorbar(im, ax=ax_v2, shrink=0.8)

        im = ax_v3.imshow(grid_v3.T, origin='lower', aspect='equal', cmap='magma')
        ax_v3.set_xlabel('digit₀ (n mod 6)')
        ax_v3.set_ylabel('digit₁ ((n//6) mod 6)')
        ax_v3.set_title(f'Mean ν₃ by residue mod 36')
        plt.colorbar(im, ax=ax_v3, shrink=0.8)

    else:  # m == 3
        # 36×6 grid: r = d0 + 6*d1 + 36*d2
        grid_v2 = mean_v2.reshape(6, 6, 6)  # (d2, d1, d0)
        # Show as 36×6: flatten (d2,d1) along x, d0 along ... actually
        # better: show d0 along x (6 cols), (d1 + 6*d2) along y (36 rows)
        flat_v2 = mean_v2.reshape(36, 6)  # (d2*6+d1, d0)
        flat_v3 = mean_v3.reshape(36, 6)

        im = ax_v2.imshow(flat_v2, origin='lower', aspect='auto', cmap='viridis')
        ax_v2.set_xlabel('digit₀ (n mod 6)')
        ax_v2.set_ylabel('6·digit₂ + digit₁')
        ax_v2.set_title(f'Mean ν₂ by residue mod 216')
        plt.colorbar(im, ax=ax_v2, shrink=0.8)

        im = ax_v3.imshow(flat_v3, origin='lower', aspect='auto', cmap='magma')
        ax_v3.set_xlabel('digit₀ (n mod 6)')
        ax_v3.set_ylabel('6·digit₂ + digit₁')
        ax_v3.set_title(f'Mean ν₃ by residue mod 216')
        plt.colorbar(im, ax=ax_v3, shrink=0.8)

fig.suptitle('Mean Winding Numbers Within 6-Adic Balls at Levels 1–3\n'
             'Coherent block structure = evidence for odometer conjugacy',
             fontsize=13)
fig.tight_layout(rect=[0, 0, 1, 0.94])
fig.savefig('/home/claude/sixadic_ball_means.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved sixadic_ball_means.png")

# ─── Figure 3: Conditional distributions within 6-adic balls ───
print("  Computing conditional distributions...")

fig, axes = plt.subplots(2, 6, figsize=(20, 7))

for r in range(6):
    mask = (idx % 6 == r)
    v2_r = v2[mask]
    v3_r = v3[mask]

    ax = axes[0, r]
    ax.hist(v2_r % 12, bins=np.arange(-0.5, 12.5, 1), density=True,
            color='steelblue', alpha=0.7, edgecolor='black', linewidth=0.5)
    ax.set_title(f'n ≡ {r} (mod 6)', fontsize=10)
    ax.set_xlabel('ν₂ mod 12')
    if r == 0:
        ax.set_ylabel('Density')

    ax = axes[1, r]
    ax.hist(v3_r % 9, bins=np.arange(-0.5, 9.5, 1), density=True,
            color='coral', alpha=0.7, edgecolor='black', linewidth=0.5)
    ax.set_xlabel('ν₃ mod 9')
    if r == 0:
        ax.set_ylabel('Density')

fig.suptitle('Conditional Distributions of ŵ(n) Within 6-Adic Balls (Level 1)\n'
             'Different shapes per ball = non-trivial fiber structure',
             fontsize=12)
fig.tight_layout(rect=[0, 0, 1, 0.92])
fig.savefig('/home/claude/sixadic_conditionals.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved sixadic_conditionals.png")

# ─── Figure 4: 2D scatter of (ν₂ mod K, ν₃ mod K) colored by 6-adic digit ───
fig, axes = plt.subplots(1, 3, figsize=(18, 5.5))

# (a) Colored by n mod 6 (first 6-adic digit)
ax = axes[0]
colors = idx % 6
subsample = np.random.RandomState(42).choice(len(idx), size=50000, replace=False)
sc = ax.scatter((v2 % 12)[subsample], (v3 % 9)[subsample],
                c=colors[subsample], cmap='tab10', s=1, alpha=0.4, vmin=0, vmax=5,
                rasterized=True)
ax.set_xlabel('ν₂ mod 12')
ax.set_ylabel('ν₃ mod 9')
ax.set_title('(a) Colored by n mod 6  (1st 6-adic digit)')
plt.colorbar(sc, ax=ax, ticks=range(6), label='n mod 6')

# (b) Colored by n mod 36 (first two 6-adic digits)
ax = axes[1]
colors36 = idx % 36
sc = ax.scatter((v2 % 12)[subsample], (v3 % 9)[subsample],
                c=colors36[subsample], cmap='nipy_spectral', s=1, alpha=0.4,
                rasterized=True)
ax.set_xlabel('ν₂ mod 12')
ax.set_ylabel('ν₃ mod 9')
ax.set_title('(b) Colored by n mod 36  (first two 6-adic digits)')
plt.colorbar(sc, ax=ax, label='n mod 36')

# (c) Colored by n mod 7 (control: 7-adic digit should show no structure)
ax = axes[2]
colors7 = idx % 7
sc = ax.scatter((v2 % 12)[subsample], (v3 % 9)[subsample],
                c=colors7[subsample], cmap='tab10', s=1, alpha=0.4, vmin=0, vmax=6,
                rasterized=True)
ax.set_xlabel('ν₂ mod 12')
ax.set_ylabel('ν₃ mod 9')
ax.set_title('(c) Colored by n mod 7  (control: no Collatz structure)')
plt.colorbar(sc, ax=ax, ticks=range(7), label='n mod 7')

fig.suptitle('Winding Number Residues Colored by p-Adic Digits\n'
             'Clustering by 6-adic digit = odometer structure',
             fontsize=12)
fig.tight_layout(rect=[0, 0, 1, 0.91])
fig.savefig('/home/claude/sixadic_scatter_colored.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved sixadic_scatter_colored.png")

# ─── Figure 5: The decisive test — mutual information ───
print("  Computing mutual information...")

def mutual_information(x, y, bins_x=None, bins_y=None):
    """Compute I(X;Y) in bits."""
    if bins_x is None:
        bins_x = np.arange(x.min() - 0.5, x.max() + 1.5, 1)
    if bins_y is None:
        bins_y = np.arange(y.min() - 0.5, y.max() + 1.5, 1)

    pxy, _, _ = np.histogram2d(x, y, bins=[bins_x, bins_y])
    pxy = pxy / pxy.sum()
    px = pxy.sum(axis=1)
    py = pxy.sum(axis=0)

    # I(X;Y) = Σ p(x,y) log(p(x,y) / (p(x)p(y)))
    mi = 0.0
    for i in range(len(px)):
        for j in range(len(py)):
            if pxy[i, j] > 0 and px[i] > 0 and py[j] > 0:
                mi += pxy[i, j] * np.log2(pxy[i, j] / (px[i] * py[j]))
    return mi

# Compute I(n mod b^m ; ν₂ mod K) and I(n mod b^m ; ν₃ mod K) for various b, m
fig, axes = plt.subplots(1, 2, figsize=(14, 5.5))

for ax_idx, (obs_name, obs_vals, K) in enumerate([
    ('ν₂ mod 12', v2 % 12, 12),
    ('ν₃ mod 9', v3 % 9, 9)
]):
    ax = axes[ax_idx]
    bins_y = np.arange(-0.5, K + 0.5, 1)

    for base in [6, 2, 3, 5, 7]:
        mis = []
        levels = []
        for m in range(1, 8):
            modulus = base ** m
            if modulus > N // 10:
                break
            x = idx % modulus
            bins_x = np.arange(-0.5, modulus + 0.5, 1)
            mi = mutual_information(x, obs_vals, bins_x, bins_y)
            # Normalise by entropy of x (= log2(modulus) if uniform)
            h_x = np.log2(modulus)
            mis.append(mi)
            levels.append(m)

        style = 'o-' if base == 6 else ('s-' if base in [2, 3] else 'x--')
        lw = 2.5 if base == 6 else (1.5 if base in [2, 3] else 1.0)
        name = {6: '6-adic', 2: '2-adic', 3: '3-adic',
                5: '5-adic (ctrl)', 7: '7-adic (ctrl)'}[base]
        ax.plot(levels, mis, style, label=name, linewidth=lw, markersize=5)

    ax.set_xlabel('Level m')
    ax.set_ylabel('I(n mod b^m ; observable)  [bits]')
    ax.set_title(f'Mutual Information with {obs_name}')
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

fig.suptitle('Mutual Information: p-Adic Digit Structure vs Winding Numbers\n'
             '6-adic should dominate 5-adic and 7-adic if odometer structure exists',
             fontsize=12)
fig.tight_layout(rect=[0, 0, 1, 0.90])
fig.savefig('/home/claude/sixadic_mutual_info.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved sixadic_mutual_info.png")

# ── Copy to outputs ─────────────────────────────────────────────────
import shutil
for f in ['sixadic_ordering.png', 'sixadic_ball_means.png',
          'sixadic_conditionals.png', 'sixadic_scatter_colored.png',
          'sixadic_mutual_info.png']:
    shutil.copy2(f'/home/claude/{f}', f'/mnt/user-data/outputs/{f}')

shutil.copy2('/home/claude/sixadic_ordering.py', '/mnt/user-data/outputs/sixadic_ordering.py')

print(f"\nAll outputs saved.")
