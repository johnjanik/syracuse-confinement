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

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
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
v2 = nu2[2:N+1].copy()
v3 = nu3[2:N+1].copy()
L = len(idx)

# ── Step 2: p-adic orderings ──────────────────────────────────────
print("Computing p-adic orderings...")
t2 = time.time()

def adic_sort_keys(arr, base, max_digits):
    """Vectorised: map each n to an int whose natural order = base-adic order."""
    keys = np.zeros(len(arr), dtype=np.int64)
    temp = arr.copy()
    for i in range(max_digits):
        keys += (temp % base).astype(np.int64) * (base ** (max_digits - 1 - i))
        temp //= base
    return keys

order_6 = np.argsort(adic_sort_keys(idx, 6, 8))   # 6^8 > 10^6
order_5 = np.argsort(adic_sort_keys(idx, 5, 9))   # 5^9 > 10^6
order_7 = np.argsort(adic_sort_keys(idx, 7, 8))   # 7^8 > 10^6
order_nat = np.arange(L)

t3 = time.time()
print(f"  Done in {t3 - t2:.1f}s.")

# ── Step 3: Local constancy test (vectorised ANOVA) ───────────────
print(f"\n{'='*72}")
print("LOCAL CONSTANCY TEST ON p-ADIC BALLS")
print(f"{'='*72}\n")
print("For base b and level m, partition [2,N] into residue classes mod b^m.")
print("Compute within-class variance of observable. Compare Var_within / Var_total.")
print("Lower ratio = more locally constant.  Higher (1-ratio) = more structure.\n")

def variance_reduction(values, labels, base, max_level, N_bound):
    """
    Vectorised ANOVA: within-group variance / total variance.

    Uses the identity: SS_within = SS_total - SS_between
      SS_between = Σ_g n_g (mean_g - grand_mean)^2
    computed via np.bincount.
    """
    total_var = np.var(values, dtype=np.float64)
    if total_var == 0:
        return [(m, 0, 0.0, 0) for m in range(1, max_level + 1)]

    grand_mean = np.mean(values, dtype=np.float64)
    n_total = len(values)
    results = []

    for m in range(1, max_level + 1):
        modulus = base ** m
        if modulus > N_bound:
            break

        residues = labels % modulus
        counts = np.bincount(residues, minlength=modulus)
        sums = np.bincount(residues, weights=values.astype(np.float64),
                           minlength=modulus)

        active = counts > 0
        means = np.zeros(modulus, dtype=np.float64)
        means[active] = sums[active] / counts[active]

        ss_between = np.sum(counts[active] * (means[active] - grand_mean)**2)
        ss_total = total_var * n_total
        ss_within = ss_total - ss_between

        var_within = ss_within / n_total
        ratio = var_within / total_var

        n_balls = int(np.sum(active))
        ball_sz = N_bound // modulus
        results.append((m, n_balls, ratio, ball_sz))

    return results


observables = {
    'ν₂ mod 6':  v2 % 6,
    'ν₃ mod 6':  v3 % 6,
    'ν₂ mod 12': v2 % 12,
    'ν₃ mod 9':  v3 % 9,
    'ν₂ mod 24': v2 % 24,
    'ν₃ mod 27': v3 % 27,
    'ν₂ (raw)':  v2.astype(np.float64),
    'ν₃ (raw)':  v3.astype(np.float64),
}

bases = [6, 5, 7, 10]
base_names = {6: '6-adic', 5: '5-adic (control)', 7: '7-adic (control)',
              10: 'decimal (control)'}

all_results = {}

for obs_name, obs_vals in observables.items():
    print(f"Observable: {obs_name}")
    print(f"  {'base':>6s}  {'level':>5s}  {'mod':>8s}  {'balls':>7s}  "
          f"{'ball_sz':>7s}  {'Vw/Vt':>8s}  {'1-Vw/Vt':>8s}")
    print(f"  {'─'*60}")

    for base in bases:
        max_lev = 8 if base <= 6 else 7
        results = variance_reduction(obs_vals, idx, base, max_lev, N)
        all_results[(obs_name, base)] = results

        for m, n_balls, ratio, ball_sz in results:
            reduction = 1 - ratio
            marker = "  ◄" if base == 6 and reduction > 0.05 else ""
            print(f"  {base:>6d}  {m:>5d}  {base**m:>8d}  {n_balls:>7d}  "
                  f"{ball_sz:>7d}  {ratio:>8.5f}  {reduction:>8.5f}{marker}")
    print()


# ── Step 4: Quantitative summary ────────────────────────────────────
print(f"{'='*72}")
print("QUANTITATIVE SUMMARY: 6-ADIC vs CONTROLS")
print(f"{'='*72}\n")
print("Variance reduction (1 - Vw/Vt) at each level for key observables:")
print("Higher = more locally constant on p-adic balls.\n")

key_obs = ['ν₂ mod 12', 'ν₃ mod 9', 'ν₂ (raw)', 'ν₃ (raw)']
for obs_name in key_obs:
    print(f"  {obs_name}:")
    print(f"    {'level':>5s}", end="")
    for base in bases:
        print(f"  {base_names[base]:>18s}", end="")
    print()

    r6 = all_results.get((obs_name, 6), [])
    for m6, _, ratio6, bs6 in r6:
        print(f"    6^{m6:<2d} ", end="")
        print(f"  {1-ratio6:>18.5f}", end="")
        for base in bases[1:]:
            rp = all_results.get((obs_name, base), [])
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


# ── Step 5: Mutual information (vectorised) ──────────────────────────
print(f"{'='*72}")
print("MUTUAL INFORMATION: p-ADIC DIGITS vs WINDING NUMBERS")
print(f"{'='*72}\n")

def mutual_information_vec(x, y, nx, ny):
    """
    Vectorised mutual information I(X;Y) in bits.
    x in [0, nx), y in [0, ny), both integer arrays.
    """
    joint = np.zeros((nx, ny), dtype=np.float64)
    np.add.at(joint, (x, y), 1.0)
    joint /= joint.sum()

    px = joint.sum(axis=1)
    py = joint.sum(axis=0)

    outer = px[:, None] * py[None, :]
    mask = (joint > 0) & (outer > 0)
    mi = np.sum(joint[mask] * np.log2(joint[mask] / outer[mask]))
    return mi


mi_data = {}

for obs_name, obs_vals, K in [('ν₂ mod 12', v2 % 12, 12),
                                ('ν₃ mod 9', v3 % 9, 9),
                                ('ν₂ mod 24', v2 % 24, 24),
                                ('ν₃ mod 27', v3 % 27, 27)]:
    print(f"  {obs_name}:")
    for base in [6, 2, 3, 5, 7]:
        mis = []
        for m in range(1, 8):
            modulus = base ** m
            if modulus > N // 10:
                break
            x = (idx % modulus).astype(np.int64)
            y = obs_vals.astype(np.int64)
            mi = mutual_information_vec(x, y, modulus, K)
            mis.append((m, mi))
        mi_data[(obs_name, base)] = mis
        vals = "  ".join(f"m={m}:{mi:.4f}" for m, mi in mis)
        name = {6:'6', 2:'2', 3:'3', 5:'5(ctrl)', 7:'7(ctrl)'}[base]
        print(f"    base={name:>7s}:  {vals}")
    print()


# ── Step 6: Visualisations ────────────────────────────────────────────
print(f"{'='*72}")
print("GENERATING VISUALISATIONS")
print(f"{'='*72}")

# ─── Figure 1: ŵ(n) along 6-adic ordering (main result) ───
fig = plt.figure(figsize=(18, 16))
gs = GridSpec(4, 2, figure=fig, hspace=0.35, wspace=0.25)

step = max(1, L // 20000)
xs = np.arange(0, L, step)

# (a) ν₂ mod 12 along 6-adic order
ax = fig.add_subplot(gs[0, 0])
ax.scatter(xs, (v2 % 12)[order_6][::step], s=0.1, alpha=0.3,
           c='steelblue', rasterized=True)
ax.set_xlabel('6-adic index')
ax.set_ylabel('ν₂ mod 12')
ax.set_title('(a) ν₂ mod 12,  6-adic ordering')

# (b) ν₃ mod 9 along 6-adic order
ax = fig.add_subplot(gs[0, 1])
ax.scatter(xs, (v3 % 9)[order_6][::step], s=0.1, alpha=0.3,
           c='coral', rasterized=True)
ax.set_xlabel('6-adic index')
ax.set_ylabel('ν₃ mod 9')
ax.set_title('(b) ν₃ mod 9,  6-adic ordering')

# (c) natural ordering control
ax = fig.add_subplot(gs[1, 0])
ax.scatter(xs, (v2 % 12)[::step], s=0.1, alpha=0.3,
           c='steelblue', rasterized=True)
ax.set_xlabel('natural index (n)')
ax.set_ylabel('ν₂ mod 12')
ax.set_title('(c) ν₂ mod 12,  natural ordering (control)')

# (d) 7-adic ordering control
ax = fig.add_subplot(gs[1, 1])
ax.scatter(xs, (v3 % 9)[order_7][::step], s=0.1, alpha=0.3,
           c='coral', rasterized=True)
ax.set_xlabel('7-adic index')
ax.set_ylabel('ν₃ mod 9')
ax.set_title('(d) ν₃ mod 9,  7-adic ordering (control)')

# (e) Zoom: first 6^4 = 1296 elements under 6-adic order
ax = fig.add_subplot(gs[2, 0])
zoom_n = 6**4
idx_zoom = order_6[:zoom_n]
v2_zoom = v2[idx_zoom]
v3_zoom = v3[idx_zoom]
x_zoom = np.arange(zoom_n)

ax.scatter(x_zoom, v2_zoom % 12, s=2, c=v2_zoom % 3, cmap='Set1',
           alpha=0.6, rasterized=True)
ax.set_xlabel('6-adic index (first 1296)')
ax.set_ylabel('ν₂ mod 12')
ax.set_title('(e) Zoom: first 6⁴ elements,  colored by ν₂ mod 3')
for m in range(1, 5):
    for j in range(0, zoom_n, 6**m):
        ax.axvline(x=j, color='gray', alpha=0.15 * m, linewidth=0.5)

# (f) Zoom ν₃ mod 9
ax = fig.add_subplot(gs[2, 1])
ax.scatter(x_zoom, v3_zoom % 9, s=2, c=v3_zoom % 3, cmap='Set1',
           alpha=0.6, rasterized=True)
ax.set_xlabel('6-adic index (first 1296)')
ax.set_ylabel('ν₃ mod 9')
ax.set_title('(f) Zoom: first 6⁴ elements,  colored by ν₃ mod 3')
for m in range(1, 5):
    for j in range(0, zoom_n, 6**m):
        ax.axvline(x=j, color='gray', alpha=0.15 * m, linewidth=0.5)

# (g) Variance reduction comparison: ν₂ mod 12
ax = fig.add_subplot(gs[3, 0])
for base in bases:
    results = all_results.get(('ν₂ mod 12', base), [])
    if not results:
        continue
    ls = [r[0] for r in results]
    reds = [1 - r[2] for r in results]
    style = 'o-' if base == 6 else 's--'
    lw = 2.5 if base == 6 else 1.0
    ax.plot(ls, reds, style, label=base_names[base], linewidth=lw, markersize=4)
ax.set_xlabel('Level m  (ball = residue class mod b^m)')
ax.set_ylabel('Variance reduction  (1 − V_within/V_total)')
ax.set_title('(g) Local constancy: ν₂ mod 12')
ax.legend(fontsize=8)
ax.set_ylim(-0.01, None)
ax.grid(True, alpha=0.3)

# (h) Variance reduction: ν₃ mod 9
ax = fig.add_subplot(gs[3, 1])
for base in bases:
    results = all_results.get(('ν₃ mod 9', base), [])
    if not results:
        continue
    ls = [r[0] for r in results]
    reds = [1 - r[2] for r in results]
    style = 'o-' if base == 6 else 's--'
    lw = 2.5 if base == 6 else 1.0
    ax.plot(ls, reds, style, label=base_names[base], linewidth=lw, markersize=4)
ax.set_xlabel('Level m  (ball = residue class mod b^m)')
ax.set_ylabel('Variance reduction  (1 − V_within/V_total)')
ax.set_title('(h) Local constancy: ν₃ mod 9')
ax.legend(fontsize=8)
ax.set_ylim(-0.01, None)
ax.grid(True, alpha=0.3)

fig.suptitle('6-Adic Ordering Experiment: Testing Odometer Conjugacy\n'
             f'N = {N:,}  |  Ref: Notes II, Conjecture 8.5', fontsize=14, y=0.995)
fig.savefig('/home/claude/sixadic_ordering.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved sixadic_ordering.png")


# ─── Figure 2: Mean ŵ within 6-adic balls at levels 1–3 ───
print("  Computing ball-level heatmaps...")
fig, axes = plt.subplots(2, 3, figsize=(18, 11))

for col, (m, ball_mod) in enumerate([(1, 6), (2, 36), (3, 216)]):
    residues = idx % ball_mod
    mean_v2 = np.bincount(residues, weights=v2.astype(np.float64),
                          minlength=ball_mod)
    mean_v3 = np.bincount(residues, weights=v3.astype(np.float64),
                          minlength=ball_mod)
    counts = np.bincount(residues, minlength=ball_mod).astype(np.float64)
    counts[counts == 0] = 1
    mean_v2 /= counts
    mean_v3 /= counts

    ax_v2 = axes[0, col]
    ax_v3 = axes[1, col]

    if m == 1:
        ax_v2.bar(range(ball_mod), mean_v2, color='steelblue')
        ax_v2.set_xlabel('n mod 6')
        ax_v2.set_ylabel('Mean ν₂')
        ax_v2.set_title('Mean ν₂ by residue mod 6')

        ax_v3.bar(range(ball_mod), mean_v3, color='coral')
        ax_v3.set_xlabel('n mod 6')
        ax_v3.set_ylabel('Mean ν₃')
        ax_v3.set_title('Mean ν₃ by residue mod 6')

    elif m == 2:
        grid_v2 = mean_v2.reshape(6, 6)
        grid_v3 = mean_v3.reshape(6, 6)

        im = ax_v2.imshow(grid_v2.T, origin='lower', aspect='equal', cmap='viridis')
        ax_v2.set_xlabel('digit₀ (n mod 6)')
        ax_v2.set_ylabel('digit₁ ((n//6) mod 6)')
        ax_v2.set_title('Mean ν₂ by residue mod 36')
        plt.colorbar(im, ax=ax_v2, shrink=0.8)

        im = ax_v3.imshow(grid_v3.T, origin='lower', aspect='equal', cmap='magma')
        ax_v3.set_xlabel('digit₀ (n mod 6)')
        ax_v3.set_ylabel('digit₁ ((n//6) mod 6)')
        ax_v3.set_title('Mean ν₃ by residue mod 36')
        plt.colorbar(im, ax=ax_v3, shrink=0.8)

    else:
        flat_v2 = mean_v2.reshape(36, 6)
        flat_v3 = mean_v3.reshape(36, 6)

        im = ax_v2.imshow(flat_v2, origin='lower', aspect='auto', cmap='viridis')
        ax_v2.set_xlabel('digit₀ (n mod 6)')
        ax_v2.set_ylabel('6·digit₂ + digit₁')
        ax_v2.set_title('Mean ν₂ by residue mod 216')
        plt.colorbar(im, ax=ax_v2, shrink=0.8)

        im = ax_v3.imshow(flat_v3, origin='lower', aspect='auto', cmap='magma')
        ax_v3.set_xlabel('digit₀ (n mod 6)')
        ax_v3.set_ylabel('6·digit₂ + digit₁')
        ax_v3.set_title('Mean ν₃ by residue mod 216')
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


# ─── Figure 4: 2D scatter colored by p-adic digit ───
fig, axes = plt.subplots(1, 3, figsize=(18, 5.5))
rng = np.random.RandomState(42)
sub = rng.choice(L, size=50000, replace=False)

ax = axes[0]
sc = ax.scatter((v2 % 12)[sub], (v3 % 9)[sub],
                c=(idx % 6)[sub], cmap='tab10', s=1, alpha=0.4,
                vmin=0, vmax=5, rasterized=True)
ax.set_xlabel('ν₂ mod 12')
ax.set_ylabel('ν₃ mod 9')
ax.set_title('(a) Colored by n mod 6  (1st 6-adic digit)')
plt.colorbar(sc, ax=ax, ticks=range(6), label='n mod 6')

ax = axes[1]
sc = ax.scatter((v2 % 12)[sub], (v3 % 9)[sub],
                c=(idx % 36)[sub], cmap='nipy_spectral', s=1, alpha=0.4,
                rasterized=True)
ax.set_xlabel('ν₂ mod 12')
ax.set_ylabel('ν₃ mod 9')
ax.set_title('(b) Colored by n mod 36  (first two 6-adic digits)')
plt.colorbar(sc, ax=ax, label='n mod 36')

ax = axes[2]
sc = ax.scatter((v2 % 12)[sub], (v3 % 9)[sub],
                c=(idx % 7)[sub], cmap='tab10', s=1, alpha=0.4,
                vmin=0, vmax=6, rasterized=True)
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


# ─── Figure 5: Mutual information ───
print("  Plotting mutual information...")
fig, axes = plt.subplots(2, 2, figsize=(14, 10))

for ax_idx, (obs_name, K) in enumerate([('ν₂ mod 12', 12), ('ν₃ mod 9', 9),
                                          ('ν₂ mod 24', 24), ('ν₃ mod 27', 27)]):
    ax = axes[ax_idx // 2, ax_idx % 2]
    for base in [6, 2, 3, 5, 7]:
        mis = mi_data.get((obs_name, base), [])
        if not mis:
            continue
        levels = [m for m, _ in mis]
        vals = [v for _, v in mis]
        style = 'o-' if base == 6 else ('s-' if base in [2, 3] else 'x--')
        lw = 2.5 if base == 6 else (1.5 if base in [2, 3] else 1.0)
        name = {6: '6-adic', 2: '2-adic', 3: '3-adic',
                5: '5-adic (ctrl)', 7: '7-adic (ctrl)'}[base]
        ax.plot(levels, vals, style, label=name, linewidth=lw, markersize=5)

    ax.set_xlabel('Level m')
    ax.set_ylabel('I(n mod b^m ; observable)  [bits]')
    ax.set_title(f'MI with {obs_name}')
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)

fig.suptitle('Mutual Information: p-Adic Digit Structure vs Winding Numbers\n'
             '6-adic should dominate 5-adic and 7-adic if odometer structure exists',
             fontsize=12)
fig.tight_layout(rect=[0, 0, 1, 0.92])
fig.savefig('/home/claude/sixadic_mutual_info.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved sixadic_mutual_info.png")


# ── Copy to outputs ─────────────────────────────────────────────────
import shutil
for f in ['sixadic_ordering.png', 'sixadic_ball_means.png',
          'sixadic_conditionals.png', 'sixadic_scatter_colored.png',
          'sixadic_mutual_info.png']:
    src = f'/home/claude/{f}'
    dst = f'/mnt/user-data/outputs/{f}'
    try:
        shutil.copy2(src, dst)
    except Exception as e:
        print(f"  Warning: could not copy {f}: {e}")

shutil.copy2('/home/claude/sixadic_ordering.py',
             '/mnt/user-data/outputs/sixadic_ordering.py')

print(f"\nAll outputs saved.")
