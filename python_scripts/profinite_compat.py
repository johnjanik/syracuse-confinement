#!/usr/bin/env python3
"""
Profinite Compatibility Test for Collatz Winding Numbers
=========================================================

Compute μ_k(a,b) = #{n ∈ [2,N] : ν₂(n) ≡ a, ν₃(n) ≡ b (mod k)}
for all k = 2^a · 3^b with 0 ≤ a,b ≤ 4.

Verify the inverse limit compatibility condition:
  For k | k',  μ_k(a,b) = Σ_{a'≡a, b'≡b mod k} μ_{k'}(a',b')

This is the foundational test for the profinite winding number
ŵ(n) ∈ Ẑ₂ × Ẑ₃.  If compatibility holds, the solenoid formulation
is empirically supported.  If it fails, the formulation is ruled out.

Ref: Notes II §5.1
"""

import numpy as np
from collections import defaultdict
import time
import sys

# ── Parameters ──────────────────────────────────────────────────────
N = 2_000_000   # upper bound on starting values
# Levels k = 2^a · 3^b for 0 ≤ a,b ≤ 4
MAX_A = 4
MAX_B = 4

def generate_levels():
    """Generate all k = 2^a · 3^b, sorted, with (a,b) labels."""
    levels = {}
    for a in range(MAX_A + 1):
        for b in range(MAX_B + 1):
            k = (2**a) * (3**b)
            levels[k] = (a, b)
    return dict(sorted(levels.items()))

LEVELS = generate_levels()
print(f"Levels k = 2^a · 3^b  (0 ≤ a,b ≤ {MAX_A}):")
for k, (a, b) in LEVELS.items():
    print(f"  k = {k:5d}  (2^{a} · 3^{b})")
print(f"\n{len(LEVELS)} levels total.\n")

# ── Step 1: Compute winding pairs (ν₂, ν₃) for all n ∈ [2, N] ──────
print(f"Computing winding pairs for n ∈ [2, {N}]...")
t0 = time.time()

nu2_arr = np.zeros(N + 1, dtype=np.int32)
nu3_arr = np.zeros(N + 1, dtype=np.int32)

for n in range(2, N + 1):
    x = n
    even_count = 0
    odd_count = 0
    while x != 1:
        if x % 2 == 0:
            x //= 2
            even_count += 1
        else:
            x = 3 * x + 1
            odd_count += 1
    nu2_arr[n] = even_count
    nu3_arr[n] = odd_count

t1 = time.time()
print(f"  Done in {t1 - t0:.1f}s.  ({N - 1} trajectories)")
print(f"  ν₂ range: [{nu2_arr[2:N+1].min()}, {nu2_arr[2:N+1].max()}]")
print(f"  ν₃ range: [{nu3_arr[2:N+1].min()}, {nu3_arr[2:N+1].max()}]")

# ── Step 2: Compute μ_k for each level ──────────────────────────────
print(f"\nComputing μ_k distributions...")
t2 = time.time()

# mu[k] is a 2D array of shape (k, k) with counts
mu = {}
for k in LEVELS:
    grid = np.zeros((k, k), dtype=np.int64)
    a_mod = nu2_arr[2:N+1] % k
    b_mod = nu3_arr[2:N+1] % k
    # Fast 2D histogram
    for i in range(len(a_mod)):
        grid[a_mod[i], b_mod[i]] += 1
    mu[k] = grid

t3 = time.time()
print(f"  Done in {t3 - t2:.1f}s.")

# Verify total counts
for k in LEVELS:
    total = mu[k].sum()
    assert total == N - 1, f"Count mismatch at k={k}: {total} ≠ {N-1}"

# ── Step 3: Profinite compatibility test ─────────────────────────────
print(f"\n{'='*72}")
print(f"PROFINITE COMPATIBILITY TEST")
print(f"{'='*72}")
print(f"For each pair k | k' in our level set, verify:")
print(f"  μ_k(a,b) = Σ{{a'≡a, b'≡b mod k}} μ_{{k'}}(a',b')")
print()

# Find all divisibility pairs (k, k') with k | k' and k ≠ k'
pairs = []
level_keys = sorted(LEVELS.keys())
for i, k in enumerate(level_keys):
    for j, kp in enumerate(level_keys):
        if kp > k and kp % k == 0:
            pairs.append((k, kp))

print(f"Found {len(pairs)} divisibility pairs to test.\n")

all_pass = True
max_error = 0
results = []

for k, kp in pairs:
    ratio = kp // k
    # Marginalise μ_{k'} down to level k
    marginal = np.zeros((k, k), dtype=np.int64)
    for a in range(kp):
        for b in range(kp):
            marginal[a % k, b % k] += mu[kp][a, b]

    # Compare
    diff = mu[k] - marginal
    err = np.abs(diff).max()
    passed = (err == 0)

    if not passed:
        all_pass = False
    max_error = max(max_error, err)

    a_k, b_k = LEVELS[k]
    a_kp, b_kp = LEVELS[kp]
    status = "PASS" if passed else "FAIL"
    results.append((k, kp, err, passed))

    if not passed or kp <= 81:  # always print small levels
        print(f"  {k:5d} (2^{a_k}·3^{b_k}) | {kp:5d} (2^{a_kp}·3^{b_kp})  "
              f"ratio={ratio:4d}  max|Δ|={err}  [{status}]")

# Print summary
print(f"\n{'─'*72}")
n_pass = sum(1 for _, _, _, p in results if p)
n_fail = sum(1 for _, _, _, p in results if not p)
print(f"RESULTS:  {n_pass} PASS,  {n_fail} FAIL  (out of {len(results)} pairs)")
print(f"Maximum absolute error: {max_error}")

if all_pass:
    print(f"\n  *** ALL COMPATIBILITY CONDITIONS SATISFIED ***")
    print(f"  The winding pair (ν₂, ν₃) defines a consistent profinite")
    print(f"  invariant ŵ(n) ∈ Ẑ₂ × Ẑ₃ at all tested levels.")
    print(f"  The solenoid formulation is empirically supported.")
else:
    print(f"\n  *** COMPATIBILITY FAILURE DETECTED ***")
    print(f"  The profinite picture may be inconsistent at some level.")
    for k, kp, err, passed in results:
        if not passed:
            print(f"    FAILED: {k} | {kp}, max error = {err}")

# ── Step 4: Detailed diagnostics ─────────────────────────────────────
print(f"\n{'='*72}")
print(f"DETAILED DIAGNOSTICS")
print(f"{'='*72}")

# For each level, report: dimension, #nonzero cells, #zero cells,
# max/min density, entropy
print(f"\n{'k':>6s}  {'(a,b)':>7s}  {'cells':>6s}  {'nonzero':>7s}  "
      f"{'zero':>5s}  {'max_dens':>9s}  {'min_dens':>9s}  {'H/log(k²)':>10s}")
print(f"{'─'*72}")

for k, (a, b) in LEVELS.items():
    if k == 1:
        continue
    grid = mu[k]
    total = grid.sum()
    ncells = k * k
    nz = np.count_nonzero(grid)
    zero = ncells - nz

    # Density (normalised)
    dens = grid / total
    max_d = dens.max()
    min_d = dens[dens > 0].min() if nz > 0 else 0

    # Shannon entropy
    p = dens[dens > 0]
    H = -np.sum(p * np.log2(p))
    H_max = np.log2(ncells)
    H_ratio = H / H_max if H_max > 0 else 0

    print(f"{k:6d}  (2^{a}·3^{b})  {ncells:6d}  {nz:7d}  "
          f"{zero:5d}  {max_d:9.6f}  {min_d:9.6f}  {H_ratio:10.6f}")

# ── Step 5: Forbidden cells at each level ─────────────────────────────
print(f"\n{'='*72}")
print(f"FORBIDDEN / SUPPRESSED CELLS")
print(f"{'='*72}")
print(f"Cells with count = 0 or count < expected/100 at each level:\n")

for k, (a, b) in LEVELS.items():
    if k == 1:
        continue
    grid = mu[k]
    total = grid.sum()
    expected = total / (k * k)  # uniform expectation

    # Strictly zero cells
    zero_cells = list(zip(*np.where(grid == 0)))
    # Heavily suppressed (< 1% of expected)
    suppressed = [(i, j) for i in range(k) for j in range(k)
                  if 0 < grid[i, j] < expected / 100]

    if zero_cells or suppressed:
        print(f"  k = {k} (2^{a}·3^{b}):")
        if zero_cells and len(zero_cells) <= 20:
            print(f"    Zero cells ({len(zero_cells)}): "
                  f"{zero_cells[:20]}{'...' if len(zero_cells)>20 else ''}")
        elif zero_cells:
            print(f"    Zero cells: {len(zero_cells)} (too many to list)")
        if suppressed and len(suppressed) <= 10:
            print(f"    Suppressed (<1% expected): {suppressed}")
        elif suppressed:
            print(f"    Suppressed (<1% expected): {len(suppressed)} cells")

# ── Step 6: Visualisations ────────────────────────────────────────────
print(f"\n{'='*72}")
print(f"GENERATING VISUALISATIONS")
print(f"{'='*72}")

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import LogNorm

# --- Panel 1: Grid of μ_k heatmaps for small levels ---
small_levels = [k for k in LEVELS if k <= 36]
n_panels = len(small_levels)
ncols = 4
nrows = (n_panels + ncols - 1) // ncols

fig, axes = plt.subplots(nrows, ncols, figsize=(16, 4 * nrows))
axes = axes.flatten()

for idx, k in enumerate(small_levels):
    ax = axes[idx]
    grid = mu[k].astype(float)
    grid[grid == 0] = np.nan  # show zeros as distinct colour

    if k <= 4:
        im = ax.imshow(grid.T, origin='lower', aspect='equal',
                       cmap='YlOrRd', interpolation='nearest')
        # Annotate cells with counts
        for i in range(k):
            for j in range(k):
                val = mu[k][i, j]
                ax.text(i, j, f'{val}', ha='center', va='center',
                        fontsize=max(6, 10 - k), color='black')
    else:
        im = ax.imshow(grid.T, origin='lower', aspect='equal',
                       cmap='YlOrRd', interpolation='nearest')

    a_lev, b_lev = LEVELS[k]
    ax.set_title(f'k = {k}  (2^{a_lev}·3^{b_lev})', fontsize=10)
    ax.set_xlabel('ν₂ mod k')
    ax.set_ylabel('ν₃ mod k')
    plt.colorbar(im, ax=ax, shrink=0.8)

for idx in range(len(small_levels), len(axes)):
    axes[idx].set_visible(False)

fig.suptitle(f'Torus Residue Distributions μ_k  (N = {N:,})', fontsize=14, y=1.01)
fig.tight_layout()
fig.savefig('/home/claude/profinite_heatmaps.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved profinite_heatmaps.png")

# --- Panel 2: Compatibility check visualisation ---
# For key pairs, show the marginal vs direct comparison
test_pairs = [(3, 9), (3, 27), (2, 6), (4, 12), (6, 36), (9, 27),
              (12, 36), (8, 24), (6, 18), (4, 36)]
test_pairs = [(k, kp) for k, kp in test_pairs if k in LEVELS and kp in LEVELS]

n_test = min(len(test_pairs), 10)
fig, axes = plt.subplots(n_test, 3, figsize=(14, 3.5 * n_test))
if n_test == 1:
    axes = axes[np.newaxis, :]

for idx, (k, kp) in enumerate(test_pairs[:n_test]):
    # Direct μ_k
    ax_direct = axes[idx, 0]
    grid_direct = mu[k].astype(float)
    grid_direct[grid_direct == 0] = np.nan
    im1 = ax_direct.imshow(grid_direct.T, origin='lower', aspect='equal',
                            cmap='YlOrRd', interpolation='nearest')
    ax_direct.set_title(f'μ_{{{k}}} (direct)', fontsize=9)
    plt.colorbar(im1, ax=ax_direct, shrink=0.8)

    # Marginalised from μ_{k'}
    marginal = np.zeros((k, k), dtype=np.int64)
    for a in range(kp):
        for b in range(kp):
            marginal[a % k, b % k] += mu[kp][a, b]
    ax_marg = axes[idx, 1]
    grid_marg = marginal.astype(float)
    grid_marg[grid_marg == 0] = np.nan
    im2 = ax_marg.imshow(grid_marg.T, origin='lower', aspect='equal',
                          cmap='YlOrRd', interpolation='nearest')
    ax_marg.set_title(f'Marginal from μ_{{{kp}}}', fontsize=9)
    plt.colorbar(im2, ax=ax_marg, shrink=0.8)

    # Difference
    ax_diff = axes[idx, 2]
    diff = mu[k].astype(float) - marginal.astype(float)
    max_abs = max(np.abs(diff).max(), 1e-10)
    im3 = ax_diff.imshow(diff.T, origin='lower', aspect='equal',
                          cmap='RdBu_r', interpolation='nearest',
                          vmin=-max_abs, vmax=max_abs)
    ax_diff.set_title(f'Δ = μ_{{{k}}} − marg(μ_{{{kp}}})  max|Δ|={int(max_abs)}',
                       fontsize=9)
    plt.colorbar(im3, ax=ax_diff, shrink=0.8)

fig.suptitle('Profinite Compatibility: Direct vs Marginalised Distributions',
             fontsize=13, y=1.01)
fig.tight_layout()
fig.savefig('/home/claude/profinite_compatibility.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved profinite_compatibility.png")

# --- Panel 3: Larger levels (k = 48, 72, 81) as heatmaps ---
large_levels = [k for k in LEVELS if k >= 48]
if large_levels:
    fig, axes = plt.subplots(1, len(large_levels),
                              figsize=(6 * len(large_levels), 5))
    if len(large_levels) == 1:
        axes = [axes]

    for idx, k in enumerate(large_levels):
        ax = axes[idx]
        grid = mu[k].astype(float)
        # Use log scale for large grids
        grid_plot = grid.copy()
        grid_plot[grid_plot == 0] = np.nan
        im = ax.imshow(grid_plot.T, origin='lower', aspect='equal',
                       cmap='inferno', interpolation='nearest',
                       norm=LogNorm(vmin=max(1, grid[grid > 0].min()),
                                    vmax=grid.max()))
        a_lev, b_lev = LEVELS[k]
        ax.set_title(f'k = {k}  (2^{a_lev}·3^{b_lev})', fontsize=11)
        ax.set_xlabel('ν₂ mod k')
        ax.set_ylabel('ν₃ mod k')
        plt.colorbar(im, ax=ax, shrink=0.8, label='count (log scale)')

    fig.suptitle(f'Torus Residues at Large Levels  (N = {N:,})', fontsize=13)
    fig.tight_layout()
    fig.savefig('/home/claude/profinite_large_levels.png', dpi=150,
                bbox_inches='tight')
    plt.close(fig)
    print("  Saved profinite_large_levels.png")

# --- Panel 4: Entropy ratio vs level ---
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

entropies = []
for k in sorted(LEVELS.keys()):
    if k == 1:
        continue
    grid = mu[k]
    total = grid.sum()
    dens = grid.flatten() / total
    p = dens[dens > 0]
    H = -np.sum(p * np.log2(p))
    H_max = np.log2(k * k)
    entropies.append((k, H, H_max, H / H_max))

ks = [e[0] for e in entropies]
ratios = [e[3] for e in entropies]

ax1.bar(range(len(ks)), ratios, color='steelblue', alpha=0.8)
ax1.set_xticks(range(len(ks)))
ax1.set_xticklabels([str(k) for k in ks], rotation=45, fontsize=8)
ax1.set_ylabel('H(μ_k) / log₂(k²)')
ax1.set_xlabel('Level k')
ax1.set_title('Normalised Entropy of μ_k')
ax1.axhline(y=1.0, color='red', linestyle='--', alpha=0.5, label='Uniform (Haar)')
ax1.legend()
ax1.set_ylim(0.5, 1.05)

# Zero-cell fraction
zero_fracs = []
for k in sorted(LEVELS.keys()):
    if k == 1:
        continue
    grid = mu[k]
    ncells = k * k
    nz = np.count_nonzero(grid)
    zero_fracs.append((k, 1 - nz / ncells))

ks2 = [e[0] for e in zero_fracs]
fracs = [e[1] for e in zero_fracs]

ax2.bar(range(len(ks2)), fracs, color='coral', alpha=0.8)
ax2.set_xticks(range(len(ks2)))
ax2.set_xticklabels([str(k) for k in ks2], rotation=45, fontsize=8)
ax2.set_ylabel('Fraction of zero cells')
ax2.set_xlabel('Level k')
ax2.set_title('Empty Cells in (ℤ/kℤ)²')

fig.suptitle('Information Content of Torus Residue Distributions', fontsize=13)
fig.tight_layout()
fig.savefig('/home/claude/profinite_entropy.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved profinite_entropy.png")

# ── Step 7: Summary table for manuscript ──────────────────────────────
print(f"\n{'='*72}")
print(f"SUMMARY TABLE (for manuscript)")
print(f"{'='*72}")
print(f"{'k':>5s}  {'(a,b)':>6s}  {'|cells|':>7s}  {'nonzero':>7s}  "
      f"{'H/H_max':>8s}  {'compat_pairs':>12s}  {'all_pass':>8s}")
print(f"{'─'*72}")

for k, (a, b) in LEVELS.items():
    if k == 1:
        # k=1 is trivial
        print(f"{k:5d}  (2^{a}·3^{b})  {1:7d}  {1:7d}  {'1.000':>8s}  "
              f"{'—':>12s}  {'—':>8s}")
        continue

    grid = mu[k]
    ncells = k * k
    nz = np.count_nonzero(grid)
    total = grid.sum()
    dens = grid.flatten() / total
    p = dens[dens > 0]
    H = -np.sum(p * np.log2(p))
    H_max = np.log2(ncells)
    H_ratio = H / H_max

    # Count how many compatibility pairs involve this k as the lower level
    compat_count = 0
    compat_pass = 0
    for k2, kp, err, passed in results:
        if k2 == k:
            compat_count += 1
            if passed:
                compat_pass += 1

    compat_str = f"{compat_pass}/{compat_count}" if compat_count > 0 else "—"
    all_ok = "YES" if (compat_count == 0 or compat_pass == compat_count) else "NO"

    print(f"{k:5d}  (2^{a}·3^{b})  {ncells:7d}  {nz:7d}  "
          f"{H_ratio:8.4f}  {compat_str:>12s}  {all_ok:>8s}")

print(f"\nN = {N:,}  |  Total trajectories: {N-1:,}")
print(f"Global compatibility: {'ALL PASS' if all_pass else 'SOME FAILURES'}")

# Copy outputs
import shutil
for f in ['profinite_heatmaps.png', 'profinite_compatibility.png',
          'profinite_large_levels.png', 'profinite_entropy.png']:
    src = f'/home/claude/{f}'
    dst = f'/mnt/user-data/outputs/{f}'
    try:
        shutil.copy2(src, dst)
    except:
        pass

print(f"\nDone.")
