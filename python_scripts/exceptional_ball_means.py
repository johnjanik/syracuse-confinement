#!/usr/bin/env python3
"""
Winding Number Residues mod Exceptional Lie Algebra Dimensions
===============================================================

For each exceptional simple Lie algebra, display mean ν₂ and mean ν₃
within residue classes mod:
  - dim(root system) = |Φ|
  - dim(Lie algebra)  = |Φ| + rank

G₂:  |Φ| = 12,  dim = 14
F₄:  |Φ| = 48,  dim = 52
E₆:  |Φ| = 72,  dim = 78
E₇:  |Φ| = 126, dim = 133
E₈:  |Φ| = 240, dim = 248
"""

import numpy as np
import time

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec

N = 1_000_000

# ── Compute winding pairs ───────────────────────────────────────────
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

idx = np.arange(2, N + 1)
v2 = nu2[2:N+1].astype(np.float64)
v3 = nu3[2:N+1].astype(np.float64)
t1 = time.time()
print(f"  Done in {t1 - t0:.1f}s.")

# ── Exceptional Lie algebra data ────────────────────────────────────
# (name, modulus, factorization (rows, cols) for 2D display)
algebras = [
    (r'$G_2$',  12,  (3, 4),   '|Φ| = 12'),
    (r'$G_2$',  14,  (2, 7),   'dim = 14'),
    (r'$F_4$',  48,  (6, 8),   '|Φ| = 48'),
    (r'$F_4$',  52,  (4, 13),  'dim = 52'),
    (r'$E_6$',  72,  (8, 9),   '|Φ| = 72'),
    (r'$E_6$',  78,  (6, 13),  'dim = 78'),
    (r'$E_7$',  126, (9, 14),  '|Φ| = 126'),
    (r'$E_7$',  133, (7, 19),  'dim = 133'),
    (r'$E_8$',  240, (15, 16), '|Φ| = 240'),
    (r'$E_8$',  248, (8, 31),  'dim = 248'),
]

def compute_ball_means(mod_val):
    """Compute mean ν₂ and ν₃ within each residue class mod `mod_val`."""
    residues = idx % mod_val
    counts = np.bincount(residues, minlength=mod_val).astype(np.float64)
    sum_v2 = np.bincount(residues, weights=v2, minlength=mod_val)
    sum_v3 = np.bincount(residues, weights=v3, minlength=mod_val)
    counts[counts == 0] = 1
    return sum_v2 / counts, sum_v3 / counts, counts

# ── Figure: 10 × 2 grid (each algebra gets one row, ν₂ and ν₃ columns) ──
fig, axes = plt.subplots(10, 2, figsize=(16, 40))

for row, (name, mod, (nr, nc), label) in enumerate(algebras):
    mean_v2, mean_v3, counts = compute_ball_means(mod)

    grid_v2 = mean_v2.reshape(nr, nc)
    grid_v3 = mean_v3.reshape(nr, nc)

    # ν₂
    ax = axes[row, 0]
    im = ax.imshow(grid_v2, origin='lower', aspect='auto', cmap='viridis',
                   interpolation='nearest')
    ax.set_title(f'{name}  {label}  —  Mean ν₂', fontsize=11)
    ax.set_xlabel(f'r mod {nc}')
    ax.set_ylabel(f'⌊r/{nc}⌋')
    plt.colorbar(im, ax=ax, shrink=0.85, pad=0.02)

    # ν₃
    ax = axes[row, 1]
    im = ax.imshow(grid_v3, origin='lower', aspect='auto', cmap='magma',
                   interpolation='nearest')
    ax.set_title(f'{name}  {label}  —  Mean ν₃', fontsize=11)
    ax.set_xlabel(f'r mod {nc}')
    ax.set_ylabel(f'⌊r/{nc}⌋')
    plt.colorbar(im, ax=ax, shrink=0.85, pad=0.02)

fig.suptitle('Mean Winding Numbers by Residue Class mod Exceptional Lie Algebra Dimensions\n'
             f'N = {N:,}  |  Root system |Φ| and Lie algebra dim = |Φ| + rank',
             fontsize=15, y=1.002)
fig.tight_layout(rect=[0, 0, 1, 0.995])
fig.savefig('/home/claude/exceptional_ball_means.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved exceptional_ball_means.png")


# ── Compact figure: just E₈ at highest resolution ───────────────────
fig, axes = plt.subplots(2, 2, figsize=(18, 12))

for col, (mod, (nr, nc), label) in enumerate([(240, (15, 16), '|Φ| = 240'),
                                                (248, (8, 31), 'dim = 248')]):
    mean_v2, mean_v3, _ = compute_ball_means(mod)
    grid_v2 = mean_v2.reshape(nr, nc)
    grid_v3 = mean_v3.reshape(nr, nc)

    ax = axes[0, col]
    im = ax.imshow(grid_v2, origin='lower', aspect='auto', cmap='viridis',
                   interpolation='nearest')
    ax.set_title(f'$E_8$  {label}  —  Mean ν₂', fontsize=13)
    ax.set_xlabel(f'r mod {nc}')
    ax.set_ylabel(f'⌊r/{nc}⌋')
    plt.colorbar(im, ax=ax, shrink=0.85)

    ax = axes[1, col]
    im = ax.imshow(grid_v3, origin='lower', aspect='auto', cmap='magma',
                   interpolation='nearest')
    ax.set_title(f'$E_8$  {label}  —  Mean ν₃', fontsize=13)
    ax.set_xlabel(f'r mod {nc}')
    ax.set_ylabel(f'⌊r/{nc}⌋')
    plt.colorbar(im, ax=ax, shrink=0.85)

fig.suptitle('$E_8$ Winding Number Residue Structure\n'
             f'N = {N:,}', fontsize=15)
fig.tight_layout(rect=[0, 0, 1, 0.95])
fig.savefig('/home/claude/e8_ball_means.png', dpi=150, bbox_inches='tight')
plt.close(fig)
print("  Saved e8_ball_means.png")


# ── Variance reduction & entropy for each modulus ───────────────────
print(f"\n{'='*72}")
print("VARIANCE REDUCTION AND ENTROPY BY EXCEPTIONAL MODULUS")
print(f"{'='*72}\n")
print(f"{'Algebra':>6s}  {'mod':>5s}  {'type':>8s}  "
      f"{'VR(ν₂)':>8s}  {'VR(ν₃)':>8s}  {'H/Hmax(ν₂)':>11s}  {'H/Hmax(ν₃)':>11s}")
print(f"{'─'*72}")

for name_raw, mod, (nr, nc), label in algebras:
    name_clean = name_raw.replace('$', '').replace('_', '')
    mean_v2, mean_v3, counts = compute_ball_means(mod)

    # Variance reduction
    total_var_v2 = np.var(v2)
    total_var_v3 = np.var(v3)

    residues = idx % mod
    ss_between_v2 = np.sum(counts * (mean_v2 - v2.mean())**2)
    ss_between_v3 = np.sum(counts * (mean_v3 - v3.mean())**2)

    vr_v2 = ss_between_v2 / (total_var_v2 * len(idx))
    vr_v3 = ss_between_v3 / (total_var_v3 * len(idx))

    # Entropy of the mean-value distribution (discretised)
    # Use the distribution of counts (should be ~uniform)
    p_v2 = counts / counts.sum()
    p_v2 = p_v2[p_v2 > 0]
    H_v2 = -np.sum(p_v2 * np.log2(p_v2))
    H_max = np.log2(mod)

    p_v3 = counts / counts.sum()
    p_v3 = p_v3[p_v3 > 0]
    H_v3 = -np.sum(p_v3 * np.log2(p_v3))

    typ = 'roots' if 'Φ' in label else 'dim'
    print(f"{name_clean:>6s}  {mod:>5d}  {typ:>8s}  "
          f"{vr_v2:>8.5f}  {vr_v3:>8.5f}  {H_v2/H_max:>11.6f}  {H_v3/H_max:>11.6f}")

# ── Copy outputs ────────────────────────────────────────────────────
import shutil
for f in ['exceptional_ball_means.png', 'e8_ball_means.png']:
    shutil.copy2(f'/home/claude/{f}', f'/mnt/user-data/outputs/{f}')
shutil.copy2('/home/claude/exceptional_ball_means.py',
             '/mnt/user-data/outputs/exceptional_ball_means.py')

print("\nDone.")
