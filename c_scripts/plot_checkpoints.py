#!/usr/bin/env python3
"""
Plot wall density and branch count growth from branch_checkpoints.csv.

Generates:
  1. Branch count vs N for key levels
  2. Wall fraction (pure_even / occupied) vs N
  3. Pure-odd count vs N
  4. Saturation curves (occupied / k^2) vs N
"""

import csv
import math
import sys
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

# ── Read checkpoint data ──────────────────────────────────────────────

data = {}  # key: (checkpoint_N, k) -> {branch, pure_even, pure_odd, empty}
all_Ns = set()
all_ks = set()

with open("branch_checkpoints.csv") as f:
    reader = csv.DictReader(f)
    for r in reader:
        N = int(r["checkpoint_N"])
        k = int(r["k"])
        all_Ns.add(N)
        all_ks.add(k)
        data[(N, k)] = {
            "branch": int(r["branch"]),
            "pure_even": int(r["pure_even"]),
            "pure_odd": int(r["pure_odd"]),
            "empty": int(r["empty"]),
        }

Ns = sorted(all_Ns)
ks = sorted(all_ks)

# Key levels for plotting
key_levels = [k for k in [72, 81, 108, 144, 162, 216, 729] if k in all_ks]
# Add 19683 if present
if 19683 in all_ks:
    key_levels.append(19683)

# ── Helper ────────────────────────────────────────────────────────────

def get_series(k_val, field):
    """Extract (N, value) pairs for a given k and field."""
    xs, ys = [], []
    for N in Ns:
        if (N, k_val) in data:
            xs.append(N)
            ys.append(data[(N, k_val)][field])
    return np.array(xs), np.array(ys)

# ── Figure 1: Branch count growth ────────────────────────────────────

fig, axes = plt.subplots(1, 2, figsize=(14, 6))

ax = axes[0]
for k_val in key_levels:
    xs, ys = get_series(k_val, "branch")
    if len(xs) > 0 and ys.max() > 0:
        ax.semilogx(xs, ys, ".-", label=f"k={k_val}", markersize=3)
ax.set_xlabel("N (trajectories)")
ax.set_ylabel("Branch cells")
ax.set_title("Branch count growth")
ax.legend(fontsize=8)
ax.grid(True, alpha=0.3)

# Occupied count (branch + pe + po)
ax = axes[1]
for k_val in key_levels:
    xs_b, ys_b = get_series(k_val, "branch")
    xs_pe, ys_pe = get_series(k_val, "pure_even")
    xs_po, ys_po = get_series(k_val, "pure_odd")
    if len(xs_b) > 0:
        ys_occ = ys_b + ys_pe + ys_po
        if ys_occ.max() > 0:
            ax.semilogx(xs_b, ys_occ, ".-", label=f"k={k_val}", markersize=3)
ax.set_xlabel("N (trajectories)")
ax.set_ylabel("Occupied cells")
ax.set_title("Total occupied (branch + pe + po)")
ax.legend(fontsize=8)
ax.grid(True, alpha=0.3)

fig.tight_layout()
outdir = os.path.join(os.path.dirname(__file__), "..", "saved_output")
os.makedirs(outdir, exist_ok=True)
fig.savefig(os.path.join(outdir, "checkpoint_branch_growth.png"), dpi=150)
print(f"Saved checkpoint_branch_growth.png")
plt.close(fig)

# ── Figure 2: Wall fraction and pure-odd vs N ────────────────────────

fig, axes = plt.subplots(1, 2, figsize=(14, 6))

# Wall fraction = pure_even / (branch + pure_even + pure_odd)
ax = axes[0]
for k_val in key_levels:
    xs_b, ys_b = get_series(k_val, "branch")
    xs_pe, ys_pe = get_series(k_val, "pure_even")
    xs_po, ys_po = get_series(k_val, "pure_odd")
    if len(xs_b) > 0:
        ys_occ = ys_b + ys_pe + ys_po
        mask = ys_occ > 0
        if mask.any():
            wall_frac = np.where(mask, ys_pe / ys_occ, 0)
            ax.semilogx(xs_b[mask], wall_frac[mask], ".-",
                       label=f"k={k_val}", markersize=3)
ax.set_xlabel("N (trajectories)")
ax.set_ylabel("Wall fraction (pe / occupied)")
ax.set_title("Pure-Even wall density vs N")
ax.legend(fontsize=8)
ax.grid(True, alpha=0.3)

# Pure-odd count
ax = axes[1]
for k_val in key_levels:
    xs, ys = get_series(k_val, "pure_odd")
    if len(xs) > 0 and ys.max() > 0:
        ax.semilogx(xs, ys, ".-", label=f"k={k_val}", markersize=3)
ax.set_xlabel("N (trajectories)")
ax.set_ylabel("Pure-odd cells")
ax.set_title("Pure-odd count vs N")
ax.legend(fontsize=8)
ax.grid(True, alpha=0.3)

fig.tight_layout()
fig.savefig(os.path.join(outdir, "checkpoint_wall_scaling.png"), dpi=150)
print(f"Saved checkpoint_wall_scaling.png")
plt.close(fig)

# ── Figure 3: Saturation curves ──────────────────────────────────────

fig, ax = plt.subplots(figsize=(10, 6))

for k_val in key_levels:
    k2 = k_val * k_val
    xs_b, ys_b = get_series(k_val, "branch")
    xs_pe, ys_pe = get_series(k_val, "pure_even")
    xs_po, ys_po = get_series(k_val, "pure_odd")
    if len(xs_b) > 0:
        ys_occ = ys_b + ys_pe + ys_po
        fill_frac = ys_occ / k2
        if fill_frac.max() > 0.01:  # skip levels that are barely filled
            ax.semilogx(xs_b, fill_frac * 100, ".-",
                       label=f"k={k_val} ({k2} cells)", markersize=3)

ax.axhline(100, color="gray", linestyle="--", alpha=0.5, label="100% saturated")
ax.set_xlabel("N (trajectories)")
ax.set_ylabel("Fill fraction (%)")
ax.set_title("Saturation curves: occupied / k² vs N")
ax.legend(fontsize=8)
ax.grid(True, alpha=0.3)
ax.set_ylim(0, 110)

fig.tight_layout()
fig.savefig(os.path.join(outdir, "checkpoint_saturation.png"), dpi=150)
print(f"Saved checkpoint_saturation.png")
plt.close(fig)

# ── Print summary table ──────────────────────────────────────────────

print(f"\n{'N':>14}  {'k':>6}  {'branch':>8}  {'pe':>6}  {'po':>6}  "
      f"{'empty':>8}  {'occ':>8}  {'fill%':>7}  {'wall%':>7}")
print("─" * 85)

for N in Ns:
    for k_val in [144, 216, 729]:
        if (N, k_val) not in data:
            continue
        d = data[(N, k_val)]
        occ = d["branch"] + d["pure_even"] + d["pure_odd"]
        k2 = k_val * k_val
        fill = occ / k2 * 100 if k2 > 0 else 0
        wall = d["pure_even"] / occ * 100 if occ > 0 else 0
        print(f"{N:>14}  {k_val:>6}  {d['branch']:>8}  {d['pure_even']:>6}  "
              f"{d['pure_odd']:>6}  {d['empty']:>8}  {occ:>8}  {fill:>6.1f}%  {wall:>6.2f}%")
    if N != Ns[-1]:
        print()
