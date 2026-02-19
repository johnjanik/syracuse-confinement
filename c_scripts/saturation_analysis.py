#!/usr/bin/env python3
"""
Saturation analysis from branch_summary.csv.

Extracts:
1. Cross-k saturation profile (fill fraction per level)
2. Historical branch count growth at k=144 with model fits
3. Saturation predictions
4. Wall density analysis
"""

import csv
import math
import sys

# ── Read branch_summary.csv ──────────────────────────────────────────

rows = []
with open("branch_summary.csv") as f:
    reader = csv.DictReader(f)
    for r in reader:
        row = {
            "k": int(r["k"]),
            "a": int(r["a"]),
            "b": int(r["b"]),
            "total_visits": int(r["total_visits"]),
            "branch": int(r["branch_cells"]),
            "pure_even": int(r["pure_even"]),
            "pure_odd": int(r["pure_odd"]),
            "empty": int(r["empty"]),
            "mean_p_odd": float(r["mean_p_odd"]),
        }
        row["k2"] = row["k"] ** 2
        row["occupied"] = row["branch"] + row["pure_even"] + row["pure_odd"]
        row["fill_frac"] = row["occupied"] / row["k2"] if row["k2"] > 0 else 0
        row["branch_frac"] = row["branch"] / row["k2"] if row["k2"] > 0 else 0
        rows.append(row)

# ── 1. Cross-k saturation profile ────────────────────────────────────

print("=" * 90)
print("CROSS-k SATURATION PROFILE (N = 10^10)")
print("=" * 90)
print(f"{'k':>6}  {'(a,b)':>8}  {'k^2':>8}  {'branch':>8}  {'p_even':>8}  "
      f"{'p_odd':>8}  {'empty':>8}  {'fill%':>8}  {'status':>12}")
print("─" * 90)

for r in rows:
    status = "SATURATED" if r["empty"] == 0 and r["pure_even"] == 0 and r["pure_odd"] == 0 else \
             "ALL-BRANCH" if r["empty"] == 0 else \
             "PARTIAL" if r["fill_frac"] > 0.5 else \
             "STRIP"
    print(f"{r['k']:>6}  (2^{r['a']}·3^{r['b']}){'':<{4-len(str(r['a']))-len(str(r['b']))}}"
          f"  {r['k2']:>8}  {r['branch']:>8}  {r['pure_even']:>8}  "
          f"{r['pure_odd']:>8}  {r['empty']:>8}  {r['fill_frac']:>7.1%}  {status:>12}")

# ── 2. Saturation frontier ───────────────────────────────────────────

print("\n" + "=" * 90)
print("SATURATION FRONTIER")
print("=" * 90)

# Find the largest k that is fully saturated (all branch, no other types)
saturated_ks = [r["k"] for r in rows if r["empty"] == 0 and r["pure_even"] == 0 and r["pure_odd"] == 0]
all_branch_ks = [r["k"] for r in rows if r["empty"] == 0]
partial_ks = [r["k"] for r in rows if r["empty"] > 0 and r["fill_frac"] > 0.3]

print(f"  Fully saturated (100% branch):  k ≤ {max(saturated_ks)} ({len(saturated_ks)} levels)")
if all_branch_ks and max(all_branch_ks) > max(saturated_ks):
    print(f"  All cells occupied (branch+walls): k ≤ {max(all_branch_ks)}")
print(f"  Partially filled (>30%):        {[r['k'] for r in rows if r['empty'] > 0 and r['fill_frac'] > 0.3]}")
print(f"  Strip regime (<30%):            k ≥ {min(r['k'] for r in rows if r['fill_frac'] < 0.3)}")

# ── 3. Resolution-independent counts ─────────────────────────────────

print("\n" + "=" * 90)
print("RESOLUTION-INDEPENDENT COUNTS (frozen across k)")
print("=" * 90)

# Find where branch count stabilizes
branch_counts = [(r["k"], r["branch"], r["pure_even"], r["pure_odd"]) for r in rows if r["k"] >= 144]
print(f"  {'k':>6}  {'branch':>8}  {'pure_even':>8}  {'pure_odd':>8}  {'occupied':>8}")
print("  " + "─" * 50)
for k, b, pe, po in branch_counts:
    print(f"  {k:>6}  {b:>8}  {pe:>8}  {po:>8}  {b+pe+po:>8}")

# Check if frozen
frozen_branch = branch_counts[-1][1]
frozen_pe = branch_counts[-1][2]
frozen_po = branch_counts[-1][3]
freeze_k = None
for k, b, pe, po in branch_counts:
    if b == frozen_branch and pe == frozen_pe and po == frozen_po:
        if freeze_k is None:
            freeze_k = k
    else:
        freeze_k = None

if freeze_k:
    print(f"\n  Counts freeze at k ≥ {freeze_k}:")
    print(f"    branch = {frozen_branch}, pure_even = {frozen_pe}, pure_odd = {frozen_po}")
    print(f"    occupied = {frozen_branch + frozen_pe + frozen_po}")

# ── 4. Historical branch count growth (k=144) ────────────────────────

print("\n" + "=" * 90)
print("BRANCH COUNT GROWTH AT k=144")
print("=" * 90)

# Historical data points
# Note: The N=10^8 and N=10^9 values (9415, 13688) are from documentation.
# The N=10^10 value is from branch_summary.csv (actual branch_cells count).
# Previous docs used 16,371 which was actually the successor-type count,
# not the branch cell count. The CSV value 16,954 is definitive.
k144_row = next(r for r in rows if r["k"] == 144)
current_branch = k144_row["branch"]

historical = [
    (1e8,  9415,  "100M run"),
    (1e9,  13688, "1B run"),
    (1e10, current_branch, "10B run (CSV)"),
]

print(f"\n  {'N':>12}  {'branch':>8}  {'source':>20}")
print("  " + "─" * 45)
for N, b, src in historical:
    print(f"  {N:>12.0f}  {b:>8}  {src:>20}")

# Fit log model: B(N) = a * ln(N) + b
# Using least squares on 3 points
xs = [math.log(N) for N, _, _ in historical]
ys = [b for _, b, _ in historical]

n = len(xs)
sx = sum(xs)
sy = sum(ys)
sxx = sum(x*x for x in xs)
sxy = sum(x*y for x, y in zip(xs, ys))

a_log = (n * sxy - sx * sy) / (n * sxx - sx * sx)
b_log = (sy - a_log * sx) / n

print(f"\n  Log fit: B(N) = {a_log:.1f} · ln(N) + ({b_log:.0f})")
print(f"          B(N) = {a_log * math.log(10):.1f} · log₁₀(N) + ({b_log:.0f})")

# Fit power law: B(N) = c * N^alpha  => ln(B) = ln(c) + alpha * ln(N)
lys = [math.log(b) for _, b, _ in historical]
slys = sum(lys)
sxlys = sum(x * ly for x, ly in zip(xs, lys))

alpha = (n * sxlys - sx * slys) / (n * sxx - sx * sx)
ln_c = (slys - alpha * sx) / n
c_pow = math.exp(ln_c)

print(f"\n  Power fit: B(N) = {c_pow:.2f} · N^{alpha:.4f}")

# Residuals
print(f"\n  {'N':>12}  {'actual':>8}  {'log_pred':>8}  {'log_err':>8}  "
      f"{'pow_pred':>8}  {'pow_err':>8}")
print("  " + "─" * 60)
for N, b_actual, _ in historical:
    log_pred = a_log * math.log(N) + b_log
    pow_pred = c_pow * N ** alpha
    print(f"  {N:>12.0f}  {b_actual:>8}  {log_pred:>8.0f}  {log_pred - b_actual:>+8.0f}  "
          f"  {pow_pred:>8.0f}  {pow_pred - b_actual:>+8.0f}")

# Predictions
print(f"\n  Predictions:")
for Npred in [1e11, 1e12, 1e13, 1e14]:
    log_p = a_log * math.log(Npred) + b_log
    pow_p = c_pow * Npred ** alpha
    print(f"    N = 10^{int(math.log10(Npred)):>2}: log → {log_p:,.0f},  power → {pow_p:,.0f}")

# ── 5. Saturation predictions for k=144 ──────────────────────────────

print("\n" + "=" * 90)
print("SATURATION PREDICTION FOR k=144")
print("=" * 90)

k144_total = 144 * 144  # = 20,736
k144_occupied = k144_row["occupied"]
k144_empty = k144_row["empty"]

print(f"  Total cells: {k144_total}")
print(f"  Currently occupied: {k144_occupied} ({k144_occupied/k144_total:.1%})")
print(f"  Empty: {k144_empty} ({k144_empty/k144_total:.1%})")
print(f"  Need ~{k144_total - k144_occupied} more cells to saturate")

# Using log model: when does occupied reach k^2?
# Approximation: assume occupied grows proportionally to branch count
# Current ratio: occupied/branch ≈ constant
occ_branch_ratio = k144_occupied / k144_row["branch"]
print(f"\n  occupied/branch ratio: {occ_branch_ratio:.4f}")
print(f"  Need branch ≈ {k144_total / occ_branch_ratio:.0f} for full saturation")
target_branch = k144_total / occ_branch_ratio
# Solve: a_log * ln(N) + b_log = target_branch
if a_log > 0:
    ln_N_sat = (target_branch - b_log) / a_log
    N_sat = math.exp(ln_N_sat)
    print(f"  Log model: saturation at N ≈ {N_sat:.2e} (10^{math.log10(N_sat):.1f})")

# ── 6. Wall analysis ─────────────────────────────────────────────────

print("\n" + "=" * 90)
print("WALL ANALYSIS (Pure-Even Cells)")
print("=" * 90)

wall_levels = [(r["k"], r["pure_even"], r["pure_odd"], r["branch"], r["occupied"])
               for r in rows if r["pure_even"] > 0 or r["pure_odd"] > 0]

if wall_levels:
    print(f"\n  {'k':>6}  {'pure_even':>10}  {'pure_odd':>10}  {'branch':>8}  "
          f"{'wall_frac':>10}  {'wall/occ':>10}")
    print("  " + "─" * 65)
    for k, pe, po, br, occ in wall_levels:
        wall_frac = pe / (k * k) if k > 0 else 0
        wall_occ = pe / occ if occ > 0 else 0
        print(f"  {k:>6}  {pe:>10}  {po:>10}  {br:>8}  "
              f"  {wall_frac:>8.2%}    {wall_occ:>8.2%}")
else:
    print("  No walls detected at any level.")

# Wall fraction among occupied cells
print(f"\n  Key ratios at k=144:")
k144 = k144_row
print(f"    pure_even / occupied = {k144['pure_even']} / {k144['occupied']} = {k144['pure_even']/k144['occupied']:.4f}")
print(f"    pure_odd  / occupied = {k144['pure_odd']} / {k144['occupied']} = {k144['pure_odd']/k144['occupied']:.4f}")
print(f"    branch    / occupied = {k144['branch']} / {k144['occupied']} = {k144['branch']/k144['occupied']:.4f}")

# ── 7. Cross-k cell count breakdown (for levels with walls) ──────────

print("\n" + "=" * 90)
print("CELL TYPE BREAKDOWN: TRANSITION ZONE (k ≥ 144)")
print("=" * 90)

transition = [r for r in rows if r["k"] >= 108]
print(f"\n  {'k':>6}  {'k^2':>8}  {'branch':>8}  {'p_even':>8}  {'p_odd':>6}  "
      f"{'empty':>8}  {'br/occ':>7}  {'pe/occ':>7}  {'po/occ':>7}")
print("  " + "─" * 80)
for r in transition:
    occ = r["occupied"]
    if occ > 0:
        print(f"  {r['k']:>6}  {r['k2']:>8}  {r['branch']:>8}  {r['pure_even']:>8}  "
              f"{r['pure_odd']:>6}  {r['empty']:>8}  "
              f"{r['branch']/occ:>7.4f}  {r['pure_even']/occ:>7.4f}  {r['pure_odd']/occ:>7.4f}")
    else:
        print(f"  {r['k']:>6}  {r['k2']:>8}  {r['branch']:>8}  {r['pure_even']:>8}  "
              f"{r['pure_odd']:>6}  {r['empty']:>8}  {'—':>7}  {'—':>7}  {'—':>7}")

print()
