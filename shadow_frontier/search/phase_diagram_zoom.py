#!/usr/bin/env python3
"""Candidate-region zoom of the (D, eps) phase diagram.

The bracket (from the exact full-range data): a counterexample's banded
windows must satisfy D > D* = 1.246 and eps < eps*(D); eps*(D) reaches 95%
of saturation by D = 4.08. Zoom window [1.20, 4.20] x [0, 0.60] at
Delta-D = 0.001 (3000 D), 2000 eps values, 24 directions, 400 tilts,
p = 4000 exact quantized states.
"""
import numpy as np, math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ND, NW, NT = 3000, 24, 400
LN2 = math.log(2.0)
Ds = np.linspace(1.20, 4.20, ND)
eps_grid = np.linspace(0.0, 0.60, 2000)
ts = np.concatenate([[0.0], np.geomspace(0.2, 20.0, NT - 1)])

lnlam = np.fromfile('results/zoom_lnlam.bin').reshape(ND, NW, NT)
RATE = np.empty((len(eps_grid), ND))
for ei, eps in enumerate(eps_grid):
    RATE[ei] = np.min(lnlam - ts * eps, axis=2).max(axis=1)
TH = RATE / LN2
np.savez_compressed('results/phase_diagram_zoom.npz',
                    Ds=Ds, eps=eps_grid, TH=TH.astype(np.float32))

# refined D* and boundary
i = int(np.searchsorted(TH[0], 1.0))
Dstar = Ds[i-1] + (Ds[i]-Ds[i-1])*(1.0-TH[0,i-1])/(TH[0,i]-TH[0,i-1])
bnd = np.full(ND, np.nan)
for di in range(ND):
    col = TH[:, di]
    if col[0] < 1: bnd[di] = 0.0; continue
    j = np.where(col >= 1.0)[0]
    bnd[di] = eps_grid[j[-1]]
EBIN = 0.44903
icross = int(np.argmax(bnd >= EBIN))
print(f"D* = {Dstar:.5f}; boundary crosses the binary ceiling 0.449 at "
      f"D = {Ds[icross]:.4f}")
for q in (1.5, 2.0, 2.5, 3.0, 3.5, 4.0):
    di = int(np.argmin(abs(Ds-q)))
    sl_l = (bnd[di]-bnd[di-60])/(Ds[di]-Ds[di-60])
    sl_r = (bnd[di+60]-bnd[di])/(Ds[di+60]-Ds[di])
    print(f"  eps*({q}) = {bnd[di]:.4f}   kink slope jump {sl_r-sl_l:+.4f}")

fig, ax = plt.subplots(figsize=(13, 8))
pm = ax.pcolormesh(Ds, eps_grid, TH, cmap='RdBu_r', vmin=0.6, vmax=1.4,
                   shading='auto', rasterized=True)
cb = fig.colorbar(pm, ax=ax)
cb.set_label(r'$\theta(D,\varepsilon)=\log_2\lambda_{\rm eff}$')
bl = ax.contour(Ds, eps_grid, TH, levels=[1.0], colors='k', linewidths=2.4)
ax.clabel(bl, fmt={1.0: r'$\lambda_{\rm eff}=2$ (exclusion boundary)'},
          fontsize=9)
ax.contour(Ds, eps_grid, TH, levels=[0.9, 0.95, 1.05, 1.1], colors='k',
           linewidths=0.5, linestyles=':', alpha=0.6)
# the candidate region: D > D*, eps < eps*(D)
mask = np.zeros_like(TH, dtype=bool)
for di in range(ND):
    if Ds[di] > Dstar:
        mask[:, di] = eps_grid < bnd[di]
ax.contourf(Ds, eps_grid, mask.astype(float), levels=[0.5, 1.5],
            colors='none', hatches=['///'], alpha=0.0)
ax.axvline(Dstar, color='k', ls='--', lw=1.2)
ax.text(Dstar-0.015, 0.30, rf'$D^*={Dstar:.4f}$ — counting wall',
        rotation=90, fontsize=10, ha='right', va='center')
ax.axhline(EBIN, color='darkgreen', ls='-.', lw=1.4)
ax.text(2.52, EBIN+0.012, r'binary ceiling $\varepsilon_{\rm bin}=0.449$:'
        r' above this, windows must spend letters $b\geq 3$',
        color='darkgreen', fontsize=9,
        bbox=dict(facecolor='white', alpha=0.85, edgecolor='none', pad=1.5))
for q in (1.5, 2.0, 2.5, 3.0, 3.5, 4.0):
    di = int(np.argmin(abs(Ds-q)))
    ax.plot([q], [bnd[di]], marker='o', ms=4, color='purple', zorder=6)
ax.text(1.52, 0.355, 'kinks at $2D\\in\\mathbb{Z}$', color='purple',
        fontsize=8, rotation=20)
ax.scatter([3.4], [0.21], marker='d', s=70, color='crimson', zorder=6)
ax.annotate('pilot candidates (all ghosts)', xy=(3.4, 0.21),
            xytext=(3.55, 0.16), fontsize=9, color='crimson',
            bbox=dict(facecolor='white', alpha=0.85, edgecolor='none', pad=1.5),
            arrowprops=dict(arrowstyle='->', lw=0.8, color='crimson'))
ax.text(2.6, 0.07, 'CANDIDATE REGION\n(hatched): windows of a counterexample'
        '\nmust live here — and for letters $\\subset\\{1,2\\}$\nit is EMPTY '
        '($\\theta_{12}<0.9791$ at every $D$)',
        fontsize=10, color='darkred', ha='center',
        bbox=dict(facecolor='white', alpha=0.85, edgecolor='none', pad=2))
ax.text(1.35, 0.55, 'EXCLUDED\n(counting)', fontsize=10, color='navy',
        ha='center', fontweight='bold')
ax.text(3.3, 0.575, 'EXCLUDED (bias)', fontsize=10, color='navy',
        fontweight='bold')
ax.set_xlabel('strip half-width $D$  (band ratio $W=2^{2D}$)')
ax.set_ylabel(r'ord-3 shadow bias $\varepsilon$')
ax.set_title('The candidate region, bracketed: '
             rf'$[{Dstar:.3f},\,4.08]\times(0,\,\varepsilon^*(D)]$'
             '\n(3000$\\times$2000 cells, 24 directions, 400 tilts, '
             '$p=4000$ exact quantized states)')
fig.tight_layout()
fig.savefig('viz/fig6_candidate_region.png', dpi=210)
print("wrote viz/fig6_candidate_region.png")
