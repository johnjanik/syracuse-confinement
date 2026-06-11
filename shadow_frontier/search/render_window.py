#!/usr/bin/env python3
"""Generic structure-hunting renderer for any phase-engine window.

Reads the engine's .meta sidecar (so grids always match), computes the
Legendre surface theta(D, eps) on a requested eps-window, and renders a
two-panel figure: theta with dense local contours, and |grad theta|.

Usage:
  python3 search/render_window.py --base results/kink15_lnlam \\
      --elo 0.25 --ehi 0.42 --out viz/fig7a_kink15.png --title "..."
"""
import argparse, math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ap = argparse.ArgumentParser()
ap.add_argument('--base', required=True)
ap.add_argument('--elo', type=float, default=0.0)
ap.add_argument('--ehi', type=float, default=0.6)
ap.add_argument('--neps', type=int, default=1500)
ap.add_argument('--out', required=True)
ap.add_argument('--title', default='')
a = ap.parse_args()

meta = dict(l.split()[:2] for l in open(a.base + '.meta')
            if len(l.split()) >= 2 and l.split()[0] in
            ('ND', 'NW', 'NT', 'P', 'BURN', 'DLO', 'DHI'))
ND, NW, NT = int(meta['ND']), int(meta['NW']), int(meta['NT'])
DLO, DHI, P = float(meta['DLO']), float(meta['DHI']), int(meta['P'])
Ds = np.linspace(DLO, DHI, ND)
ts = np.concatenate([[0.0], np.geomspace(0.2, 20.0, NT - 1)])
eps = np.linspace(a.elo, a.ehi, a.neps)

lnlam = np.fromfile(a.base + '.bin').reshape(ND, NW, NT)
assert np.max(lnlam[:, :, 0].max(1) - lnlam[:, :, 0].min(1)) < 1e-12, \
    "t=0 column not omega-independent: grid mismatch?"
TH = np.empty((a.neps, ND))
for ei, e in enumerate(eps):
    TH[ei] = np.min(lnlam - ts * e, axis=2).max(axis=1) / math.log(2)
np.savez_compressed(a.base + '_theta.npz', Ds=Ds, eps=eps,
                    TH=TH.astype(np.float32))

lo, hi = np.percentile(TH, 1), np.percentile(TH, 99)
step = max((hi - lo) / 45, 1e-4)
G = np.hypot(np.gradient(TH, axis=0) / (eps[1] - eps[0]),
             np.gradient(TH, axis=1) / (Ds[1] - Ds[0]))

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 6.5), sharey=True)
pm = ax1.pcolormesh(Ds, eps, TH, cmap='RdBu_r', vmin=lo, vmax=hi,
                    shading='auto', rasterized=True)
fig.colorbar(pm, ax=ax1, label=r'$\theta(D,\varepsilon)$')
ax1.contour(Ds, eps, TH, levels=np.arange(math.floor(lo * 100) / 100,
            hi + step, step), colors='k', linewidths=0.35, alpha=0.55)
if lo < 1.0 < hi:
    ax1.contour(Ds, eps, TH, levels=[1.0], colors='k', linewidths=2.2)
for k in range(int(2 * DLO), int(2 * DHI) + 1):
    if DLO < k / 2 < DHI:
        ax1.axvline(k / 2, color='purple', ls=':', lw=1.0, alpha=0.8)
        ax2.axvline(k / 2, color='purple', ls=':', lw=1.0, alpha=0.8)
if a.elo < 0.44903 < a.ehi:
    for ax in (ax1, ax2):
        ax.axhline(0.44903, color='darkgreen', ls='-.', lw=1.2, alpha=0.9)
g99 = np.percentile(G, 99)
pm2 = ax2.pcolormesh(Ds, eps, np.minimum(G, g99), cmap='magma',
                     shading='auto', rasterized=True)
fig.colorbar(pm2, ax=ax2, label=r'$|\nabla\theta|$ (clipped at p99)')
ax1.set_xlabel('$D$'); ax2.set_xlabel('$D$')
ax1.set_ylabel(r'$\varepsilon$')
ax1.set_title(r'$\theta$, dense contours (step %.3f)' % step)
ax2.set_title(r'gradient magnitude — arithmetic features = ridges')
fig.suptitle(f'{a.title}   [{DLO},{DHI}]x[{a.elo},{a.ehi}], '
             f'ND={ND}, NT={NT}, P={P}', fontsize=11)
fig.tight_layout()
fig.savefig(a.out, dpi=200)
print(f"wrote {a.out}  (theta range [{TH.min():.4f}, {TH.max():.4f}], "
      f"local clip [{lo:.4f}, {hi:.4f}])")
