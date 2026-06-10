#!/usr/bin/env python3
"""Very-high-resolution (D, eps) phase diagram: 2000x1500 cells, 24 directions,
400 tilts. Consumes ln lambda(D, omega, t) from vhires_phase.c, which uses the
EXACT quantized state space (B_j confined to <= floor(2D)+1 integers around
j*log2(3)) -- no delta-grid discretization of the state variable at all, so
every feature in this figure is arithmetic, not a rounding artifact.

Legendre step: theta(D,eps) = max_omega min_t [ ln lambda(D,omega,t) - t*eps ] / ln 2.
"""
import numpy as np, math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ND, NW, NT = 2000, 24, 400
LN2 = math.log(2.0)
Ds = np.linspace(0.6, 6.0, ND)
eps_grid = np.linspace(0.0, 0.6, 1500)
ts = np.concatenate([[0.0], np.geomspace(0.2, 20.0, NT - 1)])

lnlam = np.fromfile('results/vhires_lnlam.bin').reshape(ND, NW, NT)

# sanity: t=0 column must be omega-independent and match exact counts
t0 = lnlam[:, :, 0]
assert np.max(t0.max(1) - t0.min(1)) < 1e-12
print("validation theta(D) at t=0:")
for Dq, ref in [(1.0, 0.828), (1.2, 0.972), (1.2463, 0.992), (2.0, 1.258)]:
    di = int(np.argmin(abs(Ds - Dq)))
    print(f"  D={Ds[di]:.4f}: theta={t0[di,0]/LN2:.4f} (exact_count ref ~{ref})")

# Legendre transform, vectorized over D and omega per eps
RATE = np.empty((len(eps_grid), ND))
for ei, eps in enumerate(eps_grid):
    RATE[ei] = np.min(lnlam - ts * eps, axis=2).max(axis=1)
TH = RATE / LN2
np.savez_compressed('results/phase_diagram_vhires.npz',
                    Ds=Ds, eps=eps_grid, TH=TH.astype(np.float32))

# refined D* on the eps=0 axis (theta = 1 crossing)
i = int(np.searchsorted(TH[0], 1.0))
Dstar = Ds[i-1] + (Ds[i]-Ds[i-1])*(1.0-TH[0,i-1])/(TH[0,i]-TH[0,i-1])
print(f"D* (theta=1 on eps=0 axis) = {Dstar:.4f}, band ratio = {2**(2*Dstar):.3f}")

fig, ax = plt.subplots(figsize=(12, 7.5))
pm = ax.pcolormesh(Ds, eps_grid, TH, cmap='RdBu_r', vmin=0.0, vmax=1.6,
                   shading='auto', rasterized=True)
cb = fig.colorbar(pm, ax=ax)
cb.set_label(r'$\theta(D,\varepsilon)=\log_2\lambda_{\rm eff}$')
bnd = ax.contour(Ds, eps_grid, TH, levels=[1.0], colors='k', linewidths=2.2)
ax.clabel(bnd, fmt={1.0: r'$\lambda_{\rm eff}=2$'}, fontsize=9)
ax.contour(Ds, eps_grid, TH, levels=[1/(13.3+1)], colors='purple',
           linewidths=1.4, linestyles='--')
ax.text(0.63, 0.025, r'$\theta=1/(\tau{+}1)$: full Baker exclusion',
        color='purple', fontsize=8, rotation=90)
ax.axvline(Dstar, color='k', ls='--', lw=0.9, alpha=0.6)
ax.annotate(rf'$D^*={Dstar:.4f}$', xy=(Dstar, 0.57), xytext=(1.5, 0.575),
            fontsize=9, arrowprops=dict(arrowstyle='->', lw=0.8))
ax.text(0.85, 0.30, 'EXCLUDED\nany bias', fontsize=10, color='navy',
        ha='center', fontweight='bold')
ax.text(4.0, 0.545, 'EXCLUDED by bias', fontsize=10, color='navy', ha='center',
        fontweight='bold')
ax.text(4.0, 0.12, 'ALLOWED by counting\n(wide bands, low local bias)',
        fontsize=10, color='darkred', ha='center')
ax.scatter([3.4], [0.21], marker='d', s=60, color='crimson', zorder=5)
ax.annotate('pilot candidates', xy=(3.4, 0.21), xytext=(4.3, 0.26), fontsize=8,
            color='crimson', arrowprops=dict(arrowstyle='->', lw=0.7, color='crimson'))
ax.set_xlabel('strip half-width $D$  (band ratio $W=2^{2D}$)')
ax.set_ylabel(r'ord-3 shadow bias $\varepsilon$')
ax.set_title(r'The $(D,\varepsilon)$ phase diagram'
             '\n(2000$\\times$1500 cells, 24 directions, 400 tilts, '
             'exact quantized states — no $\\delta$-grid)')
fig.tight_layout()
fig.savefig('viz/fig5_phase_diagram_vhires.png', dpi=200)
print("wrote viz/fig5_phase_diagram_vhires.png")
