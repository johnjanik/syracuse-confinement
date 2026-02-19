#!/usr/bin/env python3
"""
Companion plotting script for parity_sft (C version).
Reads CSV data files written by ./parity_sft and generates
the same 4 PNG figures as the original Python script.

Usage: python3 plot_parity_sft.py [data_dir] [output_dir]
  data_dir   - directory containing CSV files (default: .)
  output_dir - directory for PNG output   (default: .)
"""

import sys
import os
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

data_dir   = sys.argv[1] if len(sys.argv) > 1 else '.'
output_dir = sys.argv[2] if len(sys.argv) > 2 else '.'

def load_csv(name):
    return np.genfromtxt(os.path.join(data_dir, name),
                         delimiter=',', names=True)

def load_params():
    params = {}
    with open(os.path.join(data_dir, 'parity_params.csv')) as f:
        for line in f:
            k, v = line.strip().split(',', 1)
            try:
                params[k] = int(v)
            except ValueError:
                params[k] = float(v)
    return params

# ── Load data ────────────────────────────────────────────────────────

ac   = load_csv('parity_autocorr.csv')
ent  = load_csv('parity_entropy.csv')
par  = load_params()
N    = par['N']

MAX_ORDER = len(ent)

# Load transition matrices
matrices = {}
for m in range(1, MAX_ORDER + 1):
    fname = os.path.join(data_dir, f'parity_matrix_m{m}.csv')
    matrices[m] = np.loadtxt(fname, delimiter=',')

# ── Figure 1: Autocorrelation comparison ─────────────────────────────

fig, axes = plt.subplots(1, 2, figsize=(16, 6))
lags = ac['lag'].astype(int)
C_emp = ac['C_emp']

colors = ['#e41a1c', '#377eb8', '#4daf4a', '#984ea3', '#ff7f00']

ax = axes[0]
ax.plot(lags, C_emp, 'ko-', linewidth=2, markersize=5,
        label='Empirical', zorder=10)
for m in range(1, MAX_ORDER + 1):
    col_name = f'C_exact_{m}'
    ax.plot(lags, ac[col_name], 's--', color=colors[m-1],
            linewidth=1.5, markersize=3,
            label=f'Order-{m} Markov', alpha=0.8)
ax.axhline(y=0, color='gray', linewidth=0.5)
ax.set_xlabel('Lag k')
ax.set_ylabel('C(k)')
ax.set_title('Autocorrelation of Parity Sequence')
ax.legend(fontsize=8)
ax.grid(True, alpha=0.3)

ax = axes[1]
for m in range(1, MAX_ORDER + 1):
    col_name = f'C_exact_{m}'
    residuals = np.abs(C_emp[1:] - ac[col_name][1:])
    ax.plot(lags[1:], residuals, 'o-', color=colors[m-1],
            linewidth=1.5, markersize=4, label=f'|dC| order {m}')
ax.set_xlabel('Lag k')
ax.set_ylabel('|C_emp(k) - C_model(k)|')
ax.set_title('Residual Autocorrelation (not captured by model)')
ax.legend(fontsize=8)
ax.set_yscale('log')
ax.grid(True, alpha=0.3)

fig.suptitle(f'Parity Sequence Autocorrelation: Empirical vs Markov Models\n'
             f'N = {N:,}', fontsize=13)
fig.tight_layout(rect=[0, 0, 1, 0.94])
out = os.path.join(output_dir, 'parity_autocorrelation.png')
fig.savefig(out, dpi=150, bbox_inches='tight')
plt.close(fig)
print(f'  Saved {out}')


# ── Figure 2: Transition matrices as heatmaps ───────────────────────

fig, axes = plt.subplots(1, MAX_ORDER, figsize=(4 * MAX_ORDER, 4.5))

for m_idx, m in enumerate(range(1, MAX_ORDER + 1)):
    ax = axes[m_idx]
    M_mat = matrices[m]
    n_states = M_mat.shape[0]

    im = ax.imshow(M_mat, cmap='YlOrRd', vmin=0, vmax=1,
                   aspect='equal', interpolation='nearest')

    if n_states <= 16:
        labels = [format(i, f'0{m}b') for i in range(n_states)]
        ax.set_xticks(range(n_states))
        ax.set_xticklabels(labels, rotation=90, fontsize=max(5, 9 - m))
        ax.set_yticks(range(n_states))
        ax.set_yticklabels(labels, fontsize=max(5, 9 - m))
    else:
        ax.set_xticks([])
        ax.set_yticks([])

    ax.set_title(f'Order {m}  ({n_states}x{n_states})', fontsize=10)
    ax.set_xlabel('To')
    if m_idx == 0:
        ax.set_ylabel('From')
    plt.colorbar(im, ax=ax, shrink=0.8)

fig.suptitle('State-to-State Transition Matrices $M_{ij}$\n'
             'Zeros (dark) = forbidden transitions defining the SFT',
             fontsize=13)
fig.tight_layout(rect=[0, 0, 1, 0.92])
out = os.path.join(output_dir, 'parity_transition_matrices.png')
fig.savefig(out, dpi=150, bbox_inches='tight')
plt.close(fig)
print(f'  Saved {out}')


# ── Figure 3: Entropy convergence ───────────────────────────────────

fig, ax = plt.subplots(1, 1, figsize=(8, 5))

orders = ent['order'].astype(int)
h_tops  = ent['h_top']
h_meass = ent['h_meas']

phi = (1 + np.sqrt(5)) / 2

ax.plot(orders, h_tops, 'o-', color='firebrick', linewidth=2,
        markersize=6, label='Topological entropy $h_{top}$')
ax.plot(orders, h_meass, 's-', color='steelblue', linewidth=2,
        markersize=6, label=r'Measure entropy $h_\mu$')
ax.axhline(y=np.log2(phi), color='firebrick', linestyle='--', alpha=0.4,
           label=f'log2(phi) = {np.log2(phi):.4f} (golden mean shift)')
ax.set_xlabel('Markov order m')
ax.set_ylabel('Entropy (bits/step)')
ax.set_title('Entropy Convergence with Markov Order')
ax.legend()
ax.grid(True, alpha=0.3)
ax.set_xticks(list(orders))

fig.tight_layout()
out = os.path.join(output_dir, 'parity_entropy.png')
fig.savefig(out, dpi=150, bbox_inches='tight')
plt.close(fig)
print(f'  Saved {out}')


# ── Figure 4: The golden mean shift graph ───────────────────────────

fig, ax = plt.subplots(figsize=(6, 4))

ax.set_xlim(-0.5, 2.5)
ax.set_ylim(-0.8, 1.2)

circle0 = plt.Circle((0.5, 0.3), 0.3, fill=False,
                      linewidth=2, color='steelblue')
circle1 = plt.Circle((1.5, 0.3), 0.3, fill=False,
                      linewidth=2, color='coral')
ax.add_patch(circle0)
ax.add_patch(circle1)
ax.text(0.5, 0.3, '0\n(even)', ha='center', va='center',
        fontsize=11, fontweight='bold', color='steelblue')
ax.text(1.5, 0.3, '1\n(odd)', ha='center', va='center',
        fontsize=11, fontweight='bold', color='coral')

# Self-loop 0->0
angle = np.linspace(0.3, 2*np.pi - 0.3, 50)
r = 0.25
cx, cy = 0.5, 0.85
ax.plot(cx + r*np.cos(angle), cy + r*np.sin(angle),
        'steelblue', linewidth=1.5)
ax.annotate('', xy=(cx + r*np.cos(-0.3), cy + r*np.sin(-0.3)),
            xytext=(cx + r*np.cos(-0.1), cy + r*np.sin(-0.1)),
            arrowprops=dict(arrowstyle='->', color='steelblue', lw=1.5))
p0 = par['T_1_00']
ax.text(0.5, 1.18, f'P = {p0:.3f}', ha='center', fontsize=9,
        color='steelblue')

# Edge 0->1
ax.annotate('', xy=(1.2, 0.38), xytext=(0.8, 0.38),
            arrowprops=dict(arrowstyle='->', color='purple', lw=1.5))
p01 = par['T_1_01']
ax.text(1.0, 0.52, f'P = {p01:.3f}', ha='center', fontsize=9,
        color='purple')

# Edge 1->0
ax.annotate('', xy=(0.8, 0.22), xytext=(1.2, 0.22),
            arrowprops=dict(arrowstyle='->', color='green', lw=1.5))
ax.text(1.0, 0.02, 'P = 1.000', ha='center', fontsize=9, color='green')

# Forbidden edge 1->1
ax.text(1.85, 0.85, 'X  1->1', fontsize=12, color='red', fontweight='bold')
ax.text(1.85, 0.7, 'FORBIDDEN', fontsize=8, color='red')

ax.set_aspect('equal')
ax.axis('off')
ax.set_title('The Golden Mean Shift: Collatz Parity SFT\n'
             'After an odd step (3x+1), next step must be even (/2)',
             fontsize=11)

fig.tight_layout()
out = os.path.join(output_dir, 'golden_mean_shift.png')
fig.savefig(out, dpi=150, bbox_inches='tight')
plt.close(fig)
print(f'  Saved {out}')

print('\nDone.')
