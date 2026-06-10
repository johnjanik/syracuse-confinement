#!/usr/bin/env python3
"""
Frontier visualization: candidate counterexamples vs typical trajectories,
repellers (negative-cycle ghosts), and typical ghosts (Sturmian).
Generates 4 PNG figures in the style of the old c_scripts plots.
Usage: python3 plot_frontier.py [output_dir]
"""
import sys, os, math, random
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

out = sys.argv[1] if len(sys.argv) > 1 else '.'
LOG2_3 = 1.58496250072115618
rng = np.random.default_rng(7)
random.seed(7)

def orbit_word(x, n):
    w, xs = [], [x]
    for _ in range(n):
        y = 3*x + 1; b = 0
        while y % 2 == 0: y //= 2; b += 1
        w.append(b); x = y; xs.append(x)
        if x == 1: break
    return w, xs

def signed_orbit_word(x, n):
    w, xs = [], [x]
    for _ in range(n):
        y = 3*x + 1; b = 0
        while y % 2 == 0: y //= 2; b += 1
        w.append(b); x = y; xs.append(x)
    return w, xs

def realize_prefix_reps(bs):
    reps = []
    r, Mb = 1, 1; A = 0; B = 0; P3 = 1
    for b in bs:
        need = B + b; mod = 1 << (need+1)
        c = (3*A + (1 << B)) % mod
        x0 = (pow((3*P3) % mod, -1, mod) * (((1 << need) - c) % mod)) % mod
        if need + 1 > Mb:
            r = x0; Mb = need + 1
        A = 3*A + (1 << B); P3 *= 3; B += b
        reps.append((B, r.bit_length(), Mb))
    return reps

ALPHA = 2 - LOG2_3
def sturmian(theta, N):
    return [1 if ((n*ALPHA + theta) % 1.0) < ALPHA else 2 for n in range(N)]

def candidate(M):
    law = {1: 0.567, 2: 0.357, 4: 0.076}
    bs = list(law); ps = np.array([law[b] for b in bs]); ps /= ps.sum()
    w = [int(b) for b in rng.choice(bs, size=M, p=ps)]
    S = sum(w) - LOG2_3*M; i = 0
    while abs(S) > 2 and i < M:
        if S > 2 and w[i] > 1: S -= w[i]-1; w[i] = 1
        elif S < -2 and w[i] == 1: S += 1; w[i] = 2
        i += 1
    return w

def theta_profile(w):
    return np.concatenate([[0.0], np.cumsum([LOG2_3 - b for b in w])])

# Fig 1: trajectory zoo
fig, ax = plt.subplots(figsize=(10, 6))
N = 220
for k in range(7):
    x0 = random.randrange(10**28, 10**29)*2 + 1
    w, xs = orbit_word(x0, N)
    ax.plot(range(len(xs)), [math.log2(x) for x in xs], color='0.65', lw=0.9,
            label='typical orbits (descend at $2-\\log_2 3$)' if k == 0 else None)
for k in range(5):
    w = candidate(N)
    ax.plot(range(N+1), 95 + theta_profile(w), color='crimson', lw=1.3, alpha=0.85,
            label='candidate counterexamples (calibrated, biased)' if k == 0 else None)
for k, th in enumerate((0.13, 0.5, 0.86)):
    w = sturmian(th, N)
    ax.plot(range(N+1), 95 + theta_profile(w), color='royalblue', lw=1.1, alpha=0.9,
            label='Sturmian ghosts (bounded band) — EXCLUDED' if k == 0 else None)
w1 = [1]*N
ax.plot(range(N+1), 95 + theta_profile(w1), color='darkorange', lw=1.6, ls='--',
        label='all-ones repeller ($x=-1$ ghost, slope $\\log_2 3-1$)')
w5, _ = signed_orbit_word(-5, N)
ax.plot(range(N+1), 95 + theta_profile(w5), color='green', lw=1.4, ls=':',
        label='negative cycles $-5,-17$ (periodic ghosts)')
w17, _ = signed_orbit_word(-17, N)
ax.plot(range(N+1), 95 + theta_profile(w17), color='green', lw=1.0, ls=':', alpha=0.7)
ax.axhline(95, color='k', lw=0.5, alpha=0.4)
ax.set_xlabel('accelerated step $n$'); ax.set_ylabel('$\\log_2 x_n$')
ax.set_title('Trajectory zoo: typical / candidates / ghosts / repellers')
ax.legend(fontsize=8, loc='lower left'); fig.tight_layout()
fig.savefig(os.path.join(out, 'fig1_trajectory_zoo.png'), dpi=140); plt.close(fig)

# Fig 2: ghost signature
fig, ax = plt.subplots(figsize=(10, 6))
x0 = random.randrange(10**14, 10**15)*2 + 1
w_real, _ = orbit_word(x0, 160)
reps = realize_prefix_reps(w_real)
ax.plot([m for _, _, m in reps], [bl for _, bl, _ in reps], color='0.3', lw=2.0,
        label=f'realizable word (orbit of integer, stabilizes at $\\log_2 x_0\\approx{math.log2(x0):.0f}$)')
for k, th in enumerate((0.13, 0.5, 0.86)):
    reps = realize_prefix_reps(sturmian(th, 160))
    ax.plot([m for _, _, m in reps], [bl for _, bl, _ in reps], color='royalblue', lw=1.0, alpha=0.85,
            label='Sturmian ghosts (ride the diagonal)' if k == 0 else None)
for k in range(4):
    reps = realize_prefix_reps(candidate(160))
    ax.plot([m for _, _, m in reps], [bl for _, bl, _ in reps], color='crimson', lw=1.0, alpha=0.85,
            label='candidate counterexamples — all ghosts (pilot: 120/120)' if k == 0 else None)
reps = realize_prefix_reps([1]*160)
ax.plot([m for _, _, m in reps], [bl for _, bl, _ in reps], color='darkorange', lw=1.6, ls='--',
        label='all-ones word ($x\\equiv-1$: ceiling $2^{B+1}-1$)')
reps = realize_prefix_reps([1, 2]*80)
ax.plot([m for _, _, m in reps], [bl for _, bl, _ in reps], color='green', lw=1.4, ls=':',
        label='$(1,2)^\\infty$ word ($x=-5$ cycle ghost)')
ax.plot([0, 420], [0, 420], color='k', lw=0.6, alpha=0.5)
ax.text(300, 318, 'ghost diagonal $r\\sim 2^{B_N}$', rotation=37, fontsize=8, alpha=0.7)
ax.set_xlabel('prefix modulus bits  $B_N+1$')
ax.set_ylabel('least positive representative bits')
ax.set_title('The ghost signature: realizable words stabilize; ghosts ride the diagonal')
ax.legend(fontsize=8, loc='upper left'); fig.tight_layout()
fig.savefig(os.path.join(out, 'fig2_ghost_signature.png'), dpi=140); plt.close(fig)

# Fig 3: phase map
fig, ax = plt.subplots(figsize=(10, 6))
z = np.exp(2j*np.pi/3)
G = sum(2.0**-b * z**-b for b in range(1, 60))
def wbias(w): return abs(np.mean([z**(-b) for b in w]) - G)
M = 64
pts_t = []
for _ in range(40):
    xs0 = random.randrange(10**40, 10**41)*2+1
    w, _ = orbit_word(xs0, 400)
    for s in range(0, len(w)-M, M):
        pts_t.append((np.mean(w[s:s+M]), wbias(w[s:s+M])))
pts_t = np.array(pts_t)
ax.scatter(pts_t[:,0], pts_t[:,1], s=8, color='0.6', alpha=0.5, label='typical orbit windows')
pts_c = np.array([(np.mean(c), wbias(c)) for c in (candidate(M) for _ in range(150))])
ax.scatter(pts_c[:,0], pts_c[:,1], s=14, color='crimson', alpha=0.8, label='candidate counterexamples')
pts_s = np.array([(np.mean(s_), wbias(s_)) for s_ in (sturmian(rng.random(), M) for _ in range(60))])
ax.scatter(pts_s[:,0], pts_s[:,1], s=14, color='royalblue', alpha=0.8, label='Sturmian ghosts (excluded)')
ax.scatter([1.0], [wbias([1]*M)], s=110, color='darkorange', marker='*', label='all-ones repeller')
ax.scatter([1.5], [wbias([1,2]*32)], s=110, color='green', marker='*', label='$-5$ cycle ghost')
ax.scatter([2.0], [wbias([2]*M)], s=110, color='k', marker='*', label='trivial cycle')
ax.axvline(LOG2_3, color='k', lw=1.0, ls='--', alpha=0.7)
ax.text(LOG2_3+0.01, 0.95, 'criticality $\\log_2 3$', fontsize=8)
ax.axvline(2.0, color='k', lw=0.6, ls=':', alpha=0.6)
ax.text(2.01, 0.95, 'stationary mean', fontsize=8)
ax.axvspan(LOG2_3, 2.65, color='green', alpha=0.05)
ax.text(2.22, 0.55, 'C1: mean-visible\n$\\Rightarrow$ descent', fontsize=9, color='darkgreen')
ax.annotate('counterexamples must live here:\ncalibrated + biased + full complexity (Fig 4)',
            xy=(1.585, 0.30), xytext=(1.05, 0.72), fontsize=9, color='crimson',
            arrowprops=dict(arrowstyle='->', color='crimson', lw=1.0))
ax.set_xlabel('window mean letter  $\\frac{1}{M}\\sum b_n$')
ax.set_ylabel('non-coboundary shadow bias  $|D_3|$')
ax.set_title('Phase map: where a counterexample must live')
ax.legend(fontsize=8, loc='center right'); fig.tight_layout()
fig.savefig(os.path.join(out, 'fig3_phase_map.png'), dpi=140); plt.close(fig)

# Fig 4: complexity vs rigidity threshold
fig, ax = plt.subplots(figsize=(10, 6))
Mw = 360
def Pp(w, p): return len({tuple(w[i:i+p]) for i in range(len(w)-p+1)})
ps = list(range(1, 19))
w, _ = orbit_word(random.randrange(10**60, 10**61)*2+1, Mw)
ax.semilogy(ps, [Pp(w, p) for p in ps], 'o-', color='0.4', label='typical orbit word')
ax.semilogy(ps, [Pp(sturmian(0.37, Mw), p) for p in ps], 's-', color='royalblue',
            label='Sturmian ($P(p)=p+1$) — EXCLUDED')
ax.semilogy(ps, [Pp(candidate(Mw), p) for p in ps], 'd-', color='crimson',
            label='candidate counterexample')
ax.semilogy(ps, [min(Mw-p+1, 2**p) for p in ps], 'k--', lw=1.0,
            label='repetition-rigidity demand $P(p)\\geq M-p+1$ (banded windows)')
ax.fill_between(ps, 1, [min(Mw-p+1, 2**p) for p in ps], color='royalblue', alpha=0.06)
ax.text(11, 6, 'DEAD ZONE\n(repeated blocks are cycles)', fontsize=9, color='navy', ha='center')
ax.set_xlabel('block length $p$'); ax.set_ylabel('factor complexity $P(p)$')
ax.set_title('Complexity profiles vs the repetition-rigidity threshold ($M=%d$)' % Mw)
ax.legend(fontsize=8, loc='upper left'); fig.tight_layout()
fig.savefig(os.path.join(out, 'fig4_complexity.png'), dpi=140); plt.close(fig)

print("wrote 4 figures to", out)
