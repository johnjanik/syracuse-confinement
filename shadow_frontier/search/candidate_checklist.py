#!/usr/bin/env python3
"""Six-step checklist over a candidate batch + (D,eps) -> margin overlay.

Batch = 120 pilot ghost words (seed-1 stream) + survival champions
+ net-ascending integer windows harvested from random orbits.
Outputs a verdict table, any survivors, and viz/fig8_candidate_margins.png
(candidate windows on the phase diagram, colored by certificate margin).
"""
import math, random, sys
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
sys.path.insert(0, 'search')
from candidate_tools import orbit, diagnose, checklist
from frontier import biased_letter_law, gen_word, calibrate, realize

random.seed(20260611)
rows = []

def add(word, xs, label):
    d = diagnose(list(word), xs, label)
    c = checklist(d)
    finite = [m for m in d['margins'].values() if m != -math.inf]
    rows.append(dict(label=label, D=d['Dband'], eps=d['max_noncob'],
                     margin=(min(finite) if finite else -2.0),
                     mean_b=d['mean_b'], crat=d['complexity_ratio'],
                     verdict=c['verdict'],
                     fail=[k for k, v in c.items()
                           if k != 'verdict' and str(v).startswith('FAIL')]))

# pilots
rng = np.random.default_rng(1)
law, _ = biased_letter_law()
for k in range(120):
    w = calibrate(gen_word(law, 240, rng))
    r, Mb = realize(w)
    xs, w2 = orbit(r, len(w))
    fill = r.bit_length() / Mb
    add(w, xs, f"pilot{k:03d}" + ("(ghost)" if fill > 0.9 else ""))

# champions ({1,2}-survival prefixes)
for n0 in (27, 4591, 31911, 517191, 687871):
    x, w = n0, []
    while True:
        t = 3 * x + 1; b = (t & -t).bit_length() - 1
        if b > 2: break
        w.append(b); x = t >> b
    xs, _ = orbit(n0, len(w))
    add(w, xs, f"champ{n0}")

# harvested net-ascending integer windows
got = 0
while got < 60:
    x0 = random.randrange(1 << 48, 1 << 52) | 1
    xs, ws = orbit(x0, 3000)
    W = 80
    for s in range(0, 3000 - W, W // 2):
        seg = xs[s:s + W + 1]
        if seg[-1] >= 4 * seg[0] and min(seg) >= seg[0]:
            add(ws[s:s + W], seg, f"ascwin{got:02d}")
            got += 1
            if got >= 60: break

# report
print(f"{'label':12s} {'D':>6s} {'eps':>6s} {'margin':>8s} {'mean_b':>7s} "
      f"{'crat':>6s}  verdict / first failures")
surv = []
from collections import Counter
failc = Counter()
for r in rows:
    for f in r['fail']: failc[f] += 1
    if r['verdict'] == 'SURVIVOR': surv.append(r)
for r in rows[:8] + [r for r in rows if r['label'].startswith('champ')] \
         + rows[125:131]:
    print(f"{r['label']:12s} {r['D']:6.2f} {r['eps']:6.3f} "
          f"{r['margin']:8.3f} {r['mean_b']:7.3f} {r['crat']:6.3f}  "
          f"{r['verdict']} {','.join(r['fail'])}")
print(f"\nbatch = {len(rows)}; failure counts: {dict(failc)}")
print(f"SURVIVORS of all six checks: {len(surv)}")
for r in surv: print("  ", r)

# overlay
bg = np.load('results/phase_diagram_vhires.npz')
fig, ax = plt.subplots(figsize=(11, 7))
ax.pcolormesh(bg['Ds'], bg['eps'], bg['TH'].astype(float), cmap='RdBu_r',
              vmin=0, vmax=1.6, alpha=0.45, shading='auto', rasterized=True)
ax.contour(bg['Ds'], bg['eps'], bg['TH'].astype(float), levels=[1.0],
           colors='k', linewidths=1.8)
Dv = [min(r['D'], 5.9) for r in rows]
Ev = [min(r['eps'], 0.59) for r in rows]
Mv = [max(-2, min(r['margin'], 0.6)) for r in rows]
sc = ax.scatter(Dv, Ev, c=Mv, cmap='PiYG', vmin=-1.0, vmax=1.0,
                edgecolors='k', linewidths=0.4, s=42, zorder=5)
fig.colorbar(sc, ax=ax, label='certificate margin '
             r'$\inf_\lambda(P_H(\lambda)-\lambda\varepsilon)$'
             ' (green: no certificate)')
ax.set_xlabel('window half-width $D$'); ax.set_ylabel(r'bias $\varepsilon$')
ax.set_title('Candidate windows on the phase diagram, colored by '
             'mixed-tower certificate margin\n(negative/red-pink = '
             'descent certificate; the interesting ones would be green '
             'inside the allowed region)')
fig.tight_layout()
fig.savefig('viz/fig8_candidate_margins.png', dpi=180)
print("wrote viz/fig8_candidate_margins.png")
