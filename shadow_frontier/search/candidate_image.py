#!/usr/bin/env python3
"""Render the four-panel candidate image + diagnostics.

Usage:
  python3 search/candidate_image.py --seed 687871 --steps 50 --out viz/cand_687871.png
  python3 search/candidate_image.py --pilot 0 --out viz/cand_pilot000.png
  python3 search/candidate_image.py --word 1,2,1,1,... --out viz/cand_word.png
"""
import argparse, math, json, sys
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
sys.path.insert(0, 'search')
from candidate_tools import orbit, diagnose, checklist, LOG23
from frontier import biased_letter_law, gen_word, calibrate, realize

ap = argparse.ArgumentParser()
ap.add_argument('--seed', type=int, help='integer orbit start')
ap.add_argument('--steps', type=int, default=60)
ap.add_argument('--pilot', type=int, help='pilot word index (seed-1 stream)')
ap.add_argument('--word', type=str, help='comma-separated letters')
ap.add_argument('--out', required=True)
a = ap.parse_args()

if a.seed is not None:
    xs, word = orbit(a.seed, a.steps)
    label = f"integer seed {a.seed}"
else:
    if a.pilot is not None:
        rng = np.random.default_rng(1)
        law, _ = biased_letter_law()
        for k in range(a.pilot + 1):
            word = calibrate(gen_word(law, 240, rng))
        label = f"pilot word #{a.pilot} (ghost class)"
    else:
        word = [int(t) for t in a.word.split(',')]
        label = "user word"
    r, Mb = realize(word)
    xs, w2 = orbit(r, len(word))
    assert w2 == list(word), "realization/word mismatch"

word = list(word)
d = diagnose(word, xs, label)
cl = checklist(d)

fig, axs = plt.subplots(2, 2, figsize=(14, 9))
# P1 height
h = [math.log2(x) for x in xs]
ax = axs[0, 0]
ax.plot(h, lw=1.2, color='navy')
ax.axhline(d['H'], color='gray', lw=0.8)
ax.axhline(d['H'] + d['Dband'], color='gray', ls='--', lw=0.8)
ax.axhline(d['H'] - d['Dband'], color='gray', ls='--', lw=0.8)
ax.set_title(f"height: H={d['H']:.1f}, D={d['Dband']:.2f} "
             f"(ratio {2**(2*d['Dband']):.1f}), slope {d['slope']:+.4f}/step")
ax.set_xlabel('n'); ax.set_ylabel(r'$\log_2 x_n$')
# P2 phase
ax = axs[0, 1]
cm = np.cumsum(word) / np.arange(1, len(word) + 1)
ax.plot(cm, color='darkred', lw=1.2, label=r'running mean $\bar b$')
ax.axhline(LOG23, color='k', ls=':', lw=1)
ax.set_ylim(min(1.3, cm.min() - 0.05), max(2.0, cm.max() + 0.05))
ax.set_xlabel('n')
ax.legend(loc='upper left', fontsize=8)
ax2 = ax.inset_axes([0.55, 0.55, 0.42, 0.40])
ks = list(d['shadows'].keys())
ax2.bar(range(len(ks)), [d['shadows'][k] for k in ks], color='teal')
null = 1 / math.sqrt(len(word))
ax2.axhline(null, color='r', ls='--', lw=0.8)
ax2.set_xticks(range(len(ks))); ax2.set_xticklabels(ks, fontsize=6, rotation=45)
ax2.set_title(r'shadow biases (red = $1/\sqrt{M}$ null)', fontsize=7)
ax.set_title(f"phase: mean b = {d['mean_b']:.4f} vs log2(3) = {LOG23:.4f}; "
             f"max non-cob = {d['max_noncob']:.3f}")
# P3 complexity
ax = axs[1, 0]
ps = sorted(d['profile']); ax.plot(ps, [d['profile'][p] for p in ps],
                                   color='purple', lw=1.4)
ax.axhline(1.0, color='gray', lw=0.6)
if d['pcrit'] <= max(ps):
    ax.axvline(d['pcrit'], color='crimson', ls='--', lw=1.2)
    ax.text(d['pcrit'], 0.45, f" critical p={d['pcrit']}", color='crimson',
            fontsize=8, rotation=90)
else:
    ax.text(0.97, 0.1, f"critical p={d['pcrit']} > window\n(untestable here)",
            transform=ax.transAxes, ha='right', color='crimson', fontsize=9)
ax.set_ylim(0, 1.05)
coll = d['min_collision']
ax.set_title(f"complexity: P(p)/(M-p+1); ratio at p={d['pfeas']}: "
             f"{d['complexity_ratio']:.3f}; min collision "
             + ('n/a' if coll is None else f'{coll:.2e}'))
ax.set_xlabel('p'); ax.set_ylabel('factor diversity ratio')
# P4 mixed tower
ax = axs[1, 1]
lvls = sorted(d['margins'])
vals = [d['margins'][lv] for lv in lvls]
disp = [(-2.0 if v == -math.inf else v) for v in vals]
cols = ['firebrick' if v < 0 else 'seagreen' for v in vals]
ax.bar(range(len(lvls)), disp, color=cols)
ax.axhline(0, color='k', lw=0.8)
ax.set_xticks(range(len(lvls)))
ax.set_xticklabels([f"$2^{{{a_}}}3^{{{b_}}}$" for a_, b_ in lvls], fontsize=8)
ax.set_title(r'mixed-tower margin $\inf_\lambda(P_H(\lambda)-\lambda\varepsilon)$'
             f"  (eps = {d['eps']:.3f}; red = certificate; -inf shown as -2)")
verdict = cl['verdict']
fig.suptitle(f"{label}   —   checklist: " +
             "  ".join(f"{k.split('_',1)[1]}:{'OK' if str(v).startswith(('pass','untest')) else 'X'}"
                       for k, v in cl.items() if k != 'verdict') +
             f"   ==> {verdict}", fontsize=11,
             color=('darkred' if verdict == 'SURVIVOR' else 'black'))
fig.tight_layout()
fig.savefig(a.out, dpi=170)
dd = {k: v for k, v in d.items() if k != 'profile'}
dd['margins'] = {f"2^{a_}3^{b_}": v for (a_, b_), v in d['margins'].items()}
print(json.dumps(dd, default=str, indent=1))
print(json.dumps(cl, indent=1))
print(f"wrote {a.out}")
