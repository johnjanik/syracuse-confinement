#!/usr/bin/env python3
"""Candidate-counterexample diagnostics library.

A serious candidate must show FOUR simultaneous properties:
  (1) height panel: banded log2(x_n) in [H-D, H+D], no downward trend;
  (2) phase map: mean letter ~ log2(3) with nontrivial non-coboundary
      shadow bias (D_3, D_9, D_27, ... -- characters with chi(2) of
      order >= 3; order-2 = parity = the exempt coboundary direction);
  (3) complexity panel: near-full factor diversity P(p)/(M-p+1) ~ 1 at
      the critical scale p = floor(log2 Y);
  (4) mixed-tower panel: NO max-plus descent certificate at tested
      levels 2^a 3^b: margin inf_{lambda>=0}(P_H(lambda) - lambda*eps)
      stays >= 0 and persists under lifts.
"""
import math
import numpy as np

LOG23 = math.log2(3.0)

def karp_vec(nv, src, tgt, w):
    """Karp max cycle mean, vectorized over edges. -inf if acyclic."""
    INF = -1e18
    hist = np.full((nv + 1, nv), INF)
    hist[0, :] = 0.0
    for k in range(1, nv + 1):
        prev = hist[k - 1][src] + w
        cur = np.full(nv, INF)
        np.maximum.at(cur, tgt, prev)
        hist[k] = cur
    best = -np.inf
    last = hist[nv]
    for v in range(nv):
        if last[v] <= INF / 2: continue
        ks = np.where(hist[:nv, v] > INF / 2)[0]
        if len(ks) == 0: continue
        m = np.min((last[v] - hist[ks, v]) / (nv - ks))
        best = max(best, m)
    return best

def v2(n):
    n = abs(n); return (n & -n).bit_length() - 1

def orbit(x, M):
    xs, ws = [x], []
    for _ in range(M):
        t = 3 * x + 1; b = v2(t); x = t >> b
        ws.append(b); xs.append(x)
    return xs, ws

# ---------- shadows ----------
# root order m <-> character family: m=3 (mod 7/9 cube part, 'D_3'),
# m=6 ('D_9': ord_9(2)=6), m=18 ('D_27': ord_27(2)=18),
# m=4 (mod 5), m=10 (mod 11), m=12 (mod 13). m=2 (parity) is EXEMPT.
SHADOW_ORDERS = {'D_3': 3, 'D_9': 6, 'D_27': 18,
                 'D_5': 4, 'D_11': 10, 'D_13': 12}

def shadow(word, m):
    z = np.exp(-2j * np.pi / m)
    G = sum(2.0 ** -b * z ** b for b in range(1, 200))
    dev = np.mean([z ** b for b in word]) - G
    return dev          # complex deviation; |dev| is the bias magnitude

def shadows(word):
    return {k: shadow(word, m) for k, m in SHADOW_ORDERS.items()}

# ---------- complexity ----------
def complexity_profile(word, pmax):
    M = len(word)
    out = {}
    for p in range(1, min(pmax, M - 1) + 1):
        out[p] = len({tuple(word[i:i + p]) for i in range(M - p + 1)}) \
                 / (M - p + 1)
    return out

# ---------- repetition / collision ----------
def min_collision(word, xs, p):
    """min over repeated length-p blocks of |x_i - x_j| / 2^{p+1};
    < 1 means repetition rigidity fires (forced cycle)."""
    if p >= len(word): return None
    seen = {}
    best = None
    for i in range(len(word) - p + 1):
        key = tuple(word[i:i + p])
        if key in seen:
            for j in seen[key]:
                r = abs(xs[i] - xs[j]) / 2.0 ** (p + 1)
                if best is None or r < best: best = r
            seen[key].append(i)
        else:
            seen[key] = [i]
    return best

# ---------- mixed-tower certificate margin ----------
def trap_margin(word, xs, a, b3, eps, om):
    """Karp max-plus pressure margin of the residue trap at level 2^a 3^b3.
    Returns (margin, ncycle_states); margin = -inf if trap acyclic."""
    z = np.exp(2j * np.pi / 3)
    G = sum(2.0 ** -bb * z ** -bb for bb in range(1, 60))
    Q = (1 << a) * 3 ** b3
    rs = [x % Q for x in xs]
    verts = sorted(set(rs[:-1])); vid = {v: i for i, v in enumerate(verts)}
    edges, g, ph, seen = [], [], [], set()
    for i, bb in enumerate(word):
        key = (rs[i], bb)
        if key in seen: continue
        seen.add(key)
        tgt = rs[i + 1]
        if tgt not in vid: vid[tgt] = len(verts); verts.append(tgt)
        edges.append((vid[rs[i]], vid[tgt], len(g)))
        g.append(LOG23 - bb)
        ph.append(float(np.real(om * (z ** (-bb) - G))))
    g = np.array(g); ph = np.array(ph)
    src = np.array([e[0] for e in edges]); tg = np.array([e[1] for e in edges])
    nv = len(verts)

    def f(lam):
        pres = karp_vec(nv, src, tg, g + lam * ph)
        return (math.inf if pres == -np.inf else pres - lam * eps)

    p0 = f(0.0)
    if p0 == math.inf:
        return -math.inf, nv                    # acyclic: no recurrent trap
    # convex in lambda: golden-section on [0, 60]
    lo, hi = 0.0, 60.0
    gr = (math.sqrt(5) - 1) / 2
    a_, b_ = hi - gr * (hi - lo), lo + gr * (hi - lo)
    fa, fb = f(a_), f(b_)
    for _ in range(18):
        if fa < fb: hi, b_, fb = b_, a_, fa; a_ = hi - gr * (hi - lo); fa = f(a_)
        else:       lo, a_, fa = a_, b_, fb; b_ = lo + gr * (hi - lo); fb = f(b_)
    return min(p0, fa, fb), nv

def margin_grid(word, xs, levels=((2,2),(3,2),(4,2),(5,3),(6,3),(8,4))):
    z = np.exp(2j * np.pi / 3)
    G = sum(2.0 ** -bb * z ** -bb for bb in range(1, 60))
    dev = np.mean([z ** (-bb) for bb in word]) - G
    eps = abs(dev)
    om = np.conj(dev / abs(dev)) if eps > 1e-9 else 1.0
    return {lv: trap_margin(word, xs, lv[0], lv[1], eps, om)[0]
            for lv in levels}, eps

# ---------- the full diagnostic record ----------
def diagnose(word, xs, label=""):
    M = len(word)
    h = [math.log2(x) for x in xs]
    H = float(np.mean(h)); Dband = float(max(abs(v - H) for v in h))
    slope = float(np.polyfit(range(len(h)), h, 1)[0])
    Y = min(xs)
    pcrit = int(math.floor(math.log2(Y)))
    sh = shadows(word)
    noncob = max(abs(v) for v in sh.values())
    pfeas = min(pcrit, M - 2)
    prof = complexity_profile(word, min(M - 1, max(pfeas + 4, 40)))
    crat = prof.get(pfeas, float('nan'))
    coll = min_collision(word, xs, pfeas) if pfeas >= 1 else None
    margins, eps = margin_grid(word, xs)
    return dict(label=label, M=M, mean_b=float(np.mean(word)),
                H=H, Dband=Dband, slope=slope, Y=Y, pcrit=pcrit,
                pfeas=pfeas,
                shadows={k: abs(v) for k, v in sh.items()},
                max_noncob=noncob, eps=eps,
                complexity_ratio=crat, profile=prof,
                min_collision=coll, margins=margins)

# ---------- the six-step checklist ----------
def checklist(d, eta=0.02, cthresh=0.90, shmin=0.05):
    r = {}
    r['1_C1_drift'] = ('FAIL: descent-forcing'
                       if d['mean_b'] > LOG23 + eta else 'pass')
    if d['pfeas'] < d['pcrit']:
        r['2_repetition'] = 'untestable (window shorter than critical scale)'
    elif d['min_collision'] is not None and d['min_collision'] < 1.0:
        r['2_repetition'] = 'FAIL: rigidity fires (collision < 2^{p+1})'
    else:
        r['2_repetition'] = 'pass'
    r['3_complexity'] = ('FAIL: low-complexity ghost'
                         if d['complexity_ratio'] < cthresh else 'pass')
    det = [k for k, v in d['shadows'].items() if v >= shmin]
    r['4_shadow'] = (f"pass ({','.join(det)})" if det
                     else 'FAIL: no non-coboundary bias')
    neg = [lv for lv, m in d['margins'].items() if m < 0]
    r['5_certificate'] = (f"FAIL: certificate at {min(neg)}" if neg
                          else 'pass (no certificate at tested levels)')
    ms = sorted(d['margins'].items())
    lifted = all(d['margins'][ms[i+1][0]] >= 0 or ms[i][1] < 0
                 for i in range(len(ms) - 1))
    r['6_lift'] = ('pass' if not neg else
                   ('finite artifact (margin dies on lift)'
                    if any(m < 0 for _, m in ms[1:]) and ms[0][1] >= 0
                    else 'n/a'))
    r['verdict'] = ('SURVIVOR' if all(str(v).startswith('pass') or
                    str(v).startswith('untestable')
                    for k, v in r.items() if k != 'verdict') else 'dead')
    return r
