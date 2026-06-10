#!/usr/bin/env python3
"""The two-clock structure of Syracuse words.

CLAIMS TO VERIFY (exact, machine-checked):
  T1 (letter trichotomy mod 8):  b=1 iff x = 3,7 mod 8;  b=2 iff x = 1 mod 8
     (equivalently v2(x-1) >= 3);  b >= 3 iff x = 5 mod 8 (v2(x-1) = 2).
     Uniformly b_n = v2(3 x_n + 1) = v2(x_n + 1/3) in Z_2.
  T2 (-1 clock, from runbudget): maximal 1-run from x has length v2(x+1)-1,
     depth decrement exactly 1 per step.
  T3 (+1 clock, NEW): maximal 2-run from x (v2(x-1)=h>=3) has length
     floor((h-1)/2), depth decrement exactly 2 per step (x'-1 = 3(x-1)/4);
     terminal depth = 1 if h odd (hand off to a 1-run), = 2 if h even
     (next letter is b>=3).
  T4 (alternating parse): the full letter stream is reproduced by reading
     the two meters and the big letters only.
MEASUREMENTS:
  M1: natural laws of the meters vs ascending-window laws (g-law, h-law,
      h-parity, big-letter share); budget decomposition of ascent.
  M2: growth of the exact confined count N_{1/2}(p) (is it polynomial?).
"""
import random, math
from decimal import Decimal, getcontext

random.seed(20260610)
L23 = math.log2(3.0)

def v2(n):
    return (n & -n).bit_length() - 1

def step(x):
    t = 3 * x + 1
    b = v2(t)
    return t >> b, b

# ---------- T1-T3: exact clock verification ----------
T = 20000
t1 = t2 = t3 = 0
for _ in range(T):
    x = random.randrange(1, 1 << 44) | 1
    _, b = step(x)
    r = x % 8
    assert (b == 1) == (r in (3, 7))
    assert (b == 2) == (r == 1)
    assert (b >= 3) == (r == 5)
    assert b == v2(3 * x + 1)
    t1 += 1
    if r in (3, 7):                       # -1 clock
        g = v2(x + 1)
        y, n = x, 0
        while True:
            y2, b2 = step(y)
            if b2 != 1: break
            assert v2(y2 + 1) == v2(y + 1) - 1
            y, n = y2, n + 1
        assert n == g - 1
        t2 += 1
    if r == 1 and x > 1:                  # +1 clock
        h = v2(x - 1)
        if h == 2:
            _, b2 = step(x); assert b2 >= 3
        else:
            y, n = x, 0
            while True:
                y2, b2 = step(y)
                if b2 != 2: break
                assert v2(y2 - 1) == v2(y - 1) - 2
                y, n = y2, n + 1
            assert n == (h - 1) // 2
            hterm = h - 2 * n
            _, bnext = step(y)
            if hterm == 1: assert bnext == 1
            else:          assert hterm == 2 and bnext >= 3
        t3 += 1
print(f"T1 trichotomy: {t1}/{T} pass;  T2 (-1 clock): {t2} pass;  T3 (+1 clock): {t3} pass")

# ---------- T4: alternating parse reproduces the word ----------
def parse_letters(x, N):
    out = []
    while len(out) < N:
        if x % 4 == 3:
            g = v2(x + 1); l = g - 1
            out += [1] * l
            x = (3 ** l * (x + 1) >> l) - 1
        elif x % 8 == 1 and x > 1:
            h = v2(x - 1); l = (h - 1) // 2
            out += [2] * l
            x = (3 ** l * (x - 1) >> (2 * l)) + 1
        else:
            x, b = step(x); out.append(b)
    return out[:N]

ok = 0
for _ in range(2000):
    x = random.randrange(3, 1 << 40) | 1
    direct, y = [], x
    for _ in range(300):
        y, b = step(y); direct.append(b)
    assert parse_letters(x, 300) == direct
    ok += 1
print(f"T4 parse: {ok}/2000 trajectories reproduced exactly")

# ---------- M1: meter laws, natural vs ascending windows ----------
def window_stats(seeds, steps, wlen):
    nat = dict(g=[], h=[], hpar=[], big=[], n=0)
    asc = dict(g=[], h=[], hpar=[], big=[], n=0)
    budgets = []
    for _ in range(seeds):
        x0 = random.randrange(1 << 48, 1 << 52) | 1
        xs, bs = [x0], []
        y = x0
        for _ in range(steps):
            if y == 1: break
            y, b = step(y); xs.append(y); bs.append(b)
        nsteps = len(bs)
        for s in range(0, nsteps - wlen, wlen // 2):
            seg_x, seg_b = xs[s:s + wlen + 1], bs[s:s + wlen]
            ascending = (seg_x[-1] >= 4 * seg_x[0]) and min(seg_x) >= seg_x[0]
            tgt = asc if ascending else nat
            tgt['n'] += 1
            i = 0
            while i < wlen:
                x = seg_x[i]
                if seg_b[i] == 1 and (i == 0 or seg_b[i - 1] != 1):
                    tgt['g'].append(v2(x + 1))
                if seg_b[i] != 1 and (i == 0 or seg_b[i - 1] == 1):
                    h = v2(x - 1)
                    tgt['h'].append(h); tgt['hpar'].append(h % 2)
                if seg_b[i] >= 3:
                    tgt['big'].append(seg_b[i])
                i += 1
            if ascending:
                n1 = seg_b.count(1); n2 = seg_b.count(2)
                cbig = sum(b - L23 for b in seg_b if b >= 3)
                budgets.append(((L23 - 1) * n1, (2 - L23) * n2, cbig,
                                math.log2(seg_x[-1] / seg_x[0])))
    return nat, asc, budgets

nat, asc, budgets = window_stats(seeds=4000, steps=2000, wlen=60)
def mean(a): return sum(a) / len(a) if a else float('nan')
print(f"\nM1 windows: typical n={nat['n']}, ascending n={asc['n']}")
print(f"  run-start depth g: typical mean {mean(nat['g']):.3f} (natural 3.000), "
      f"ascending mean {mean(asc['g']):.3f}")
print(f"  handoff depth h:   typical mean {mean(nat['h']):.3f} (natural 3.000), "
      f"ascending mean {mean(asc['h']):.3f}")
print(f"  P[h odd]:          typical {mean(nat['hpar']):.3f} (natural 0.333), "
      f"ascending {mean(asc['hpar']):.3f}")
print(f"  big letters/step:  typical {len(nat['big'])/(nat['n']*60):.4f} (natural 0.25), "
      f"ascending {len(asc['big'])/(asc['n']*60):.4f}")
if budgets:
    A = mean([b[0] for b in budgets]); C2 = mean([b[1] for b in budgets])
    CB = mean([b[2] for b in budgets]); NET = mean([b[3] for b in budgets])
    print(f"  ascending budget per window: +{A:.2f} (1-runs) -{C2:.2f} (2-letters) "
          f"-{CB:.2f} (big letters) = {A-C2-CB:.2f}; measured net {NET:.2f}")

# natural-law reference: E[b] = 2, drift/letter = log2(3) - 2
print(f"  natural drift/letter = log2(3) - 2 = {L23-2:.4f}")

# ---------- M2: N_{1/2}(p) growth -- polynomial? ----------
getcontext().prec = 60
L = Decimal(3).ln() / Decimal(2).ln()
def exact_count(D, p):
    Dd = Decimal(str(D))
    cur = {0: 1}
    out = []
    for j in range(1, p + 1):
        lo = int((Decimal(j) * L - Dd).to_integral_value(rounding='ROUND_CEILING'))
        hi = int((Decimal(j) * L + Dd).to_integral_value(rounding='ROUND_FLOOR'))
        nxt = {}
        for B, c in cur.items():
            for Bn in range(max(lo, B + 1), hi + 1):
                nxt[Bn] = nxt.get(Bn, 0) + c
        cur = nxt
        out.append(sum(cur.values()))
    return out

print("\nM2: exact confined counts N_D(p):")
for D in (0.5, 0.55, 0.6):
    cs = exact_count(D, 1600)
    n100, n400, n1600 = cs[99], cs[399], cs[1599]
    expo = math.log(n1600 / n400) / math.log(4.0)  # poly degree if polynomial
    print(f"  D={D}: N(100)={n100}, N(400)={n400}, N(1600)={n1600}; "
          f"log-log slope p->4p: {expo:.2f}  (lambda^p would give slope ~{1200*math.log(1.1)/math.log(4):.0f}+)")
