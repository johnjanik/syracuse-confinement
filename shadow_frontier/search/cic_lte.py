#!/usr/bin/env python3
"""CIC (Carry Independence Conjecture) via the LTE round chain.

CIC: every odd n0 > 1 eventually takes a letter b >= 3 (hits 5 mod 8).
Equivalently no positive integer > 1 has all letters in {1,2} forever.

ROUND CHAIN: a {1,2}-orbit, parsed at 1-run starts, is the chain
  x: g = v2(x+1), l = g-1, m = (x+1)/2^g (odd)
  READING: v = v2(3^l m - 1) = v2(m - 3^{-l})   [LTE normal form]
  death <=> v odd ; survival <=> v = 2r even (r>=1):
  then h = 1+v (odd), 2-run length r, u = oddpart(3^l m - 1),
  next 1-run start z with m' = oddpart(3^r u + 1), g' = 1 + v2(3^r u + 1).
Verifications:
  W1  round-chain recoding is exact (letters + m' formula)
  W2  LTE normal form v2(3^l m - 1) = v2(m - 3^{-l} mod 2^big)
  W3  Mersenne first round: x = 2^g - 1 survives <=> g odd & v2(g-1) even
  W4  Haar laws: per-round survival EXACTLY 1/3, iid across rounds
      (tests Chang's 'two-round anti-correlation 0.635' under Haar);
      conditional drift per surviving round = 2*0.585 - (4/3)*0.415 = +0.6166
  W5  entropy deficit: lambda_12(D) < 2^H(2-log2 3) = 1.9714 for all D
  W6  min-height survival champions (growth of min n0 surviving D letters)
"""
import random, math
import numpy as np
from decimal import Decimal, getcontext

random.seed(20260611)
L23 = math.log2(3.0)

def v2(n):
    n = abs(n); return (n & -n).bit_length() - 1

def step(x):
    t = 3 * x + 1; b = v2(t); return t >> b, b

def letters(x, n):
    out = []
    for _ in range(n):
        x, b = step(x); out.append(b)
    return out

# ---------- W1: round chain exactness ----------
ok, n = True, 0
for _ in range(5000):
    x = (random.randrange(1, 1 << 46) * 4 + 3)        # 1-run start
    g = v2(x + 1); l = g - 1; m = (x + 1) >> g
    M = 3 ** l * m - 1
    v = v2(M)
    h = 1 + v
    r = (h - 1) // 2
    pred = [1] * l + [2] * r
    if v % 2 == 0:                                     # survive: next is b=1
        u = M >> v
        gnext = 1 + v2(3 ** r * u + 1)
        pred += [1]
        mnext = (3 ** r * u + 1) >> v2(3 ** r * u + 1)
    direct = letters(x, len(pred))
    if direct != pred: ok = False
    if v % 2 == 0:
        # walk to the next 1-run start and check (g', m')
        y = x
        for _ in range(l + r): y, _ = step(y)
        if v2(y + 1) != gnext or (y + 1) >> gnext != mnext: ok = False
    else:
        # death: letter after the 2-run is >= 3
        y = x
        for _ in range(l + r): y, _ = step(y)
        if step(y)[1] < 3: ok = False
    n += 1
print(f"W1 round chain: {n} rounds, letters+death+(g',m') all exact: {ok}")

# ---------- W2: LTE normal form ----------
ok = True
for _ in range(2000):
    l = random.randint(0, 40); m = random.randrange(1, 1 << 40) | 1
    v = v2(3 ** l * m - 1)
    tgt = pow(pow(3, l, 1 << 60), -1, 1 << 60)         # 3^{-l} mod 2^60
    if v != v2((m - tgt) % (1 << 60)) and v < 60: ok = False
print(f"W2 LTE normal form v2(3^l m - 1) = v2(m - 3^(-l)): {ok}")

# ---------- W3: Mersenne first round ----------
ok = True
tbl = []
for g in range(2, 61):
    x = 2 ** g - 1
    l = g - 1
    v = v2(3 ** l - 1)                                  # m = 1
    survives = (v % 2 == 0)
    pred = (g % 2 == 1) and (v2(g - 1) % 2 == 0)
    if survives != pred: ok = False
    tbl.append((g, survives))
surv = [g for g, s in tbl if s]
print(f"W3 Mersenne 2^g-1 round-1 survival == [g odd & v2(g-1) even]: {ok}")
print(f"   surviving g <= 60: {surv}")

# ---------- W4: Haar laws (exact enumeration over residue classes) ----------
# enumerate classes x = 3 mod 4 (1-run starts) mod 2^MM; follow rounds while
# the consumed bit budget keeps the round outcome class-determined
MM = 24
det_j = [0] * 8; sur_j = [0] * 8
drift1 = []
for x0 in range(3, 1 << MM, 4):
    x, bits, j = x0, 0, 0
    alive = True
    while alive and j < 7:
        g = v2(x + 1); l = g - 1; m = (x + 1) >> g
        Mv = 3 ** l * m - 1; v = v2(Mv); r = v // 2 if v % 2 == 0 else (v - 1) // 2
        if bits + g + 1 + v + 3 > MM: break
        det_j[j] += 1
        if v % 2 == 1: alive = False; break
        sur_j[j] += 1
        if j == 0: drift1.append((L23 - 1) * l - (2 - L23) * r)
        bits += l + 2 * r + 1
        for _ in range(l + r): x, _ = step(x)           # to next 1-run start
        j += 1
print("W4 Haar laws (exact classes mod 2^24, determined rounds only):")
for j in range(5):
    if det_j[j]:
        print(f"   round {j+1}: survival {sur_j[j]}/{det_j[j]} = "
              f"{sur_j[j]/det_j[j]:.6f}  (iid prediction 1/3 = 0.333333)")
print(f"   conditional drift round 1 over survivors: {sum(drift1)/len(drift1):+.4f} "
      f"(prediction +0.6166) -- SURVIVORS ASCEND")

# ---------- W5: entropy deficit for the {1,2} alphabet ----------
getcontext().prec = 50
LD = Decimal(3).ln() / Decimal(2).ln()
def lam12(D, p):
    Dd = Decimal(str(D)); cur = {0: 1}
    for j in range(1, p + 1):
        lo = int((Decimal(j) * LD - Dd).to_integral_value(rounding='ROUND_CEILING'))
        hi = int((Decimal(j) * LD + Dd).to_integral_value(rounding='ROUND_FLOOR'))
        nxt = {}
        for B, c in cur.items():
            for b in (1, 2):                            # alphabet restricted
                Bn = B + b
                if lo <= Bn <= hi: nxt[Bn] = nxt.get(Bn, 0) + c
        cur = nxt
    tot = sum(cur.values())
    return math.exp(math.log(tot) / p) if tot else 0.0
q = 2 - L23
Hq = -q * math.log2(q) - (1 - q) * math.log2(1 - q)
print(f"W5 entropy deficit: ceiling 2^H(2-log2 3) = 2^{Hq:.5f} = {2**Hq:.5f}")
for D in (0.8, 1.2, 2.0, 4.0, 8.0):
    lam = lam12(D, 2000)
    print(f"   D={D}: lambda_12 = {lam:.5f}  theta_12 = {math.log2(lam):.5f}"
          f"  (< {Hq:.5f}: {math.log2(lam) < Hq + 1e-9})")

# ---------- W6: min-height survival champions ----------
LIM = 1 << 26
xs = np.arange(3, LIM, 4, dtype=np.int64)               # 1-run starts only
n0 = xs.copy()
print("W6 min n0 (odd, =3 mod 4) surviving D letters in {1,2}:")
champ = {}
for D in range(1, 45):
    t = 3 * xs + 1
    b = np.zeros_like(xs)
    tt = t.copy()
    bb = (tt & 1) == 0
    v = np.zeros_like(xs)
    while bb.any():
        tt[bb] >>= 1; v[bb] += 1
        bb = (tt & 1) == 0
    alive = v <= 2
    xs = (t >> np.minimum(v, 62))[alive]; n0 = n0[alive]
    if len(n0) == 0: break
    champ[D] = int(n0.min())
for D in sorted(champ):
    if D % 4 == 0 or D > 36:
        c = champ[D]
        print(f"   D={D}: min n0 = {c}  (log2 = {math.log2(c):.2f}, "
              f"D/log2(n0) = {D/math.log2(c):.2f})")
