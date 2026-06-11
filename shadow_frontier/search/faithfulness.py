#!/usr/bin/env python3
"""Faithfulness audit of the finite-shadow framework.

Referee question: does the finite-shadow language capture ALL arithmetic
mechanisms available to Collatz, or only those visible to surviving
candidates inside the framework?

F1  LOSSLESSNESS: length-k words partition the odd 2-adics into exactly
    one residue class mod 2^{B_w+1} each (conjugacy, not projection).
F2  k-POINT SHADOW COMPLETENESS: for any modulus Q coprime to 6, the
    window observable x_{n+i} mod Q is an EXACT function of
    (x_n mod Q, letters); multiplicative characters satisfy the keystone
    identity chi(x_{n+1}) chi(2)^b = chi(3x_n+1) exactly.
F3  CRT ORTHOGONALITY: conditional on ANY word-prefix cylinder, residues
    mod m (m odd) are EXACTLY equidistributed: no finite place other
    than 2 feeds the word.
F4  HIDDEN-CHANNEL TEST (non-tautological): do multiplicative invariants
    (omega(n), squarefreeness, primality, 3|n) of deep {1,2}-survivors
    deviate from size-matched random odd controls? A deviation would be
    an arithmetic mechanism OUTSIDE the shadow language.
F5  FORWARD-FLOW LAWS: letter marginals are exactly 2^{-k} by residue
    counting over ALL odd integers (universal, Tao-direction), and
    ensemble letter autocorrelations vanish.
"""
import random, math
from collections import defaultdict
import numpy as np

random.seed(20260611)

def v2(n):
    n = abs(n); return (n & -n).bit_length() - 1

def step(x):
    t = 3 * x + 1; b = v2(t); return t >> b, b

def letters(x, n):
    out = []
    for _ in range(n):
        x, b = step(x); out.append(b)
    return out

# ---------- F1: losslessness ----------
K = 4
groups = defaultdict(set)
M = 1 << 21
for x in range(1, M, 2):
    w = tuple(letters(x, K))
    if sum(w) + 1 <= 21:                       # word determined within modulus
        groups[w].add(x % (1 << (sum(w) + 1)))
ok = all(len(s) == 1 for s in groups.values())
mass = sum(2.0 ** -(sum(w)) for w in groups)   # density among odds
print(f"F1 losslessness: {len(groups)} length-{K} words, each = exactly one "
      f"class mod 2^(B+1): {ok}; total mass {mass:.6f} (should approach 1)")

# ---------- F2: k-point shadow completeness ----------
ok = True
for _ in range(2000):
    Q = random.choice([5, 7, 11, 13, 25, 35])
    x = random.randrange(1, 1 << 40) | 1
    w, y = [], x
    A, B = 0, 0
    for i in range(3):
        y2, b = step(y)
        # affine form: x_{n+i+1} = (3^{i+1} x + A)/2^B with A,B from word
        A = 3 * A + (1 << B); B += b
        w.append(b); y = y2
        lhs = y % Q
        rhs = (3 ** (i + 1) * x + A) * pow(2, -B, Q) % Q
        if lhs != rhs: ok = False
    # keystone identity for any multiplicative character: as group identity
    x1, b = step(x)
    if (x1 * pow(2, b, Q)) % Q != (3 * x + 1) % Q: ok = False
print(f"F2 k-point completeness (window mod Q = f(x mod Q, letters); "
      f"keystone identity): {ok}")

# ---------- F3: CRT orthogonality ----------
ok = True
for trial in range(40):
    # read a realizable word off a random integer; its class IS the cylinder
    x = random.randrange(1 << 50, 1 << 54) | 1
    w = letters(x, 18)
    B = sum(w); mod = 1 << (B + 1)
    r = x % mod
    # sanity: the class representative reproduces the word
    if letters(r if r > 0 else r + mod, 18) != w: ok = False
    for m in (3, 5, 7):
        cnt = defaultdict(int)
        for j in range(3 * m):
            cnt[(r + j * mod) % m] += 1
        if sorted(cnt.values()) != [3] * m: ok = False
print(f"F3 CRT orthogonality (cylinder members exactly uniform mod 3,5,7): {ok}")

# ---------- F4: hidden-channel test ----------
LIM = 1 << 22
xs = np.arange(1, LIM, 2, dtype=np.int64)
n0 = xs.copy()
D = 0
while len(n0) > 3000:
    t = 3 * xs + 1
    v = np.zeros_like(xs)
    tt = t.copy()
    m = (tt & 1) == 0
    while m.any():
        tt[m] >>= 1; v[m] += 1; m = (tt & 1) == 0
    alive = v <= 2
    xs = (t >> np.minimum(v, 62))[alive]; n0 = n0[alive]; D += 1
survivors = [int(z) for z in n0]
print(f"F4 hidden channels: {len(survivors)} survivors of depth {D} below 2^22")

def omega_sqfree(n):
    om, sq, m = 0, True, n
    p = 2
    while p * p <= m:
        if m % p == 0:
            om += 1
            e = 0
            while m % p == 0: m //= p; e += 1
            if e > 1: sq = False
        p += 1 if p == 2 else 2
    if m > 1: om += 1
    return om, sq

ctrl = [random.randrange(min(survivors) | 1, LIM) | 1 for _ in range(len(survivors))]
for name, pop in [("survivors", survivors), ("controls  ", ctrl)]:
    oms, sqs, div3, prim = [], 0, 0, 0
    for n in pop:
        om, sq = omega_sqfree(n)
        oms.append(om); sqs += sq; div3 += (n % 3 == 0); prim += (om == 1 and sq)
    N = len(pop)
    print(f"   {name}: mean omega = {sum(oms)/N:.3f}, P[squarefree] = {sqs/N:.3f}, "
          f"P[3|n] = {div3/N:.3f}, P[prime-ish] = {prim/N:.3f}")
print("   (matching values = no multiplicative channel outside the language;"
      " odd-integer squarefree density 8/pi^2 = 0.811)")

# ---------- F5: forward-flow universal laws ----------
mod = 1 << 14
cnt = defaultdict(int)
for x in range(1, mod, 2):
    cnt[min(v2(3 * x + 1), 10)] += 1
print("F5 letter marginals over ALL odd residues mod 2^14 (exact counting):")
for k in range(1, 6):
    print(f"   P[b={k}] = {cnt[k]}/{mod//2} = {cnt[k]/(mod//2):.6f}  "
          f"(law 2^-{k} = {2.0**-k:.6f})")
# lag correlation must be measured BEFORE absorption into the trivial
# cycle (whose constant b=2 tail induces spurious positive correlation):
# use 600-bit seeds and 300-letter windows (drift consumes ~125 bits).
corr = []
for _ in range(400):
    x = random.randrange(1 << 600, 1 << 604) | 1
    bs = letters(x, 300)
    a = np.array(bs[:-1], dtype=float); b = np.array(bs[1:], dtype=float)
    corr.append(np.corrcoef(a, b)[0, 1])
print(f"   ensemble lag-1 letter correlation (pre-absorption windows): "
      f"{np.mean(corr):+.5f} +- {np.std(corr)/20:.5f}  (faithful prediction: 0)")
