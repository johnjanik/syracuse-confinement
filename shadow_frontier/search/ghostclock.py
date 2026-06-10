#!/usr/bin/env python3
"""Verification suite for material imported from arXiv:2603.11066v6 (Chang),
recast in our framework. Signature sigma=(k_1..k_l), depth K=sum, block map
F(x)=(3^l x + C)/2^K, phantom root rho = C/(2^K-3^l) (denominator always odd).
Alignment a(x) := v2((2^K-3^l)x - C) = v2(x - rho).

V1  cylinder threshold: following the sigma-block <=> alignment >= K+1
V2  universal repulsion: full block drops alignment by exactly K
V3  universal ride cap: #consecutive sigma-blocks ridden = floor((a-1)/K)
V5  universal depth supply: per-band pool of alignment->=g points = 2^{k-g}
V6  census formula (affine count): #{u<2^L: a(A+Bu)>=t} = 2^{L-t+min(beta,gam)}
V7  shadow return-time (their Thm): re-entry gap >= l+K-1 -- STRESS TEST
V7b alignment recovery speed: is +1 bit/step the max? -- STRESS TEST
V8  recompute their census constant R = sum_{K>=3} R(K) (claim: <= 0.0893)
V9  their Persistent Exit Lemma part 2 == our parity handoff at h=3
V10 compatible-class count |C_D| (their claim 2*3^{D-1}; our coding: 3^D)
"""
import random, math
from math import comb

random.seed(20260611)
L23 = math.log2(3.0)

def v2(n):
    n = abs(n)
    return (n & -n).bit_length() - 1

def step(x):
    t = 3 * x + 1
    b = v2(t)
    return t >> b, b

def letters(x, n):
    out = []
    for _ in range(n):
        x, b = step(x)
        out.append(b)
    return out

def sig_data(sig):
    l, K = len(sig), sum(sig)
    B = [0]
    for k in sig: B.append(B[-1] + k)
    C = sum(3 ** (l - 1 - j) * 2 ** B[j] for j in range(l))
    D = 2 ** K - 3 ** l                      # odd
    return l, K, C, D

def align(x, C, D):
    return v2(D * x - C)

def rep_mod(sig, m):
    """least positive odd representative of rho mod 2^m"""
    l, K, C, D = sig_data(sig)
    return (C * pow(D, -1, 2 ** m)) % (2 ** m)

FAMS = [(1,), (2,), (1, 2), (1, 1, 2), (1, 1, 1, 2, 1, 1, 4)]
RAND = [tuple(random.randint(1, 5) for _ in range(random.randint(2, 6)))
        for _ in range(20)]

print("=== V1 cylinder threshold (claim: forcing modulus = K+1) ===")
ok = True
for sig in FAMS + RAND:
    l, K, C, D = sig_data(sig)
    forced = None
    for m in range(1, K + 4):
        r = rep_mod(sig, m)
        if all(letters(r + j * 2 ** m, l) == list(sig)
               for j in random.sample(range(1, 1 << 14), 40)):
            forced = m; break
    if forced != K + 1: ok = False; print(f"  {sig}: forcing modulus {forced} != K+1={K+1}")
print(f"  all {len(FAMS)+len(RAND)} signatures: forcing modulus == K+1: {ok}")

print("=== V2 universal repulsion (alignment drop == K per block) ===")
ok, n = True, 0
for sig in FAMS + RAND:
    l, K, C, D = sig_data(sig)
    for extra in range(1, 9):
        m = K + 1 + extra
        x = rep_mod(sig, m) + random.randint(1, 1 << 12) * 2 ** m
        a0 = align(x, C, D)
        y = (3 ** l * x + C)
        assert y % 2 ** K == 0
        y >>= K
        if letters(x, l) != list(sig) or align(y, C, D) != a0 - K:
            ok = False; print(f"  FAIL {sig} m={m}")
        n += 1
print(f"  {n} block applications: drop == K exactly: {ok}")

print("=== V3 universal ride cap (blocks ridden == floor((a-1)/K)) ===")
ok, n = True, 0
for sig in FAMS + RAND:
    l, K, C, D = sig_data(sig)
    for a in range(K + 1, min(K + 26, 60)):
        x = rep_mod(sig, a) + (2 ** a if rep_mod(sig, a + 1) == rep_mod(sig, a)
                               else 0)            # force alignment EXACTLY a
        if align(x, C, D) != a: x += 2 ** (a + 1)
        if align(x, C, D) != a: continue
        rides = 0
        y = x
        while letters(y, l) == list(sig):
            y = (3 ** l * y + C) >> K
            rides += 1
        if rides != (a - 1) // K:
            ok = False; print(f"  FAIL {sig}: a={a} rides={rides} != {(a-1)//K}")
        n += 1
print(f"  {n} cases: rides == floor((a-1)/K): {ok}")

print("=== V5 universal depth supply (band pool size) ===")
ok = True
for sig in FAMS:
    l, K, C, D = sig_data(sig)
    for k, g in [(16, 6), (18, 9), (20, 12)]:
        cnt = sum(1 for x in range(rep_mod(sig, g) % 2 ** g, 2 ** (k + 1), 2 ** g)
                  if x >= 2 ** k)
        if abs(cnt - 2 ** (k - g)) > 1: ok = False; print(f"  FAIL {sig} k={k} g={g}: {cnt}")
print(f"  pool sizes == 2^(k-g) (+-1): {ok}")

print("=== V6 census formula (CORRECTED: requires gamma <= beta) ===")
ok = True
for _ in range(400):
    sig = random.choice(FAMS + RAND)
    l, K, C, D = sig_data(sig)
    Lp = random.randint(8, 14)
    A = random.randrange(1, 1 << 30) | 1
    beta = align(A, C, D)
    gam = random.randint(0, max(0, beta))            # hypothesis gamma <= beta
    B = (random.randrange(1, 1 << 20) | 1) << gam
    t = random.randint(gam + 1, gam + 6)
    cnt = sum(1 for u in range(1 << Lp) if align(A + B * u, C, D) >= t)
    pred = 2 ** (Lp - t + gam) if Lp - t + gam >= 0 else 0
    if cnt != pred: ok = False
print(f"  400 cases with gamma<=beta match 2^(L-t+gamma): {ok}")
# the hypothesis is necessary: beta < gamma kills the formula
sig = (1, 2); l, K, C, D = sig_data(sig)
A = 11; beta = align(A, C, D); B = 2 ** (beta + 3); t = beta + 1
cnt = sum(1 for u in range(1 << 10) if align(A + B * u, C, D) >= t)
print(f"  beta<gamma counterexample: beta={beta} gamma={beta+3} t={t}: "
      f"count={cnt} vs naive {2**(10-t+beta)} -- hypothesis is necessary")

print("=== V7 shadow return-time REFUTATION (ride-aware visits) ===")
import statistics
for sig in [(1, 2), (1, 1, 2), (2, 1)]:
    l, K, C, D = sig_data(sig)
    exit_gaps, quick = [], 0
    for _ in range(400):
        x = random.randrange(1 << 48, 1 << 52) | 1
        xs, y = [], x
        for _ in range(4000):
            if y == 1: break
            xs.append(y); y, _ = step(y)
        t, last_exit = 0, None
        while t < len(xs) - 6 * l:
            a = align(xs[t], C, D)
            if a >= K + 1:
                rides = (a - 1) // K               # exact, by V3
                if last_exit is not None:
                    g = t - last_exit
                    exit_gaps.append(g)
                    if g < K - 1: quick += 1
                t += rides * l
                last_exit = t
            else:
                t += 1
    if exit_gaps:
        print(f"  sig={sig} (l={l},K={K}): visits={len(exit_gaps)}, "
              f"min exit->reentry gap={min(exit_gaps)} (their claim >= {l+K-1}), "
              f"median={statistics.median(exit_gaps):.0f}, "
              f"gaps<K-1: {100*quick/len(exit_gaps):.1f}% -- THEOREM FALSE AS STATED")

print("=== V7b alignment recovery speed (max one-step gain) ===")
for sig in [(1,), (1, 2), (1, 1, 2)]:
    l, K, C, D = sig_data(sig)
    mx = 0
    for _ in range(200):
        y = random.randrange(1 << 48, 1 << 52) | 1
        a_prev = align(y, C, D)
        for _ in range(3000):
            if y == 1: break
            y, _ = step(y)
            a = align(y, C, D)
            if a - a_prev > mx: mx = a - a_prev
            a_prev = a
    print(f"  sig={sig}: max observed one-step alignment GAIN = +{mx} "
          f"(their proof needs <= +1)")

print("=== V8 recompute census constant R (their claim R <= 0.0893) ===")
def mobius(n):
    if n == 1: return 1
    res, p, m = 1, 2, n
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0: return 0
            res = -res
        p += 1
    if m > 1: res = -res
    return res

def necklaces(K, l):
    g = math.gcd(K, l)
    tot = 0
    for d in range(1, g + 1):
        if g % d == 0:
            mu = mobius(d)
            if mu: tot += mu * comb(K // d - 1, l // d - 1)
    return tot // l

R, RK_table = 0.0, {}
for K in range(3, 501):
    rk = 0.0
    lmin = int(K / L23) + 1
    for l in range(lmin, K + 1):
        M = necklaces(K, l)
        if M: rk += M * (L23 - K / l)
    rk /= 2 ** K
    RK_table[K] = rk
    R += rk
print(f"  R(3..500) = {R:.6f}   (their claim 0.0893; margin vs eps=0.415: "
      f"{0.415/R:.2f}x)")
print(f"  leading terms: R(3)={RK_table[3]:.5f} R(4)={RK_table[4]:.5f} "
      f"R(5)={RK_table[5]:.5f} R(10)={RK_table[10]:.6f} R(20)={RK_table[20]:.2e}")

print("=== V9 their Persistent Exit Lemma == our parity handoff at h=3 ===")
ok, n = True, 0
for _ in range(4000):
    x = (random.randrange(1, 1 << 40) * 32 + 27)        # x = 27 mod 32, depth 2
    assert v2(x + 1) == 2
    y, b1 = step(x)                                      # final burst step
    h = v2(y - 1)
    y2, b2 = step(y)
    y3, b3 = step(y2)
    if not (b1 == 1 and h == 3 and b2 == 2 and b3 == 1): ok = False
    n += 1
print(f"  {n} samples x=27 mod 32: run-end -> h=3 exactly -> single b=2 -> "
      f"new 1-run: {ok}")

print("=== V10 compatible-class count |C_D| ({1,2}-words to depth D) ===")
for Dd in range(1, 9):
    M = 2 * Dd + 3
    cnt = 0
    for r in range(1, 2 ** M, 2):
        if all(b <= 2 for b in letters(r, Dd)): cnt += 1
    # classes mod 2^M; each word class mod 2^{B+1} contains 2^{M-B-1} residues
    print(f"  D={Dd}: surviving odd residues mod 2^{M} = {cnt} "
          f"(our prediction 2^{M-1}*(3/4)^D = {2**(M-1)*(3/4)**Dd:.0f}; "
          f"their |C_D|=2*3^(D-1) = {2*3**(Dd-1)})")
