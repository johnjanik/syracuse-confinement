#!/usr/bin/env python3
"""The 3-smooth LTE cascade: x = 2^g 3^a -+ 1.

S1  minus family x = 2^g 3^a - 1 (g>=2): round-1 reading v = v2(3^n - 1),
    n = g+a-1; LTE: v = 1 (n odd) / 2 + v2(n) (n even);
    survival <=> v2(n) even >= 2.  [a=0 reproduces the Mersenne theorem]
S2  plus family x = 2^g 3^a + 1 (g>=3): +1-clock ride floor((g-1)/2);
    g odd  -> lands z = 2*3^{a'} + 1, a' = a+(g-1)/2 (stays 3-smooth!);
              g' = 2 if a' even, 3 if a' odd;
    g even -> terminal 4*3^{a'} + 1, death letter b = 2 + v2(3^{a'+1}+1)
              in {3,4} (LTE), i.e. closed-form CIC death.
S3  plus family round 2 (g odd):
    a' even -> v' = v2(3^{a'+1}+1) - 1 = 1: DEATH, closed form;
    a' odd  -> v' = v2(3^{a'+2} + 5) - 2 = v2(a'+2 - Log_3(-5)):
               a GHOST-LOG reading against N0 = Log_3(-5) in Z_2.
S4  N0 = Log_3(-5) mod 2^64 (iterative discrete-log lift) + the identity
    v2(3^N + 5) = 2 + v2(N - N0) for N = N0 mod 2.
S5  minus family round 2: the reading is the 4-term S-unit valuation
    v' = v2(3^{n+r+l'} - 3^{r+l'} + 2^v 3^{l'} - 2^{v+l'}) - v - l'
    (the S-unit horizon: no 2-term collapse).
S6  cascade statistics for the minus family: death-round map over a
    (g,a) grid; thinning vs (1/3)^j; family champions.
"""
import math

def v2(n):
    n = abs(n); return (n & -n).bit_length() - 1

def step(x):
    t = 3 * x + 1; b = v2(t); return t >> b, b

def reading_chain(x, maxrounds=40):
    """rounds until death (b>=3); returns (rounds survived, readings)."""
    rounds, readings = 0, []
    while rounds < maxrounds:
        assert x % 4 == 3
        g = v2(x + 1); l = g - 1; m = (x + 1) >> g
        v = v2(3 ** l * m - 1)
        readings.append(v)
        if v % 2 == 1: return rounds, readings
        for _ in range(l + v // 2): x, _ = step(x)
        rounds += 1
    return rounds, readings

# ---------- S1: minus family round 1 ----------
ok = True
for g in range(2, 40):
    for a in range(0, 25):
        n = g + a - 1
        x = 2 ** g * 3 ** a - 1
        v = v2(3 ** (g - 1) * ((x + 1) >> g) - 1)
        pred = 1 if n % 2 == 1 else 2 + v2(n)
        if v != pred: ok = False
        surv = reading_chain(x, 1)[0] >= 1
        if surv != (n % 2 == 0 and v2(n) % 2 == 0): ok = False
print(f"S1 minus family round 1 == LTE(n=g+a-1) on 38x25 grid: {ok}")

# ---------- S2: plus family structure ----------
ok = True
for g in range(3, 36):
    for a in range(0, 22):
        x = 2 ** g * 3 ** a + 1
        r = (g - 1) // 2
        ap = a + r
        y = x
        for i in range(r):
            y2, b = step(y)
            if b != 2: ok = False
            y = y2
        if g % 2 == 1:
            if y != 2 * 3 ** ap + 1: ok = False
            gp = v2(y + 1)
            if gp != (2 if ap % 2 == 0 else 3): ok = False
        else:
            if y != 4 * 3 ** ap + 1: ok = False
            _, b = step(y)
            pred = 2 + v2(3 ** (ap + 1) + 1)
            if b != pred or pred not in (3, 4): ok = False
print(f"S2 plus family: ride floor((g-1)/2), landing forms, death letters: {ok}")

# ---------- S4: N0 = Log_3(-5) in Z_2 ----------
K = 64
N0 = 1                       # 3^1 = 3 = -5 mod 8
for k in range(4, K + 1):
    mod = 1 << k
    if pow(3, N0, mod) != (-5) % mod:
        N0 += 1 << (k - 3)   # ord(3 mod 2^k) = 2^{k-2}
        assert pow(3, N0, mod) == (-5) % mod
print(f"S4 N0 = Log_3(-5) mod 2^64 = {N0}")
print(f"   = 0x{N0:x}; low bits: {bin(N0 % 1024)}")
ok = True
for N in range(3, 4000, 2):  # N odd = N0 parity
    lhs = v2(3 ** N + 5)
    rhs = 2 + v2((N - N0) % (1 << 60))
    if lhs != rhs: ok = False
print(f"   identity v2(3^N + 5) = 2 + v2(N - N0) for odd N < 4000: {ok}")

# ---------- S3: plus family round 2 ----------
ok = True
deaths_even, ghostlog = 0, []
for g in range(3, 36, 2):                       # g odd
    for a in range(0, 22):
        x = 2 ** g * 3 ** a + 1
        ap = a + (g - 1) // 2
        # walk to the 1-run start z = 2*3^ap + 1, then do one round
        z = 2 * 3 ** ap + 1
        gp = v2(z + 1); lp = gp - 1; mp = (z + 1) >> gp
        vp = v2(3 ** lp * mp - 1)
        if ap % 2 == 0:
            if vp != 1: ok = False                # closed-form death
            deaths_even += 1
        else:
            pred = v2((ap + 2 - N0) % (1 << 60))
            if vp != pred: ok = False             # ghost-log reading
            ghostlog.append((ap, vp))
print(f"S3 plus family round 2: a' even -> death (v'=1) [{deaths_even} cases]; "
      f"a' odd -> v' = v2(a'+2 - Log_3(-5)) [{len(ghostlog)} cases]: {ok}")

# ---------- S5: minus family round 2 = 4-term S-unit valuation ----------
ok = True
cnt = 0
for g in range(2, 30):
    for a in range(0, 18):
        n = g + a - 1
        if n % 2 == 1 or v2(n) % 2 == 1: continue # need round-1 survival
        x = 2 ** g * 3 ** a - 1
        v = 2 + v2(n); r = v // 2
        # walk to next 1-run start, get actual round-2 reading
        y = x
        for _ in range((g - 1) + r): y, _ = step(y)
        gp = v2(y + 1); lp = gp - 1; mp = (y + 1) >> gp
        vp = v2(3 ** lp * mp - 1)
        Sunit = (3 ** (n + r + lp) - 3 ** (r + lp)
                 + 2 ** v * 3 ** lp - 2 ** (v + lp))
        if vp != v2(Sunit) - v - lp: ok = False
        cnt += 1
print(f"S5 minus family round 2 == 4-term S-unit valuation ({cnt} cases): {ok}")

# ---------- S6: cascade statistics, minus family ----------
hist = {}
champs = []
for g in range(2, 42):
    for a in range(0, 26):
        x = 2 ** g * 3 ** a - 1
        rds, rd = reading_chain(x)
        hist[rds] = hist.get(rds, 0) + 1
        champs.append((rds, g, a, rd))
champs.sort(reverse=True)
tot = sum(hist.values())
print("S6 minus-family death-round distribution (grid g<42, a<26, N=%d):" % tot)
acc = tot
for j in sorted(hist):
    print(f"   die at round {j+1}: {hist[j]:4d}  "
          f"(survive >= {j+1} rounds: {acc/tot:.4f}; iid (1/3)^{j} = {3.0**-j:.4f})")
    acc -= hist[j]
print("   family champions (rounds survived, g, a, readings):")
for c in champs[:5]:
    print(f"     {c[0]} rounds: g={c[1]}, a={c[2]}, readings={c[3]}")
