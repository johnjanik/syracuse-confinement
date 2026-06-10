"""Validate degenerate classifier against exact complete sums, c=5, m=10.
S_pair = sum_{a in U} chi( prod_{i=1}^{m-1} (3^i a + C_i)/(3^i a + C'_i) ).
Prediction: deg_frac = 0  =>  S = 0 (machine);  deg_frac > 0  =>  |S|/phi ~ deg_frac scale."""
import numpy as np
c, m = 5, 10
K = c + 3; MOD = 3**K; Q = 3**c; PHI = 2 * 3**(c - 1)
rng = np.random.default_rng(42)
dlog = {}; p = 1
for j in range(PHI): dlog[p] = j; p = (p * 2) % Q
U = [a for a in range(Q) if a % 3]; phi = len(U)
chi = {a: np.exp(2j * np.pi * dlog[a] / PHI) for a in U}
invQ = {a: pow(a, -1, Q) for a in U}

def consts(b):
    C = [None, 1]; P = 1; B = 0
    for i in range(1, m):
        P = (P * pow(2, int(b[i - 1]), MOD)) % MOD
        C.append((3 * C[-1] + P) % MOD)
    return C  # C[1..m-1] used; C[m]=last appended? indices: C[i], i=1..m

def v3(x):
    if x % MOD == 0: return K
    v = 0; x %= MOD
    while x % 3 == 0: x //= 3; v += 1
    return v

def classify(C1, C2, aset):
    dnom = K
    for i in range(1, m):
        d = (C1[i] - C2[i]) % MOD
        if d: dnom = min(dnom, i + v3(d))
    fr = 0
    for a in aset:
        L = 0
        for i in range(1, m):
            num = (pow(3, i, MOD) * ((C2[i] - C1[i]) % MOD)) % MOD
            den = ((pow(3, i, MOD) * a + C1[i]) % MOD) * ((pow(3, i, MOD) * a + C2[i]) % MOD) % MOD
            L = (L + num * pow(den, -1, MOD)) % MOD
        if v3(L) >= c - 1: fr += 1
    return dnom, fr / len(aset)

def exact_S(C1, C2):
    S = 0
    for a in U:
        r = 1
        for i in range(1, m):
            n_ = (pow(3, i, Q) * a + C1[i]) % Q
            d_ = (pow(3, i, Q) * a + C2[i]) % Q
            r = r * n_ % Q * invQ[d_] % Q
        S += chi[r]
    return abs(S) / phi

aset = U[::7][:24]  # fixed sample of units for deg_frac
res = {'deg': [], 'ctrl': []}
tries = 0
while (len(res['deg']) < 40 or len(res['ctrl']) < 40) and tries < 30000:
    tries += 1
    b1 = np.minimum(rng.geometric(0.5, m), 40); b2 = np.minimum(rng.geometric(0.5, m), 40)
    C1, C2 = consts(b1), consts(b2)
    dnom, fr = classify(C1, C2, aset)
    if dnom > c - 2: continue
    if fr > 0.2 and len(res['deg']) < 40:
        res['deg'].append((fr, exact_S(C1, C2)))
    elif fr == 0 and len(res['ctrl']) < 40:
        res['ctrl'].append((fr, exact_S(C1, C2)))
ctrl = np.array([s for _, s in res['ctrl']])
deg = np.array(res['deg'])
print(f"controls (deg_frac=0, n={len(ctrl)}):  max |S|/phi = {ctrl.max():.2e}   mean = {ctrl.mean():.2e}")
print(f"degenerate (deg_frac>0.2, n={len(deg)}): |S|/phi: min={deg[:,1].min():.3f} "
      f"mean={deg[:,1].mean():.3f} max={deg[:,1].max():.3f}")
print(f"   corr(deg_frac, |S|/phi) = {np.corrcoef(deg[:,0], deg[:,1])[0,1]:.3f}")
print(f"   nonzero (>1e-10) fraction among degenerate: {(deg[:,1]>1e-10).mean():.2f}")
