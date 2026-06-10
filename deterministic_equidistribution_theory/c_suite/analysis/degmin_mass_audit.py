"""Degenerate-minimum mass lemma audit (dc_19 sec 4.IV).

Pairs (w,w') of m-step valuation words, product measure p_0 x p_0 (s=0,
b_i ~ Geom(1/2)).  Interior constants C_i (i=1..m-1), Delta C_i = C_i - C'_i.
Nominal valuation   d_nom = min_i [ i + v3(Delta C_i) ].
True valuation at a: d_true(a) = v3( sum_i 3^i (C'_i - C_i) / ((3^i a + C_i)(3^i a + C'_i)) ).
Degenerate-to-stationary event: d_nom <= c-2  AND  d_true(a) >= c-1
(escapes the complete-sum vanishing lemma despite nominal nonstationarity).
"""
import numpy as np, sys

def v3_arr(x, cap):
    v = np.zeros(x.shape, np.int64); y = x.copy()
    zero = (y == 0); v[zero] = cap; active = ~zero
    for _ in range(cap):
        div = active & (y % 3 == 0)
        if not div.any(): break
        y[div] //= 3; v[div] += 1; active = div
    return np.minimum(v, cap)

def henselinv(u, MOD):
    x = np.where(u % 3 == 1, 1, 2).astype(np.int64)
    for _ in range(4):
        x = (x * ((2 - u * x) % MOD)) % MOD
    return x % MOD

def run(c, m, N, nA, seed):
    rng = np.random.default_rng(seed)
    K = c + 3; MOD = 3**K; Q = 3**c; PHI = 2 * 3**(c - 1)
    p2 = np.array([pow(2, k, MOD) for k in range(64)], np.int64)
    inv2Q = pow(2, -1, Q)
    i2Q = np.array([pow(inv2Q, k, Q) for k in range(PHI)], np.int64)
    b1 = np.minimum(rng.geometric(0.5, (N, m)), 50).astype(np.int64)
    b2 = np.minimum(rng.geometric(0.5, (N, m)), 50).astype(np.int64)
    aU = []
    while len(aU) < nA:
        x = int(rng.integers(1, Q))
        if x % 3: aU.append(x)
    aU = np.array(aU, np.int64)
    C1 = np.ones(N, np.int64); C2 = np.ones(N, np.int64)   # C_1 = 1
    P1 = np.ones(N, np.int64); P2 = np.ones(N, np.int64)   # 2^{B_i} mod MOD
    B1 = np.zeros(N, np.int64); B2 = np.zeros(N, np.int64)
    dnom = np.full(N, K, np.int64)
    L = np.zeros((N, nA), np.int64)
    for i in range(1, m):            # use C_i, i = 1..m-1
        dC = (C1 - C2) % MOD
        vi = i + v3_arr(dC, K)
        dnom = np.minimum(dnom, np.where(dC == 0, K, np.minimum(vi, K)))
        t3 = pow(3, i, MOD)
        num = (t3 * ((C2 - C1) % MOD)) % MOD
        for j in range(nA):
            den = (((t3 * aU[j]) % MOD + C1) % MOD) * (((t3 * aU[j]) % MOD + C2) % MOD) % MOD
            L[:, j] = (L[:, j] + num * henselinv(den, MOD)) % MOD
        # advance C_i -> C_{i+1} = 3 C_i + 2^{B_i}
        P1 = (P1 * p2[b1[:, i - 1]]) % MOD; B1 += b1[:, i - 1]
        P2 = (P2 * p2[b2[:, i - 1]]) % MOD; B2 += b2[:, i - 1]
        C1 = (3 * C1 + P1) % MOD
        C2 = (3 * C2 + P2) % MOD
    # endpoint: C_m = current C after loop ran to i=m-1 then advanced -> C_m; B_m adds last b
    B1 += b1[:, m - 1]; B2 += b2[:, m - 1]
    E1 = (C1 % Q) * i2Q[B1 % PHI] % Q
    E2 = (C2 % Q) * i2Q[B2 % PHI] % Q
    matched = (E1 == E2) & ((B1 - B2) % 2 == 0)
    nominal_ns = dnom <= c - 2
    dtrue = v3_arr(L % MOD, K)                      # (N, nA)
    deg = (dtrue >= c - 1) & nominal_ns[:, None]    # degenerate-to-stationary per a
    degfrac = deg.mean(axis=1)
    # level-cost histogram (first a-column, nominal nonstationary pairs)
    lift = (dtrue[:, 0] - dnom)[nominal_ns]
    hist = np.bincount(np.clip(lift, 0, 8), minlength=9) / max(len(lift), 1)
    out = dict(c=c, m=m, N=N,
               P_nom_ns=nominal_ns.mean(),
               M_deg=degfrac.mean(),
               P_match=matched.mean(),
               M_deg_matched=degfrac[matched].mean() if matched.any() else float('nan'),
               n_match=int(matched.sum()),
               hist=hist)
    return out

if __name__ == "__main__":
    print(f"{'c':>2} {'m':>3} {'P[dnom<=c-2]':>12} {'M_deg':>10} {'P_match':>9} "
          f"{'M_deg|match':>11} {'#match':>7}   P[lift>=k], k=1..4")
    for c, m, N, nA, seed in [(5,5,2_000_000,9,1),(5,7,2_000_000,9,2),(5,10,2_000_000,9,3),
                              (6,6,2_000_000,9,4),(6,8,2_000_000,9,5),(6,12,2_000_000,9,6),
                              (7,7,2_000_000,6,7),(7,14,2_000_000,6,8)]:
        r = run(c, m, N, nA, seed)
        tail = 1 - np.cumsum(r['hist'])
        print(f"{r['c']:>2} {r['m']:>3} {r['P_nom_ns']:>12.4f} {r['M_deg']:>10.3e} "
              f"{r['P_match']:>9.5f} {r['M_deg_matched']:>11.3e} {r['n_match']:>7d}   "
              + " ".join(f"{tail[k]:.4f}" for k in range(4)))
        sys.stdout.flush()
