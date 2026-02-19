#!/usr/bin/env python3
"""
Chistyakov embedding of Z_2 into C, colored by Collatz stopping time.
Tests whether the Collatz orbit measure on the embedded fractal
deviates from Haar measure (which equals the fractal Hausdorff measure
by Chistyakov's Theorem 7).

Reference: D.V. Chistyakov, arXiv:math/0202089v1 (2002)
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import Normalize
from matplotlib import cm
import time

# ─────────────────────────────────────────────────────────────────────
# 1. Chistyakov embedding  Υ_s^(m) : Z_p → C
# ─────────────────────────────────────────────────────────────────────

def padic_val(n, p):
    """p-adic valuation: largest k such that p^k divides n."""
    if n == 0:
        return 999
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

def padic_digit(n, k, p):
    """k-th digit of n in base-p expansion (coefficient of p^k)."""
    return (n // (p ** k)) % p

def chistyakov_embed(x_arr, s, m='inf', p=2, Nmax=55):
    """
    Compute Υ_s^(m)(x) for array of positive integers x ∈ Z_p.

    Formula (Chistyakov eq.15):
      Υ_s^(m)(x) = (1 - s^{v(x)})/(1-s) + Σ_{n=v(x)}^∞ s^n χ_n^(m)(x)

    Characters (eq.14):
      χ_n^(m)(x) = exp(i2π/p · Σ_{k=0}^{m} x_{n-k} · p^{-k})
    where x_j is the j-th digit of x in base p (x_j = 0 for j < 0).

    For m='inf':
      χ_n^(∞)(x) = exp(i2π · {x / p^{n+1}}_p)
                  = exp(i2π · (x mod p^{n+1}) / p^{n+1})   for x ∈ Z_p.
    """
    x_arr = np.asarray(x_arr, dtype=np.int64)
    N = len(x_arr)
    result = np.zeros(N, dtype=complex)

    # Precompute p-adic valuations
    vals = np.array([padic_val(int(x), p) for x in x_arr], dtype=int)

    # First term: (1 - s^v(x)) / (1 - s)
    result += (1.0 - s ** vals) / (1.0 - s)

    # Sum over n = 0 .. Nmax
    for n in range(Nmax + 1):
        mask = (n >= vals)
        if not np.any(mask):
            continue

        # Compute χ_n^(m)(x)
        if m == 'inf' or m == np.inf:
            mod = p ** (n + 1)
            if mod > 2**62:
                phase = 2.0 * np.pi * x_arr.astype(float) / float(mod)
            else:
                phase = 2.0 * np.pi * (x_arr % mod).astype(float) / float(mod)
            chi = np.exp(1j * phase)
        elif m == 0:
            digit_n = np.zeros(N, dtype=int)
            for idx in range(N):
                digit_n[idx] = padic_digit(int(x_arr[idx]), n, p)
            chi = np.exp(1j * 2 * np.pi / p * digit_n.astype(float))
        else:
            # General finite m
            phase_sum = np.zeros(N, dtype=float)
            for k in range(int(m) + 1):
                j = n - k
                if j >= 0:
                    dig = np.zeros(N, dtype=int)
                    for idx in range(N):
                        dig[idx] = padic_digit(int(x_arr[idx]), j, p)
                    phase_sum += dig.astype(float) * (p ** (-k))
            chi = np.exp(1j * 2 * np.pi / p * phase_sum)

        result += np.where(mask, (s ** n) * chi, 0.0 + 0j)

    return result


# ─────────────────────────────────────────────────────────────────────
# 2. Collatz stopping times
# ─────────────────────────────────────────────────────────────────────

def collatz_stopping_times(N):
    """Total stopping time for n in [1..N] via DP."""
    sigma = np.zeros(N + 1, dtype=int)
    for n in range(2, N + 1):
        x, steps = n, 0
        while x >= n and x != 1:
            x = x // 2 if x % 2 == 0 else 3 * x + 1
            steps += 1
        sigma[n] = steps + sigma[x]
    return sigma


# ─────────────────────────────────────────────────────────────────────
# 3. Multifractal box-counting
# ─────────────────────────────────────────────────────────────────────

def multifractal_spectrum(Z, weights, n_scales=16):
    """
    Compute generalized dimensions D_q via box-counting.
    Returns dict {q: D_q} and diagnostic arrays.
    """
    pts = np.column_stack([Z.real, Z.imag])
    lo, hi = pts.min(0), pts.max(0)
    span = max(hi[0] - lo[0], hi[1] - lo[1]) * 1.01

    w = weights / weights.sum()
    qs = np.array([-3, -2, -1, 0, 1, 2, 3, 5])

    nb_arr = np.unique(np.logspace(
        np.log10(5),
        np.log10(min(600, int(np.sqrt(len(Z))))),
        n_scales
    ).astype(int))

    log_eps, log_Zq = [], {q: [] for q in qs}

    for nb in nb_arr:
        eps = span / nb
        ix = ((pts[:, 0] - lo[0]) / eps).astype(int).clip(0, nb - 1)
        iy = ((pts[:, 1] - lo[1]) / eps).astype(int).clip(0, nb - 1)
        keys = ix * nb + iy
        bm = np.bincount(keys, weights=w, minlength=nb * nb)
        bm = bm[bm > 0]
        if len(bm) < 3:
            continue
        log_eps.append(np.log(eps))
        for q in qs:
            if q == 1:
                log_Zq[q].append(-np.sum(bm * np.log(bm)))   # entropy
            else:
                log_Zq[q].append(np.log(np.sum(bm ** q)))

    log_eps = np.array(log_eps)
    dims = {}
    for q in qs:
        y = np.array(log_Zq[q])
        if len(y) < 4:
            dims[q] = np.nan
            continue
        if q == 0:
            dims[q] = -np.polyfit(log_eps, y, 1)[0]  # D_0 = -d log N / d log ε
        elif q == 1:
            dims[q] = np.polyfit(-log_eps, y, 1)[0]   # D_1 = d H / d log(1/ε)
        else:
            dims[q] = np.polyfit(log_eps, y, 1)[0] / (q - 1)
    return dims, qs, log_eps


# ─────────────────────────────────────────────────────────────────────
# 4. Main
# ─────────────────────────────────────────────────────────────────────

def main():
    t0 = time.time()

    # ── Parameters ──
    N = 150_000
    p = 2
    s_abs = 0.42
    s_arg = np.pi / 5
    s = s_abs * np.exp(1j * s_arg)
    D_s = np.log(p) / (-np.log(s_abs))
    s0 = np.sin(np.pi / p) / (1 + np.sin(np.pi / p))

    print(f"p = {p},  s = {s_abs:.2f} exp(iπ/{np.pi/s_arg:.0f}),  |s| = {s_abs}")
    print(f"s_0(p={p}) = {s0:.4f}  ({'OK' if s_abs < s0 else 'WARNING: |s| >= s_0'})")
    print(f"Scaling dimension D_s = {D_s:.4f}")

    # ── Compute embedding ──
    x_arr = np.arange(1, N + 1, dtype=np.int64)
    print(f"\nEmbedding {N:,} integers (m=∞) ...")
    t1 = time.time()
    Z = chistyakov_embed(x_arr, s, m='inf', p=p, Nmax=55)
    print(f"  done in {time.time()-t1:.1f}s")

    # Verify scaling relation Υ(px) = sΥ(x) + 1
    x_test = np.arange(1, 2001, dtype=np.int64)
    Y_x = chistyakov_embed(x_test, s, m='inf', p=p, Nmax=55)
    Y_px = chistyakov_embed(p * x_test, s, m='inf', p=p, Nmax=55)
    err = np.max(np.abs(Y_px - (s * Y_x + 1)))
    print(f"  Scaling check |Υ({p}x) - (sΥ(x)+1)| = {err:.2e}")

    # ── Stopping times ──
    print("Computing stopping times ...")
    t1 = time.time()
    sigma = collatz_stopping_times(N)
    stop = sigma[1:N + 1].astype(float)
    print(f"  done in {time.time()-t1:.1f}s  (mean σ = {stop.mean():.1f})")

    # ── Orbit visitation measure ──
    print("Computing Collatz orbit visitation counts ...")
    t1 = time.time()
    M_orbit = min(N, 40_000)
    visit = np.zeros(N + 1, dtype=float)
    for n0 in range(2, M_orbit + 1):
        x = n0
        while x != 1:
            if 1 <= x <= N:
                visit[x] += 1
            x = x // 2 if x % 2 == 0 else 3 * x + 1
    visit[1] += M_orbit - 1
    orbit_w = visit[1:N + 1].copy()
    orbit_w /= orbit_w.sum()
    haar_w = np.ones(N, dtype=float) / N
    print(f"  done in {time.time()-t1:.1f}s")

    # ── Multifractal spectra ──
    print("Computing D_q spectra ...")
    dims_h, qs, _ = multifractal_spectrum(Z, haar_w)
    dims_o, _, _  = multifractal_spectrum(Z, orbit_w)
    print("  done.")

    # ══════════════════════════════════════════════════════════════════
    # FIGURE 1  –  Main embedding + diagnostics   (2 × 3)
    # ══════════════════════════════════════════════════════════════════

    fig, ax = plt.subplots(2, 3, figsize=(21, 13.5))
    fig.suptitle(
        r"$\Upsilon_s^{(\infty)}(\mathbb{Z}_2)\;\hookrightarrow\;\mathbb{C}$"
        f"  —  $p=2$,  $s={s_abs}\\,e^{{i\\pi/5}}$,  "
        f"$D_s={D_s:.3f}$,  $N={N:,}$",
        fontsize=16, fontweight='bold', y=0.99)

    # (a) full embedding, colour = stopping time
    a = ax[0, 0]
    vmax_s = np.percentile(stop, 98)
    sc = a.scatter(Z.real, Z.imag, c=stop, s=0.04, alpha=0.55,
                   cmap='inferno', norm=Normalize(0, vmax_s), rasterized=True)
    a.set_title(r'(a) Colour $=$ stopping time $\sigma(n)$', fontsize=12)
    a.set_xlabel(r'Re $\Upsilon$'); a.set_ylabel(r'Im $\Upsilon$')
    a.set_aspect('equal')
    fig.colorbar(sc, ax=a, shrink=.75, label=r'$\sigma$')

    # (b) colour = 2-adic valuation
    a = ax[0, 1]
    v2 = np.array([padic_val(int(x), 2) for x in x_arr])
    sc2 = a.scatter(Z.real, Z.imag, c=v2, s=0.04, alpha=0.55,
                    cmap='viridis', norm=Normalize(0, 10), rasterized=True)
    a.set_title(r'(b) Colour $= v_2(n)$ (2-adic valuation)', fontsize=12)
    a.set_xlabel(r'Re $\Upsilon$'); a.set_ylabel(r'Im $\Upsilon$')
    a.set_aspect('equal')
    fig.colorbar(sc2, ax=a, shrink=.75, label=r'$v_2$')

    # (c) colour = log₂(n)  (shows how natural ordering maps into fractal)
    a = ax[0, 2]
    sc3 = a.scatter(Z.real, Z.imag, c=np.log2(x_arr), s=0.04, alpha=0.55,
                    cmap='coolwarm', rasterized=True)
    a.set_title(r'(c) Colour $= \log_2 n$', fontsize=12)
    a.set_xlabel(r'Re $\Upsilon$'); a.set_ylabel(r'Im $\Upsilon$')
    a.set_aspect('equal')
    fig.colorbar(sc3, ax=a, shrink=.75, label=r'$\log_2 n$')

    # (d) zoom n ∈ [1, 4096]
    a = ax[1, 0]
    Nz = 4096
    Zz = Z[:Nz]
    sz = stop[:Nz]
    sc4 = a.scatter(Zz.real, Zz.imag, c=sz, s=2, alpha=.8,
                    cmap='inferno', norm=Normalize(0, vmax_s), rasterized=True)
    a.set_title(rf'(d) Zoom $n\in[1,{Nz}]$, colour $=\sigma$', fontsize=12)
    a.set_xlabel(r'Re $\Upsilon$'); a.set_ylabel(r'Im $\Upsilon$')
    a.set_aspect('equal')
    fig.colorbar(sc4, ax=a, shrink=.75, label=r'$\sigma$')

    # (e) generalised dimension spectrum D_q
    a = ax[1, 1]
    dh = [dims_h.get(q, np.nan) for q in qs]
    do = [dims_o.get(q, np.nan) for q in qs]
    a.plot(qs, dh, 'bo-', lw=2.2, ms=9, label='Haar (uniform)', zorder=3)
    a.plot(qs, do, 'rs-', lw=2.2, ms=9, label='Collatz orbit', zorder=3)
    a.axhline(D_s, color='k', ls='--', alpha=.45,
              label=f'$D_s = {D_s:.3f}$ (theory)')
    a.set_xlabel('$q$', fontsize=13)
    a.set_ylabel('$D_q$', fontsize=13)
    a.set_title('(e) Multifractal spectrum $D_q$', fontsize=12)
    a.legend(fontsize=10)
    a.grid(True, alpha=.25)

    # (f) mean stopping time vs fractal radius
    a = ax[1, 2]
    mag = np.abs(Z)
    nbins = 80
    edges = np.linspace(np.percentile(mag, 1), np.percentile(mag, 99), nbins + 1)
    centres, means, errs = [], [], []
    for i in range(nbins):
        m = (mag >= edges[i]) & (mag < edges[i + 1])
        if m.sum() > 20:
            centres.append(.5 * (edges[i] + edges[i + 1]))
            means.append(stop[m].mean())
            errs.append(stop[m].std() / np.sqrt(m.sum()))
    centres, means, errs = map(np.array, (centres, means, errs))
    a.errorbar(centres, means, 2 * errs, fmt='o-', ms=3, lw=1, color='navy',
               ecolor='lightskyblue', label=r'$\langle\sigma\rangle$ vs $|\Upsilon|$')
    a.axhline(stop.mean(), color='red', ls='--', alpha=.5,
              label=f'global $\\langle\\sigma\\rangle = {stop.mean():.1f}$')
    a.set_xlabel(r'$|\Upsilon_s^{(\infty)}(n)|$', fontsize=12)
    a.set_ylabel(r'$\langle\sigma\rangle$', fontsize=12)
    a.set_title(r'(f) Stopping time vs fractal radius', fontsize=12)
    a.legend(fontsize=10); a.grid(True, alpha=.25)

    fig.tight_layout(rect=[0, 0, 1, .95])
    fig.savefig('/mnt/user-data/outputs/chistyakov_collatz_embedding.png',
                dpi=200, bbox_inches='tight')
    plt.close(fig)
    print(f"Figure 1 saved  ({time.time()-t0:.0f}s)")

    # ══════════════════════════════════════════════════════════════════
    # FIGURE 2  –  Orbits + density ratio   (2 × 2)
    # ══════════════════════════════════════════════════════════════════

    fig2, ax2 = plt.subplots(2, 2, figsize=(15, 14))
    fig2.suptitle(
        r"Collatz Trajectories and Orbit Measure on $\Upsilon_s^{(\infty)}(\mathbb{Z}_2)$",
        fontsize=15, fontweight='bold', y=.99)

    # (a) self-similar structure: even (blue) vs odd (red)
    a = ax2[0, 0]
    K = min(N, 8192)
    Zk = Z[:K]
    cols = np.where(x_arr[:K] % 2 == 0, 0, 1)
    a.scatter(Zk.real, Zk.imag, c=cols, s=.6, alpha=.7,
              cmap='bwr', rasterized=True)
    a.set_title('(a) Even (blue) vs Odd (red)', fontsize=12)
    a.set_xlabel(r'Re $\Upsilon$'); a.set_ylabel(r'Im $\Upsilon$')
    a.set_aspect('equal')

    # (b) trajectory paths
    a = ax2[0, 1]
    a.scatter(Zk.real, Zk.imag, c='lightgray', s=.3, alpha=.25, rasterized=True)

    starts = [27, 97, 871, 6171, 3711, 2463]
    cmap_t = plt.cm.tab10
    for ti, n0 in enumerate(starts):
        traj = [n0]
        x = n0
        while x != 1:
            x = x // 2 if x % 2 == 0 else 3 * x + 1
            traj.append(x)
        traj = np.array(traj, dtype=np.int64)
        traj = traj[traj <= K]
        if len(traj) < 2:
            continue
        Zt = chistyakov_embed(traj, s, m='inf', p=p, Nmax=55)
        c = cmap_t(ti / len(starts))
        a.plot(Zt.real, Zt.imag, '-', color=c, lw=1.3, alpha=.85,
               label=f'$n_0={n0}$')
        a.plot(Zt.real[0], Zt.imag[0], 'o', color=c, ms=5)
    a.set_title('(b) Collatz trajectories on fractal', fontsize=12)
    a.set_xlabel(r'Re $\Upsilon$'); a.set_ylabel(r'Im $\Upsilon$')
    a.set_aspect('equal')
    a.legend(fontsize=8, ncol=2, loc='upper left')

    # (c) density ratio  orbit / Haar on pixel grid
    a = ax2[1, 0]
    ng = 120
    xr = np.linspace(Z.real.min(), Z.real.max(), ng + 1)
    yr = np.linspace(Z.imag.min(), Z.imag.max(), ng + 1)
    Hh, _, _ = np.histogram2d(Z.real, Z.imag, [xr, yr], weights=haar_w)
    Ho, _, _ = np.histogram2d(Z.real, Z.imag, [xr, yr], weights=orbit_w)
    with np.errstate(divide='ignore', invalid='ignore'):
        ratio = np.where(Hh > 0, Ho / Hh, np.nan)
    im = a.imshow(ratio.T, origin='lower',
                  extent=[xr[0], xr[-1], yr[0], yr[-1]],
                  cmap='RdBu_r', vmin=0.15, vmax=6, aspect='equal',
                  interpolation='nearest')
    a.set_title('(c) Orbit / Haar density ratio', fontsize=12)
    a.set_xlabel(r'Re $\Upsilon$'); a.set_ylabel(r'Im $\Upsilon$')
    fig2.colorbar(im, ax=a, shrink=.75, label='ratio')

    # (d) σ distribution by angular sector
    a = ax2[1, 1]
    ang = np.angle(Z)
    n_sec = 8
    edges_a = np.linspace(-np.pi, np.pi, n_sec + 1)
    for i in range(n_sec):
        m = (ang >= edges_a[i]) & (ang < edges_a[i + 1])
        if m.sum() > 200:
            a.hist(stop[m], bins=80, range=(0, vmax_s), density=True,
                   alpha=.2, color=plt.cm.hsv(i / n_sec),
                   label=f'sector {i+1}')
    a.set_xlabel(r'$\sigma(n)$', fontsize=12)
    a.set_ylabel('density', fontsize=12)
    a.set_title(r'(d) $\sigma$ distribution by angular sector', fontsize=12)
    a.legend(fontsize=7, ncol=2); a.grid(True, alpha=.25)

    fig2.tight_layout(rect=[0, 0, 1, .95])
    fig2.savefig('/mnt/user-data/outputs/chistyakov_collatz_orbits.png',
                 dpi=200, bbox_inches='tight')
    plt.close(fig2)
    print(f"Figure 2 saved  ({time.time()-t0:.0f}s)")

    # ══════════════════════════════════════════════════════════════════
    # FIGURE 3  –  Gallery   (2 × 3)
    # ══════════════════════════════════════════════════════════════════

    fig3, ax3 = plt.subplots(2, 3, figsize=(19, 12))
    fig3.suptitle(
        r"Gallery: Chistyakov Embeddings $\Upsilon_s^{(m)}(\mathbb{Z}_p)$"
        "  Coloured by Collatz $\\sigma$",
        fontsize=15, fontweight='bold', y=.99)

    gallery = [
        (2, 0,   1/3.0+0j,                  r'$p{=}2,\;m{=}0,\;s{=}1/3$ (Cantor)'),
        (2, 1,   0.42*np.exp(1j*np.pi/5),   r'$p{=}2,\;m{=}1,\;s{=}.42e^{i\pi/5}$'),
        (2,'inf', 0.42*np.exp(1j*np.pi/5),  r'$p{=}2,\;m{=}\infty,\;s{=}.42e^{i\pi/5}$'),
        (3, 0,   0.5+0j,                    r'$p{=}3,\;m{=}0,\;s{=}1/2$ (Sierpiński)'),
        (3,'inf', 0.42*np.exp(1j*np.pi/6),  r'$p{=}3,\;m{=}\infty,\;s{=}.42e^{i\pi/6}$'),
        (6, 0,   0.30+0j,                   r'$p{=}6,\;m{=}0,\;s{=}.30$ (Koch-type)'),
    ]

    Ng = 25_000
    xg = np.arange(1, Ng + 1, dtype=np.int64)
    sigma_g = collatz_stopping_times(Ng)
    sg = sigma_g[1:Ng + 1].astype(float)
    vmax_g = np.percentile(sg, 98)

    for idx, (pp, mm, ss, label) in enumerate(gallery):
        a = ax3[idx // 3, idx % 3]
        Zg = chistyakov_embed(xg, ss, m=mm, p=pp, Nmax=40)
        is_1d = np.all(np.abs(Zg.imag) < 1e-10)
        if is_1d:
            a.scatter(Zg.real, sg, c=sg, s=.25, alpha=.5,
                      cmap='inferno', norm=Normalize(0, vmax_g), rasterized=True)
            a.set_ylabel(r'$\sigma(n)$')
        else:
            a.scatter(Zg.real, Zg.imag, c=sg, s=.3, alpha=.55,
                      cmap='inferno', norm=Normalize(0, vmax_g), rasterized=True)
            a.set_ylabel(r'Im $\Upsilon$')
            a.set_aspect('equal')
        a.set_title(label, fontsize=11)
        a.set_xlabel(r'Re $\Upsilon$')
        D_g = np.log(pp) / (-np.log(abs(ss)))
        a.text(.02, .02, f'$D_s={D_g:.2f}$', transform=a.transAxes,
               fontsize=9, bbox=dict(fc='white', alpha=.7))

    fig3.tight_layout(rect=[0, 0, 1, .95])
    fig3.savefig('/mnt/user-data/outputs/chistyakov_gallery.png',
                 dpi=200, bbox_inches='tight')
    plt.close(fig3)
    print(f"Figure 3 saved  ({time.time()-t0:.0f}s)")

    # ── Print D_q table ──
    print(f"\n{'='*55}")
    print("MULTIFRACTAL SPECTRUM  D_q")
    print(f"{'='*55}")
    print(f"  Predicted  D_s = {D_s:.4f}")
    print(f"\n  {'q':>4s}  {'Haar':>10s}  {'Collatz':>10s}  {'Δ':>10s}")
    print("  " + "-" * 40)
    for q in qs:
        h = dims_h.get(q, np.nan)
        o = dims_o.get(q, np.nan)
        d = o - h if np.isfinite(h) and np.isfinite(o) else np.nan
        print(f"  {q:4d}  {h:10.4f}  {o:10.4f}  {d:+10.4f}")
    print(f"\n  Constant D_q → monofractal (= Haar).")
    print(f"  Varying  D_q → multifractal (Collatz ≠ Haar).")
    print(f"\nDone.  Total: {time.time()-t0:.0f}s")


if __name__ == '__main__':
    main()
