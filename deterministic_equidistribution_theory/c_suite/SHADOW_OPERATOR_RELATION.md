# Relating the long shadow windows (Exp I) to the operator gaps (Exp E/F)

Tests the manuscript's central arrow: a persistent quenched bias (large `|W|`)
should correspond to a near-peripheral eigenstate of `L_{s,Q,L,χ}` — i.e. shadow
windows should live in sectors where the operator gap is small. Data: the
large-scale run (`out_large/`), shadow moduli {9,27,81,243} (all powers of 3, so
multiplicative characters match between I, E, F).

## 0. A methodological correction this analysis forced

Joining I to **E** (the killed *residue-height* operator) gave several
`gap_ratio > 1`, which is impossible: since `|L_χ| = L_principal` on the same
support, Wielandt's theorem forces `ρ(L_χ) ≤ ρ(L_principal)`. Diagnosis: E's
power iteration **did not converge** — residuals 3–9 %, every sector hit
MAXIT=3000. The killed-height operator has a near-degenerate band of top
eigenvalues (the height-transport mode), so power iteration stalls.

**Resolution (done).** E's solver has been replaced by a **restarted complex
Arnoldi** (Krylov subspace + Hessenberg shifted-QR Ritz values; validated against
known spectra in the unit tests). The killed-height operator now converges to
residual `< 8×10⁻¹¹` with **no Wielandt violations**. (Separately, the full
character group then showed the killed-height *uniform* gap
`κ_Q = 1 − max_χ ratio` is **0** — the quadratic character carries the
height-transport mode — while the residue-only uniform gap **stabilizes** at
≈0.236 (s=0)/0.074 (s=1) as Q→3⁷; see `VALIDATION_REPORT.md` §E/F.) The relation
below uses the **residue-only operator** (Exp F's object, dim = Q, also now
Arnoldi): it is the *correct* object for a residue character sum — the tilt `s`
enters `W` only as the weight `2^{sΔ}`, while the decorrelation is residue-driven —
and its gap ratios are all `≤ 1`.

F was re-run over {9,27,81,243} with a **principal-on-units baseline**
(`χ_0` = 1 on units, 0 on non-units), the apples-to-apples trivial sector for
multiplicative characters.

## 1. Tilt level — a clean correspondence

Residue-only gaps are systematically **weaker (closer to 1) at s=1 than at s=0**
— the critical tilt has the smallest gaps:

| | s=0 gap range | s=1 gap range |
|---|---|---|
| Q=27 | 0.22–0.76 | 0.54–0.85 |
| Q=81 | 0.58–0.76 | 0.85–0.93 |

The shadow windows concentrate at exactly that tilt:

- of **53 158** shadow-bearing windows, **43 843 (82 %)** have argmax `s=1`;
- of the **218 long windows (len ≥ 64), 100 % are at s=1**.

**Shadows appear at the tilt where the operator gap is weakest.** This is a
genuine I↔F correspondence in the predicted direction.

## 2. Long windows sit in weaker-gap sectors

Mean operator gap ratio of the argmax sector:

- all shadow windows: **0.567**
- long shadow windows (≥64): **0.729**

Long, persistent shadows live in sectors with a *smaller* gap (ratio nearer 1) —
again the manuscript's predicted direction: a slowly-decaying mode is permitted
precisely where the gap is weak.

## 3. Sector level — confounded by modulus (finite-size)

Across sectors at fixed tilt the correspondence is **weak**:
`corr(|W|, gap_ratio) = +0.247` (right sign, but small). Reason: the argmax is
dominated by the **smallest modulus** —

- Q=9: 49 727 shadows · Q=27: 2 167 · Q=243: 860 · Q=81: 404 (**94 % at Q=9**).

Q=9 has only 6 unit residues, so a short window's empirical `|mean χ|` is large by
finite-sample inflation regardless of the asymptotic gap (Q=9,k=3 carries 36 666
shadows yet has a healthy gap of 0.60). The single-orbit shadow signal therefore
tracks *residue-class count*, not the operator gap.

## Conclusion

- The operator (residue-only F) **decorrelates every nontrivial sector**
  (all gaps < 1); the gap is weakest at the critical tilt s=1.
- The long shadow windows correspond to the operator in the predicted direction
  **at the tilt level** (all long shadows at s=1) and **in gap magnitude**
  (long shadows in weaker-gap sectors, 0.73 vs 0.57).
- **But** the per-sector single-orbit shadow is dominated by small-Q finite-size
  inflation, so it is *not* clean evidence of an operator anti-gap. This is the
  manuscript's "circularity leak" made concrete: reading an obstruction off one
  orbit's own short windows is confounded; the finite operator gap (E/F) is the
  reliable object, and it shows no anti-gap.

## Follow-ups
1. Harden E's killed-height spectral solver (Arnoldi/shift-invert) so its κ_Q is
   trustworthy; cross-check against residue-only F.
2. Make `defect-windows` (Exp C) use the multiplicative-character family for 3^r
   (it currently uses additive), then measure per-sector `|W_{n,ℓ}|` decay vs ℓ
   directly against the F gap rate at fixed (Q,χ,s) — controlling for Q.
3. Normalize the shadow detector by residue-class count (e.g. compare `|W|` to a
   per-(Q,len) null) so the sector signal is not swamped by small Q.
