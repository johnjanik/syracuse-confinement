# Validation Report — collatz_tests (large-scale run)

Results from a large-scale sweep (`out_large/`, FAST128 release build,
2026-06-09). These supersede the earlier exploratory numbers and confirm each
experiment against its spec pre-registration. Exact commands are in
`run_large.sh`; every CSV carries a provenance header (commit, compiler, build,
command, UTC timestamp).

## H — congruence gate (the load-bearing identity)
Verifies `x_n ≡ Σ_{k=1}^r 3^{k-1} 2^{-(b_{n-k}+…+b_{n-1})} (mod 3^r)`, flagged by
the critique (`critiques/dc_1.md`) as unverified before reliance.

- FAST128, seeds 3–999 999, r≤8, 6 sampled n: **23 905 968 / 23 905 968 match**, 0 overflow.
- (earlier) GMP, seed 9 999 999 999 999 999, r=12, n up to 155 (values ≫ 2¹²⁸): **144/144**.

**PASS.** ~24M checks; the identity holds and downstream code may rely on it.

## A — height-tail census (octaves 10–28, 100k seeds/octave)
Pre-registered: `log2 Pr(h≥H) ≈ −H + C`.

- Octave 24: per-step slope of `log2(tail/seeds)` over H=3…11 averages **≈ −0.97**
  (−0.96, −0.97, −1.04, −1.02, −0.97, −0.94, −1.06, −0.91, −0.85); steeper in the
  low-count tail (H≥12). Max height climbs with octave (24.3 at N=28).

**PASS** — slope −1 confirmed.

## B — Cramér-tilt law (octave 26, 200k seeds, `--crit-mode height`)
Pre-registered: critical-excursion bulk → `p^(1)_b = 3·4^{−b}`,
entropy-per-digit → `H₂(3/4)=0.8113`.

- Boundary-excluded **middle** segments, length ≥16 (**103 976** segments):
  `p̂ = (0.657, 0.229, 0.089, 0.021)` — between annealed `(.5,.25,.125,.0625)`
  and critical `(.75,.1875,.0469,.0117)`; **KL→p^(1) = 0.093 ≪ KL→annealed = 0.191**;
  entropy/digit **0.870** (→ 0.811).

**PASS** — at scale the bulk sits decisively closer to the Cramér tilt than to
annealed (gap roughly doubled vs the small run).

## C — defect windows (50 long-orbit seeds, Q=9/27/81, s=0/0.5/1)
Pre-registered: ordinary windows decay; no persistent residue resonance.

- `|W|` at s=0 (Q=27, k=1) decreases with window length:
  0.31 (L16) → 0.24 (L32) → 0.20 (L77) → 0.11 (L116). |W| rises slightly with
  tilt (0.241→0.274 from s=0→1 at L32). Single-orbit windows stay short
  (orbits terminate at 1); the asymptotic decay lives in E/F.

## D — post-exit taboo (octave 24, 100k seeds)
Pre-registered: post-exit windows separated from `p^(1)` and/or `M_post(1)<1`.

- **6 496** windows: **KL→p = 0.177 ≪ KL→p^(1) = 0.576**, mean
  `M_post(1) = 0.989 < 1` (53 % subcritical).

**PASS** — post-exit relaxes toward annealed, away from the critical tilt.

## E — exact operator gaps (Q=9/27/81/243, L=48, R=6, Bmax=20, 4 tilts, 4 chars)
Pre-registered: nontrivial sectors below trivial, `ρ(L_χ) ≤ (1−κ_Q)ρ(L_0)`.

- Every nontrivial sector strictly below trivial. Per-(Q,s) **κ_Q** (= 1 − min
  gap ratio over characters):

  | Q | s=0 | s=0.5 | s=1 | s=1.5 |
  |---|----|----|----|----|
  | 9   | 0.094 | 0.099 | 0.122 | 0.204 |
  | 27  | 0.183 | 0.162 | 0.136 | 0.101 |
  | 81  | 0.306 | 0.317 | 0.371 | 0.418 |
  | 243 | 0.315 | 0.316 | 0.272 | 0.160 |

**Solver:** the killed-height operator has a near-degenerate band of top
eigenvalues (the height-transport mode) on which power iteration stalls — it
formerly returned residuals of 3–9 % and even `gap_ratio > 1` (impossible by
Wielandt, `ρ(L_χ) ≤ ρ(L_0)`). It is now solved by a **restarted complex Arnoldi**
(Krylov dimension grown to convergence; validated against known spectra in the
unit tests). All sectors now converge to **residual < 8×10⁻¹¹** with **no
Wielandt violations**, so the κ_Q below are reliable.

**Definition correction.** A *uniform* gap means `ρ(L_χ) ≤ (1−κ_Q)ρ(L_0)` for
**all** nontrivial χ, so it is governed by the **worst** character:
`κ_Q = 1 − max_χ [ρ(L_χ)/ρ(L_{χ₀})]`. (An earlier note mistakenly reported
`1 − min`, the *best*-gapped character, over only the first four characters — a
much larger and misleading number. The full character group, computed via
conjugate symmetry `k = 1..⌊φ/2⌋`, corrects this.)

**Killed-height, `sync` coupling: no uniform gap, κ_Q = 0.** For the full group
at Q = 9, 27, 81 the maximum gap ratio is **exactly 1.0**, at the **quadratic
character** (k = φ/2): `ρ(L_χ) = ρ(L_{χ₀})` to machine precision. This is
**structural, not a discretization artifact** — it stays exactly 1.0 across
R ∈ {2,4,6,8,12,16} and L ∈ {24…120}, even as ρ itself moves. Mechanism: the
height coordinate is ≈ n·log₂3 − Bₙ, so it encodes Bₙ, and the quadratic
character's 2-adic factor χ(2)⁻ᵇ = (−1)ᵇ accumulates to (−1)^{Bₙ} — a
**coboundary of the residue-height skew product**. In the faithful skew product
(one b drives both residue and height) the quadratic character is therefore
removable, and no change to the height *geometry* can gap it. **This is now
proved analytically** (see the appendix of `defect_cocycle_with_findings.tex`):
χ₂ factors through reduction mod 3, χ₂(S(x)) = (−1)^b, so on the
residue × (Bₙ mod 2) skew product the potential d(a,τ)=χ₂(a)(−1)^τ trivializes
χ₂ (giving ρ(L_{χ₂})=ρ(L₀)); the residue-only ratio is exactly
(2^{1+s}−1)/(2^{1+s}+1) = 1/3 (s=0), 3/5 (s=1), matching F; and only the
quadratic character is removable (χ(3a+1) is non-constant for order >2).

**Killed-height, `factored` coupling: the rebuild that inherits the residue gap.**
`--height-mode factored` builds `M = L_res(χ) ⊗ T_height`: the height contributes
a residue-independent survival factor and the character twists only the residue
factor (so b no longer synchronizes residue and height). Then the quadratic
character is gapped — ratio **0.333 (s=0) / 0.600 (s=1)**, the residue-only value
— and the uniform κ_Q equals the residue gap exactly: **0.345 (Q=9) → 0.236
(Q≥27)** at s=0, **0.092 → 0.074** at s=1, matching F sector-by-sector. Since the
Kronecker height factor cancels in every gap ratio, this holds for all Q (F
confirms stabilization to Q=2187). The killed operator now **inherits the
stabilizing residue gap and gaps every character**, including the quadratic one.

## F — exact residue-only gap, full character group (Q=9..2187, Bmax=28)

The residue-only operator (dim Q) is the object that actually governs the residue
Weyl sum. Full-group uniform gap `κ_Q = 1 − max_χ ratio`:

| Q | φ | κ_Q (s=0) | κ_Q (s=1) | worst-χ freq k/φ |
|---|---|----|----|----|
| 9   | 6   | 0.345 | 0.092 | ~0.33 / 0.33 |
| 27  | 18  | 0.236 | 0.092 | ~0.22 / 0.33 |
| 81  | 54  | 0.236 | 0.074 | ~0.22 / 0.019 |
| 243 | 162 | 0.236 | 0.074 | ~0.22 / 0.019 |
| 729 | 486 | 0.236 | 0.074 | ~0.22 / 0.019 |
| 2187| 1458| 0.236 | 0.074 | ~0.22 / 0.019 |

**κ_Q stabilizes** (s=0 → 0.236, s=1 → 0.074), bounded well away from 0, and the
worst character sits at a **fixed frequency**, not at k=1. The lowest-frequency
character k=1 — where the annealed `1−|p̂(1/φ)|` decays to 0 (0.42 → 2×10⁻⁵ as
Q→2187) — is in fact gapped by the **exact** operator by 0.24–0.78, i.e. the exact
operator gaps low frequencies **far more** than the i.i.d. shadow predicts.

**Finding (the finiteness leak, residue-only):** the annealed prediction that the
gap closes at low frequency is **refuted** — the exact residue operator keeps a
uniform gap bounded away from 0 as Q→∞ over the tested range (3²→3⁷). The
"finiteness leak" is not realized for the residue operator. Reconciles with the
shadow analysis: the residue-only operator is the right object, and it gaps
every sector; the killed-height κ_Q=0 is a height-coupling artifact.

(Annealed vs exact, as before: `corr(exact_s0, annealed) = 0.38`, mean
deviation 0.25 — the exact gap is not the i.i.d. Fourier value, here decisively
*larger* at low frequency.)

## G — trace / determinant shadows (Q=9/27, small L)
- `tr(L¹)=0`, `tr(L²)=1.25`, `tr(L³)=0`, `tr(L⁴)=0.594`; `det(1−zL)` smooth and
  positive — no spurious peripheral structure at small (Q,L).

## E/F decision — which operator powers H23a

The faithful **`sync`** skew product, on the **coboundary-quotient** character
family, relative to the **valuation-pushforward** residue reference. Rationale:
- H23a is an *inverse* argument, so the operator's ρ must govern the actual W_n;
  only `sync` (one b drives residue + height, matching the orbit) qualifies.
- `factored` reports a gap at χ₂, but W_n(χ₂,0) → −1/3 (mean −0.353 over 3.2e4
  orbits) — it does **not** decay. `factored`'s χ₂ gap is a mirage (false
  negative); `sync` correctly gives ρ(L_{χ₂})=ρ(L₀).
- χ₂ is a coboundary (proved): the residues are non-uniform mod 3 (ratio 1/3:2/3
  = valuation-parity pushforward), so χ₂ is part of the *reference*, not an
  obstruction. H23a runs on the quotient by coboundaries.
- There `sync` has a positive, Q-uniform gap: worst non-coboundary character at
  ξ=1/6 with ratio **0.9069 → κ_Q ≈ 0.0931**, identical for **Q=9,27,81,243** and
  both tilts — comfortably ≳ 1/polylog(Q).
`factored`/residue-only are kept as diagnostics (pure residue gap
(2^{1+s}−1)/(2^{1+s}+1), κ 0.236/0.074). See `defect_cocycle_with_findings.tex`
§"Which operator powers H23a".

**The gap is constant (by conductor), not just polylog.** Each conductor-3^c
character's twisted operator lives on the mod-3^c reduction, which is *autonomous*
((3a+1) mod 3^c depends only on a mod 3^{c-1}), so its gap is r-independent. Gap
ratio by conductor (r-independent, s=0): 3(χ₂)=1.000 [coboundary], **9=0.9069**,
27=0.8530, 81=0.8261, 243=0.7306. The worst non-coboundary sector is the fixed
conductor-9 (order-6) character → **κ_Q = κ₀ ≈ 0.0931 constant for all Q=3^r**,
governed by one fixed mod-9×height operator; higher conductors strictly more
gapped. (Proved: autonomy. Open: conductor-monotonicity via complete-fiber
cancellation — the Sync Quotient Gap Theorem program in the manuscript appendix.)
H23a restated: a gap for all **non-coboundary** characters (not all nontrivial).

## I — quenched spectral-shadow search (octaves 18–24, 80k/oct, Q=9/27/81/243)
`shadow_flag` = `max_{Q,χ,s}|W| ≥ δ` **and** `≥ 3×` a length-scaled null
(`rms(weights)/√len`), to defeat short-window + max-over-grid inflation.

- **1 254 232** windows; **53 158 (4.2 %)** shadow-bearing.
- By label: **critical_C_A 8.4 % > high_ascent 5.4 % > post_exit 3.2 %**
  (critical excursions likeliest to carry a residue shadow; post-exit least —
  taboo-consistent; `ordinary` n=46, 0 %).
- By length: shadow rate **grows monotonically** —
  0.3 % (8–15) → 2.9 % (16–31) → 7.2 % (32–63) → **100 % (64–127, n=218)**.

**Finding (stable at 1.25M windows):** long excursions almost always exceed the
decorrelation null — the candidate "spectral shadow made visible". Caveats:
long-window sample still modest (n=218); the √len null may weaken at large L.
Follow-up: relate flagged long windows to E/F operator gaps; scale Q and the
long-window sample.

## Open item
The "C_A-critical" definition is project-internal; `--crit-mode {height|vsq}`
defaults to `height`. Confirm the formal certificate before treating B/D/I
critical labels as canonical.

---
*Raw outputs in `out_large/` (git-ignored; `congruence_checks.csv` ≈ 0.7 GB).
Regenerate with `./run_large.sh`.*
