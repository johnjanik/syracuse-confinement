# Finite Spectral Shadows for the Collatz Valuation Cocycle

A research program on the Collatz/Syracuse map via a *deterministic defect
cocycle*: finite residue–height transfer operators, their coboundary
structure, and the quenched shadows that bad orbits must cast. Developed
across 33 critique-driven iterations (`critiques/dc_1.md` … `dc_33.md`),
with every computation and proof step recorded in the AIPM (`ailog`)
provenance trail (59 captures, validation passing).

## What this program proved, in one paragraph

Starting from a conjectural defect cocycle, it built and validated a
nine-experiment computational suite; classified the coboundaries exactly
(Cob = ⟨χ₂⟩: the quadratic character is valuation parity in disguise);
proved strict spectral gaps, conductor collapse, and the ejection theorem;
survived roughly ten exact marginal coincidences, each broken by a named
mechanism (the pinning constant C₀ < 1.355, the shell constant 3C₁ < 5.16,
the level-cost constant 4/7 < 3^(−1/2), the all-derivative grading lemmas,
the root-ball law); proved the uniform finite spectral gap
sup_c γ_c(0) ≤ (√3/2)^(1/2) + o(1) < 1 — the finite H23a theorem at s = 0;
proved the keystone arrow (every bad orbit casts a finite non-coboundary
two-point shadow); absorbed cycle elimination into the shadow framework via
linear forms in logarithms (every nontrivial cycle has x_min ≤ C·p^(τ+1));
and ended with genuinely new mathematics — *repetition rigidity*, by which
repeated valuation blocks are exact cycles (2-adic coding makes equal
blocks in a height band literally equal points), killing every Sturmian
and bounded-discrepancy subexponential-complexity ghost unconditionally.
What remains is stated with precision and without inflation: the quenched
shadow exclusion (the Collatz conjecture in minimal finite-shadow
language), with the surviving counterexample class characterized — words
that mimic randomness at every banded scale — and the S-unit/subspace
frontier named as the next tool.

## Contents

| Path | Description |
|---|---|
| `finite_spectral_shadows.tex/.pdf` | The manuscript (45 pp): full theorem stack, proofs, audits, open problems. |
| `finite_spectral_shadows_computational.tex/.pdf` | Companion report (7 pp): the experiment suite and analysis-script catalogue with headline constants. |
| `defect_cocycle.tex`, `collatz_defect_cocycle_c_specs.tex` | The original notes and suite specification the program began from. |
| `c_suite/collatz_tests/` | The nine-experiment C suite (Experiments A–I), FAST128/GMP builds, validation report. |
| `c_suite/analysis/` | The 14 audit scripts of the analytic campaign (threshold Schur, cascade operator, bounded shells, level-cost, root-ball, ghost tests, max-plus certificates, Sturmian realizability). Generated data (`out/`, `out_large/`) is gitignored and regenerable. |
| `critiques/` | The driving critique series dc_1–dc_33. |
| `.aipm/` | AI provenance store (`ailog validate` passes). |

## Machine verification

The elementary core of the repetition-rigidity argument is formalized in
Lean 4 (Mathlib v4.27.0) in the companion repository
[`collatz_notes`](https://github.com/johnjanik/collatz_notes):
`lean4/CollatzLean/FiniteSpectralShadows.lean` proves `word_congr` (the
2-adic coding lemma), `repetition_rigidity`, and `orbit_periodic_of_eq`
sorry-free, depending only on Lean's three standard axioms; the Baker
cycle bound is stated as the leading `proof_wanted` of the formal program.

## Status

- **Proved:** the finite H23a operator theorem (s = 0); keystone arrow;
  periodic exclusion via linear forms; repetition rigidity and the
  Sturmian/low-complexity exclusion; complexity–height tradeoff;
  calibrated-measure reduction; ~30 theorems/lemmas in total.
- **Open:** quenched shadow exclusion (`op:quenched` / `op:ctwo`) — the
  Collatz conjecture in minimal finite-shadow form; the s ∈ (0,1]
  extension; the S-unit/subspace second frontier for
  randomness-mimicking words.
