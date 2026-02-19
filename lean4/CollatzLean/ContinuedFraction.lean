/-
  CollatzLean/ContinuedFraction.lean
  Continued fraction infrastructure for log₂3 ≈ 1.58496...

  The convergents p_k/q_k of the CF expansion give the best rational
  approximations to log₂3 and identify candidate (ν₂, ν₃) pairs for
  Collatz cycles. For each convergent, the gap |2^{p_k} - 3^{q_k}|
  bounds the minimum c₀ of any hypothetical cycle.

  Key results:
  1. CF coefficients and convergent computation verified by native_decide
  2. Power comparisons for convergents up to k=8 (~317-digit numbers)
  3. Gap computations and Steiner c₀ bounds for small convergents
  4. Steiner boundary analysis: Δ₃ ≤ 79 is optimal with Hercher m ≤ 91
  5. Extension table for larger Hercher thresholds

  References:
  - OEIS A028507: CF expansion of log(3)/log(2)
  - Steiner (1977): Cycle equation framework
  - Hercher (2024): No m-cycle for m ≤ 91
-/
import CollatzLean.Baker

set_option linter.style.nativeDecide false

namespace Collatz

namespace ContinuedFraction

/-! ## Continued fraction coefficients of log₂3

log₂3 = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, ...]

The partial quotients are from OEIS A028507. -/

/-- First 15 partial quotients of the CF expansion of log₂3. -/
def cfCoeffs : List ℕ := [1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55]

/-! ## Convergent computation -/

/-- Compute convergents from CF coefficients using the standard recurrence:
    p_n = a_n · p_{n-1} + p_{n-2},  q_n = a_n · q_{n-1} + q_{n-2}.
    Takes (p_{n-2}, p_{n-1}, q_{n-2}, q_{n-1}) as state. -/
def convergentsFrom : List ℕ → ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | [], _, _, _, _ => []
  | a :: rest, p2, p1, q2, q1 =>
    let p := a * p1 + p2
    let q := a * q1 + q2
    (p, q) :: convergentsFrom rest p1 p q1 q

/-- The convergents of log₂3 computed from the CF coefficients.
    Initialize with (p_{-2}, p_{-1}, q_{-2}, q_{-1}) = (0, 1, 1, 0).
    Even-indexed convergents underestimate log₂3 (so 2^p < 3^q).
    Odd-indexed convergents overestimate log₂3 (so 2^p > 3^q). -/
def log2_3_convergents : List (ℕ × ℕ) :=
  convergentsFrom cfCoeffs 0 1 1 0

/-! ## Convergent verification -/

/-- All 15 convergents verified against the standard recurrence. -/
theorem convergents_verified : log2_3_convergents = [
    (1, 1), (2, 1), (3, 2), (8, 5), (19, 12), (65, 41), (84, 53),
    (485, 306), (1054, 665), (24727, 15601), (50508, 31867),
    (125743, 79335), (176251, 111202), (301994, 190537),
    (16785921, 10590737)] := by native_decide

#eval log2_3_convergents

/-! ## Power comparisons: 2^p vs 3^q

Even convergents (k = 0, 2, 4, 6, 8): p/q < log₂3, so 2^p < 3^q.
Odd convergents (k = 1, 3, 5, 7): p/q > log₂3, so 2^p > 3^q.

Only odd convergents can be winding numbers for hypothetical cycles,
since cycles require 2^{ν₂} > 3^{ν₃} (from correction > 0). -/

-- Even convergents: 2^p < 3^q (these CANNOT be cycle winding numbers)
theorem pow2_lt_pow3_k0 : 2 ^ 1 < 3 ^ 1 := by native_decide
theorem pow2_lt_pow3_k2 : 2 ^ 3 < 3 ^ 2 := by native_decide
theorem pow2_lt_pow3_k4 : 2 ^ 19 < 3 ^ 12 := by native_decide
theorem pow2_lt_pow3_k6 : 2 ^ 84 < 3 ^ 53 := by native_decide
theorem pow2_lt_pow3_k8 : 2 ^ 1054 < 3 ^ 665 := by native_decide

-- Odd convergents: 2^p > 3^q (candidate cycle winding numbers)
theorem pow2_gt_pow3_k1 : 2 ^ 2 > 3 ^ 1 := by native_decide
theorem pow2_gt_pow3_k3 : 2 ^ 8 > 3 ^ 5 := by native_decide
theorem pow2_gt_pow3_k5 : 2 ^ 65 > 3 ^ 41 := by native_decide
theorem pow2_gt_pow3_k7 : 2 ^ 485 > 3 ^ 306 := by native_decide

/-! ## Gaps and Steiner c₀ bounds

For odd convergent (p, q) where 2^p > 3^q, the gap Δ = 2^p - 3^q
constrains the minimum c₀ via the cycle equation (Baker.lean):
  c₀ · (2^L - 3^K) = cycleCorrection c₀ p
Combined with correction_lower_bound (2·correction + 1 ≥ 3^K):
  c₀ ≥ (3^K - 1) / (2 · (2^L - 3^K)) -/

-- k=1 (L=2, K=1): gap = 1, min c₀ ≥ (3-1)/(2·1) = 1
theorem gap_k1 : 2 ^ 2 - 3 ^ 1 = 1 := by native_decide

-- k=3 (L=8, K=5): gap = 13, min c₀ ≥ ⌈(243-1)/(2·13)⌉ = ⌈9.31⌉ = 10
theorem gap_k3 : 2 ^ 8 - 3 ^ 5 = 13 := by native_decide
theorem steiner_c0_bound_k3 : (3 ^ 5 - 1) ≤ 10 * (2 * (2 ^ 8 - 3 ^ 5)) := by native_decide

-- Even convergent gaps (opposite direction, for reference)
-- k=2 (L=3, K=2): 3^2 - 2^3 = 1
theorem gap_k2 : 3 ^ 2 - 2 ^ 3 = 1 := by native_decide
-- k=4 (L=19, K=12): 3^12 - 2^19 = 7153
theorem gap_k4 : 3 ^ 12 - 2 ^ 19 = 7153 := by native_decide

/-! ## Convergents within Hercher range (q ≤ 91)

All convergents (p, q) with q ≤ 91 are covered by Hercher's theorem
(no m-cycle for m ≤ 91). The relevant convergents are k=0 through k=6:
  k=0: q=1, k=1: q=1, k=2: q=2, k=3: q=5, k=4: q=12, k=5: q=41, k=6: q=53
The first convergent beyond Hercher's range is k=7 with q=306 > 91. -/

theorem convergent_k5_in_hercher : 41 ≤ 91 := by omega
theorem convergent_k6_in_hercher : 53 ≤ 91 := by omega
theorem convergent_k7_beyond_hercher : 306 > 91 := by omega

/-! ## Steiner K-bound boundary analysis

For Δ₃ ≤ D with period p = 3D and Hercher threshold m ≤ M:
if ν₃ ≥ M+1 then ν₂ = p - ν₃ ≤ 3D - (M+1), and we need
2^{3D-(M+1)} < 3^{M+1} for contradiction with 2^{ν₂} > 3^{ν₃}.

With M = 91: max D such that 2^{3D-92} < 3^92 is D = 79.
This is why steiner_K_bound_79 in SteinerCycle.lean uses Δ₃ ≤ 79. -/

/-- Check whether the Steiner bound works for Hercher threshold M and max Δ₃ = D.
    Returns true iff 2^{3D - (M+1)} < 3^{M+1}, meaning any cycle with
    Δ₃ ≤ D and ν₃ > M can be ruled out by contradiction. -/
def steinerWorks (M D : ℕ) : Bool :=
  let nu3_min := M + 1
  let nu2_max := if 3 * D ≥ nu3_min then 3 * D - nu3_min else 0
  decide (2 ^ nu2_max < 3 ^ nu3_min)

-- Current state: M = 91 (Hercher 2024), optimal boundary at D = 79
theorem steiner_boundary_79 : steinerWorks 91 79 = true := by native_decide
theorem steiner_boundary_80 : steinerWorks 91 80 = false := by native_decide

-- Verify all D ≤ 79 work with M = 91
theorem steiner_all_79 : (List.range 80).all (steinerWorks 91) = true := by native_decide

/-! ## Extension table: what larger Hercher thresholds would unlock

Each unit increase in M gains about 0.86 units of Δ₃ coverage.
The relationship is max D ≈ (M+1) · log₂3 / 3 ≈ 0.528 · (M+1). -/

-- M = 92 → max D = 80 (one step beyond current)
theorem steiner_ext_92 : steinerWorks 92 80 = true := by native_decide
theorem steiner_ext_92_fail : steinerWorks 92 81 = false := by native_decide

-- M = 100 → max D = 87
theorem steiner_ext_100 : steinerWorks 100 87 = true := by native_decide
theorem steiner_ext_100_fail : steinerWorks 100 88 = false := by native_decide

-- M = 150 → max D = 130
theorem steiner_ext_150 : steinerWorks 150 130 = true := by native_decide
theorem steiner_ext_150_fail : steinerWorks 150 131 = false := by native_decide

-- M = 200 → max D = 173
theorem steiner_ext_200 : steinerWorks 200 173 = true := by native_decide
theorem steiner_ext_200_fail : steinerWorks 200 174 = false := by native_decide

-- Scaling analysis: (M, max D that works)
#eval (List.range 12).map fun i =>
  let M := 91 + i * 10
  let failD := (List.range 300).find? fun d => !steinerWorks M d
  (M, failD.map (· - 1))

end ContinuedFraction

end Collatz
