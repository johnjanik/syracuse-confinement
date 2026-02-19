/-
  CollatzLean/SkewProduct.lean

  The skew product structure of the Collatz map.

  Identifies the Collatz dynamics on the 2-adic integers Z₂ as a skew product:
    Base: the 2-adic odometer σ: Z₂ → Z₂ (adding 1)
    Fiber: the torus T = R/Z
    Cocycle: φ(x) = log₂3 if x is odd, 0 if x is even

  The dynamics are: (x, θ) ↦ (σ(x), θ + φ(x))

  The cocycle sum φ_n(x) = Σ_{i=0}^{n-1} φ(σ^i(x)) counts odd steps weighted
  by log₂3, which exactly matches walkCellError.

  Key proved results (all sorry-free, no axioms):
  - Cocycle tracking: cocycleSum = log₂3 · ν₃
  - Fiber coord = walk = walkCellError (identification)
  - Cocycle mean irrationality: log₂3/2 is irrational (Furstenberg input)
  - Deficit via cocycle: deficit = 2·ν₃ - ν₂
  - HasCompensatedRuns ↔ cocycle density condition
  - Cocycle shift during v₂=1 runs: d · log₂3 increase

  === Furstenberg's theorem and the gap ===

  Furstenberg (1961): For skew products over uniquely ergodic bases with
  irrational fiber rotation, the skew product is ergodic.

  The 2-adic odometer IS uniquely ergodic (Haar measure).
  The Collatz cocycle HAS irrational mean log₂3/2.
  So the skew product IS ergodic by Furstenberg's theorem.

  However, ergodicity gives Birkhoff averages (ν₃/t → 1/3 for μ-a.e. x),
  NOT bounded deficit (∃ D, ∀ t, deficit(t) ≤ D). The gap between
  "time averages converge" and "deficit is bounded" is the open problem.
  See finite_deficit_bound in DiophantineRepeller.lean.

  NOTE (2026-02-19): The former `irrational_cocycle_ergodic` axiom claimed
  HasCompensatedRuns for all n ≥ 1. This is FALSE (SWC is false for n=27).
  The axiom has been removed. The proved infrastructure remains.
-/
import CollatzLean.SolenoidMixing
import CollatzLean.WeylEquidistribution

set_option linter.style.nativeDecide false

namespace Collatz

open Real

/-! ## Section 1: The cocycle (sorry-free)

  The Collatz cocycle φ(n, t) at step t is:
    log₂3  if step t is odd (×3+1 then ÷2)
    0      if step t is even (÷2 only)

  The cocycle sum φ_n(n, t) = Σ_{s<t} φ(n,s) = log₂3 · ν₃(n,t).
  This is exactly the "fiber coordinate" in the skew product. -/

/-- The Collatz cocycle at step t: log₂3 if odd, 0 if even. -/
noncomputable def collatzCocycle (n t : ℕ) : ℝ :=
  if isOddStep n t then logb 2 3 else 0

/-- The cocycle sum: total fiber displacement after t steps.
    This equals log₂3 · ν₃(n,t). -/
noncomputable def cocycleSum (n t : ℕ) : ℝ :=
  logb 2 3 * ↑(nu3 n t)

/-- Base case: cocycle sum at t=0 is 0. -/
@[simp] theorem cocycleSum_zero (n : ℕ) : cocycleSum n 0 = 0 := by
  simp [cocycleSum]

/-- The cocycle sum increments by the cocycle at each step. -/
theorem cocycleSum_step (n t : ℕ) :
    cocycleSum n (t + 1) = cocycleSum n t + collatzCocycle n t := by
  unfold cocycleSum collatzCocycle
  by_cases ho : isOddStep n t = true
  · simp only [ho, ↓reduceIte]
    rw [nu3_step_odd n t ho]; push_cast; ring
  · have hof : isOddStep n t = false := by
      cases h : isOddStep n t <;> simp_all
    simp only [hof, Bool.false_eq_true, ↓reduceIte]
    have hev : isEvenStep n t = true := by
      simp only [isEvenStep, isOddStep, decide_eq_true_eq] at *; omega
    rw [nu3_step_even n t hev]; simp

/-- The cocycle sum equals log₂3 · ν₃. -/
theorem cocycleSum_eq (n t : ℕ) : cocycleSum n t = logb 2 3 * ↑(nu3 n t) := rfl

/-! ## Section 2: Fiber coordinate = walkCellError (sorry-free)

  The fiber coordinate θ_t in the skew product is:
    θ_t = ν₂(n,t) - cocycleSum(n,t) = ν₂(n,t) - log₂3 · ν₃(n,t)

  This is EXACTLY walkCellError (= cellError(ν₂, ν₃) = walk). -/

/-- The fiber coordinate in the skew product: base position minus cocycle sum.
    This equals walkCellError(n,t) = walk(n,t). -/
noncomputable def fiberCoord (n t : ℕ) : ℝ :=
  ↑(nu2 n t) - cocycleSum n t

/-- The fiber coordinate equals the walk. -/
theorem fiberCoord_eq_walk (n t : ℕ) : fiberCoord n t = walk n t := by
  simp only [fiberCoord, cocycleSum, walk]

/-- The fiber coordinate equals walkCellError. -/
theorem fiberCoord_eq_walkCellError (n t : ℕ) :
    fiberCoord n t = walkCellError n t := by
  rw [fiberCoord_eq_walk, walk_eq_walkCellError]

/-- The fiber coordinate increments by the walkIncrement at each step:
    +1 at even steps (ν₂ increments, cocycle 0),
    -log₂3 at odd steps (ν₂ unchanged, cocycle log₂3). -/
theorem fiberCoord_step (n t : ℕ) :
    fiberCoord n (t + 1) = fiberCoord n t + walkIncrement n t := by
  rw [fiberCoord_eq_walk, fiberCoord_eq_walk]
  exact walk_increment_eq n t

/-! ## Section 3: The cocycle mean is irrational (sorry-free)

  The average cocycle value is:
    E[φ] = P(odd) · log₂3 + P(even) · 0 = P(odd) · log₂3

  For the 2-adic odometer, P(odd) = 1/2, so E[φ] = log₂3/2.
  Since log₂3 is irrational (proved in Baker.lean), log₂3/2 is also irrational. -/

/-- log₂3 / 2 is irrational. -/
theorem irrational_half_logb_two_three : Irrational (logb 2 3 / 2) := by
  intro ⟨q, hq⟩
  -- hq : (↑q : ℝ) = logb 2 3 / 2
  -- So logb 2 3 = 2 * q, contradicting irrational_logb_two_three
  exact irrational_logb_two_three ⟨2 * q, by push_cast; linarith⟩

/-- The mean cocycle value (log₂3 / 2) is irrational. This is the key
    arithmetic input for the ergodicity theorem. -/
theorem cocycle_mean_irrational : Irrational (logb 2 3 / 2) :=
  irrational_half_logb_two_three

/-! ## Section 4: Deficit tracking via cocycle (sorry-free)

  The deficit = 3·ν₃ - t can be expressed via the cocycle:
    deficit(n,t) = 3·ν₃(n,t) - t
                 = 3·ν₃(n,t) - (ν₂(n,t) + ν₃(n,t))  [by ν₂+ν₃=t]
                 = 2·ν₃(n,t) - ν₂(n,t)

  And the walk = ν₂ - log₂3·ν₃, so:
    deficit = -(walk + (log₂3 - 2)·ν₃)
    deficit ≤ 0 ↔ walk ≥ (2 - log₂3)·ν₃

  The sliding window condition (3·Δν₃ ≤ W) is equivalent to:
  the cocycle sum grows at most W/3 per window (i.e., ν₃ density ≤ 1/3). -/

/-- Deficit expressed via cocycle sum and fiber coordinate:
    deficit = -(fiberCoord) + (1 - log₂3) · ν₃ ... not quite.
    More precisely: deficit = 2·ν₃ - ν₂ (from ν₂ + ν₃ = t). -/
theorem deficit_eq_two_nu3_minus_nu2 (n t : ℕ) :
    deficit n t = 2 * ↑(nu3 n t) - ↑(nu2 n t) := by
  have hp := nu_partition n t
  simp only [deficit]; omega

/-- The HasCompensatedRuns condition is equivalent to:
    the cocycle sum grows by at most W/3 in log₂3 units over any window.
    Since cocycleSum = log₂3 · ν₃, this is: log₂3 · Δν₃ ≤ log₂3 · W/3,
    i.e., Δν₃ ≤ W/3, i.e., 3·Δν₃ ≤ W. -/
theorem compensated_runs_iff_cocycle_density (n W : ℕ) :
    HasCompensatedRuns n W ↔
    ∀ t, 3 * (nu3 n (t + W) - nu3 n t) ≤ W := by
  constructor
  · intro h t; exact h t
  · intro h t; exact h t

/-! ## Section 5: Cocycle shift algebra (sorry-free)

  Additional algebraic properties of the cocycle that connect
  to the existing infrastructure in SolenoidMixing.lean. -/

/-- The cocycle sum over a v₂=1 run: during d compressed odd steps
    (2d uncompressed), the cocycle sum increases by d · log₂3.
    This is the "fiber moves by d · log₂3" statement. -/
theorem cocycleSum_of_v2_run (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1) :
    cocycleSum n (t + 2 * d) = cocycleSum n t + ↑d * logb 2 3 := by
  simp only [cocycleSum]
  have h := nu3_of_v2_run n t d hn hodd hrun
  have : (nu3 n (t + 2 * d) : ℝ) = ↑(nu3 n t) + ↑d := by exact_mod_cast h
  rw [this]; ring

/-- The fiber coordinate shift during a v₂=1 run: exactly d · (1 - log₂3).
    This is cellError_shift_of_v2_run restated in fiber coordinates. -/
theorem fiberCoord_shift_of_v2_run (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1) :
    fiberCoord n (t + 2 * d) = fiberCoord n t + ↑d * (1 - logb 2 3) := by
  rw [fiberCoord_eq_walkCellError, fiberCoord_eq_walkCellError]
  exact cellError_shift_of_v2_run n t d hn hodd hrun

/-! ## Section 6: Why Furstenberg is necessary but not sufficient

  The skew product decomposition of the Collatz dynamics:

  1. BASE DYNAMICS (2-adic odometer):
     The sequence of parities (odd/even) of a Collatz trajectory is
     determined by the 2-adic expansion of the starting point.
     The odometer σ(x) = x+1 on Z₂ is uniquely ergodic (w.r.t. Haar).

  2. FIBER DYNAMICS (torus rotation):
     The walk/fiberCoord/walkCellError tracks the fiber coordinate.
     Each odd step rotates the fiber by log₂3 (irrational).
     Each even step rotates by 0.

  3. FURSTENBERG'S THEOREM (Furstenberg 1961):
     Since the base is uniquely ergodic and the fiber rotation has
     irrational mean (log₂3/2), the skew product is ergodic.

  4. WHAT ERGODICITY GIVES:
     Birkhoff averages: for μ-a.e. x ∈ Z₂,
       (1/T) Σ_{t<T} 1_{odd}(σ^t(x)) → 1/2.
     This means ν₃/t → 1/3 (in uncompressed steps), so
     deficit/t → 0 (sublinear deficit growth).

  5. WHAT ERGODICITY DOES NOT GIVE:
     Bounded deficit: ∃ D, ∀ t, deficit(t) ≤ D.
     Ergodicity gives deficit/t → 0, but not deficit = O(1).
     The former `irrational_cocycle_ergodic` axiom overclaimed by asserting
     HasCompensatedRuns (which requires 3·Δν₃ ≤ W for ALL windows starting
     from t=0, which is false for n=27).

     The correct gap is finite_deficit_bound (DiophantineRepeller.lean):
     ∃ D, ∀ t, deficit(t) ≤ D, equivalent to the Collatz conjecture.

  References:
  - H. Furstenberg, "Strict ergodicity and transformation of the torus",
    American Journal of Mathematics 83 (1961), 573–601.
  - W. Parry, "Topics in Ergodic Theory", CUP, 1981.
  - M. Einsiedler & T. Ward, "Ergodic Theory", Springer GTM 259, 2011, Ch. 9.
-/

/-! ## Summary

  === FILE STATUS ===

  Proved (no sorry):
  - cocycleSum_zero, cocycleSum_step, cocycleSum_eq
  - fiberCoord_eq_walk, fiberCoord_eq_walkCellError, fiberCoord_step
  - irrational_half_logb_two_three, cocycle_mean_irrational
  - deficit_eq_two_nu3_minus_nu2
  - compensated_runs_iff_cocycle_density
  - cocycleSum_of_v2_run, fiberCoord_shift_of_v2_run

  Sorry'd: 0
  Axioms: 0

  NOTE (2026-02-19): The former `irrational_cocycle_ergodic` axiom
  (asserting HasCompensatedRuns for all n ≥ 1) has been REMOVED because
  HasCompensatedRuns ↔ SlidingWindowCondition, which is false for n=27.
  The proved infrastructure (cocycle tracking, irrationality, fiber-walk
  identification) remains and supports the narrative in the manuscript.
-/

end Collatz
