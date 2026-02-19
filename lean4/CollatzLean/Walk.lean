/-
  CollatzLean/Walk.lean
  The real-valued transverse walk u(t) = ν₂(t) - log₂(3)·ν₃(t),
  its increment rules, mean drift, and equilibrium threshold.
-/
import CollatzLean.Winding
import CollatzLean.BranchLocus
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option linter.style.nativeDecide false

namespace Collatz

open Real Finset

/-! ## The transverse walk -/

/-- The transverse walk: u(t) = ν₂(n,t) - log₂(3) · ν₃(n,t). -/
noncomputable def walk (n t : ℕ) : ℝ :=
  ↑(nu2 n t) - logb 2 3 * ↑(nu3 n t)

/-- The walk increment at step t: +1 if even, -log₂(3) if odd. -/
noncomputable def walkIncrement (n t : ℕ) : ℝ :=
  if isEvenStep n t then 1 else -(logb 2 3)

/-- The mean walk increment up to step t: walk(n,t) / t. -/
noncomputable def meanWalkIncrement (n t : ℕ) : ℝ :=
  walk n t / ↑t

/-- The equilibrium proportion: p_eq = 1 / (1 + log₂(3)). -/
noncomputable def p_equilibrium : ℝ := 1 / (1 + logb 2 3)

/-! ## Rational proxy for #eval -/

/-- Rational approximation of the walk using 8/5 for log₂(3). -/
def walk_approx (n t : ℕ) : ℚ :=
  ↑(nu2 n t) - (8 : ℚ) / 5 * ↑(nu3 n t)

/-! ## Base case -/

@[simp] theorem walk_zero (n : ℕ) : walk n 0 = 0 := by
  simp [walk]

/-! ## Step rules -/

/-- Even step: walk increases by 1. -/
theorem walk_step_even (n t : ℕ) (he : isEvenStep n t = true) :
    walk n (t + 1) = walk n t + 1 := by
  unfold walk
  rw [nu2_step_even n t he, nu3_step_even n t he]
  push_cast
  ring

/-- Odd step: walk decreases by log₂(3). -/
theorem walk_step_odd (n t : ℕ) (ho : isOddStep n t = true) :
    walk n (t + 1) = walk n t - logb 2 3 := by
  unfold walk
  rw [nu2_step_odd n t ho, nu3_step_odd n t ho]
  push_cast
  ring

/-! ## Increment characterization -/

/-- The walk increment matches the step rule. -/
theorem walk_increment_eq (n t : ℕ) :
    walk n (t + 1) = walk n t + walkIncrement n t := by
  by_cases he : isEvenStep n t = true
  · rw [walk_step_even n t he]
    simp [walkIncrement, he]
  · have hef : isEvenStep n t = false := by
      cases h : isEvenStep n t <;> simp_all
    have ho : isOddStep n t = true := by
      simp only [isEvenStep, isOddStep, decide_eq_true_eq] at *
      omega
    rw [walk_step_odd n t ho]
    unfold walkIncrement; rw [if_neg he]
    ring

/-! ## Walk as sum of increments -/

/-- The walk equals the sum of all increments. -/
theorem walk_eq_sum_increments (n t : ℕ) :
    walk n t = ∑ i ∈ Finset.range t, walkIncrement n i := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih, walk_increment_eq]

/-! ## Mean walk increment -/

/-- The mean walk increment equals 1 - (1 + log₂(3)) · (ν₃/t). -/
theorem meanWalkIncrement_eq (n t : ℕ) (ht : (t : ℝ) ≠ 0) :
    meanWalkIncrement n t = 1 - (1 + logb 2 3) * (↑(nu3 n t) / ↑t) := by
  unfold meanWalkIncrement walk
  have hpart : (nu2 n t : ℝ) = ↑t - ↑(nu3 n t) := by
    have h := nu_partition n t
    have : (nu2 n t : ℝ) + ↑(nu3 n t) = ↑t := by exact_mod_cast h
    linarith
  rw [hpart]
  field_simp
  ring

/-! ## Drift positivity -/

/-- If the odd proportion is below equilibrium, the drift is positive. -/
theorem drift_positive_of_podd_lt (p_odd : ℝ) (_hp : 0 ≤ p_odd)
    (hlt : p_odd < p_equilibrium) :
    1 - (1 + logb 2 3) * p_odd > 0 := by
  unfold p_equilibrium at hlt
  have hlog_pos : logb 2 3 > 0 :=
    logb_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 3)
  have h1log_pos : 1 + logb 2 3 > 0 := by linarith
  have : (1 + logb 2 3) * p_odd < 1 := by
    rwa [lt_div_iff₀ h1log_pos, mul_comm] at hlt
  linarith

/-! ## Pure-even cells force +1 increment -/

/-- At a pure-even cell, the walk increment is always +1. -/
theorem walkIncrement_at_pureEven (k : ℕ) [NeZero k] (cell : ZMod k × ZMod k)
    (N T : ℕ) (hpe : isPureEven k cell N T)
    (n t : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ N) (ht1 : 1 ≤ t) (ht2 : t ≤ T)
    (hcell : torusResidue k n t = cell) :
    walkIncrement n t = 1 := by
  have he := pureEven_forces_even k cell N T hpe n t hn1 hn2 ht1 ht2 hcell
  simp [walkIncrement, he]

/-! ## Evaluation -/

#eval walk_approx 7 20
#eval walk_approx 27 100

end Collatz
