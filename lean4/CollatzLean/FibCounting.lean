/-
  CollatzLean/FibCounting.lean
  Fibonacci word counting for the golden mean shift,
  and the key numerical inequality log₂(3) < φ.
-/
import CollatzLean.SFT
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Topology.Order.Basic

set_option linter.style.nativeDecide false

open Real in
open scoped Real

namespace Collatz

/-! ## Avoid count: binary words of length n with no "11" -/

/-- Number of binary words of length n avoiding the bigram "11".
    Satisfies the Fibonacci recurrence: f(0)=1, f(1)=2, f(n+2)=f(n+1)+f(n). -/
def avoidCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => avoidCount (n + 1) + avoidCount n

/-! ## Relationship to Fibonacci numbers -/

/-- Strengthened induction: avoidCount n = fib(n+2) for all n. -/
private theorem avoidCount_eq_fib_pair (n : ℕ) :
    avoidCount n = Nat.fib (n + 2) ∧ avoidCount (n + 1) = Nat.fib (n + 3) := by
  induction n with
  | zero =>
    constructor
    · -- avoidCount 0 = 1 = fib 2
      native_decide
    · -- avoidCount 1 = 2 = fib 3
      native_decide
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨ih2, ?_⟩
    -- avoidCount (n + 2) = avoidCount (n + 1) + avoidCount n = fib (n+3) + fib (n+2) = fib (n+4)
    change avoidCount (n + 2) = Nat.fib (n + 4)
    have hdef : avoidCount (n + 2) = avoidCount (n + 1) + avoidCount n := rfl
    rw [hdef, ih2, ih1, Nat.add_comm (Nat.fib (n + 3))]
    exact (@Nat.fib_add_two (n + 2)).symm

theorem avoidCount_eq_fib (n : ℕ) : avoidCount n = Nat.fib (n + 2) :=
  (avoidCount_eq_fib_pair n).1

/-! ## Small verifications -/

theorem avoidCount_zero : avoidCount 0 = 1 := rfl
theorem avoidCount_one : avoidCount 1 = 2 := rfl
theorem avoidCount_two : avoidCount 2 = 3 := rfl
theorem avoidCount_three : avoidCount 3 = 5 := rfl
theorem avoidCount_four : avoidCount 4 = 8 := rfl
theorem avoidCount_five : avoidCount 5 = 13 := rfl

#eval (List.range 8).map avoidCount  -- [1, 2, 3, 5, 8, 13, 21, 34]

/-! ## The key inequality: log₂(3) < φ -/

/-- log₂(3) < 8/5, via 3⁵ = 243 < 256 = 2⁸. -/
theorem logb_two_three_lt : Real.logb 2 3 < 8 / 5 := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [Real.logb, div_lt_div_iff₀ hlog2_pos (by norm_num : (0 : ℝ) < 5)]
  -- Goal: Real.log 3 * 5 < 8 * Real.log 2
  have lhs : Real.log 3 * 5 = Real.log ((3 : ℝ) ^ 5) := by
    rw [Real.log_pow]; ring
  have rhs : 8 * Real.log 2 = Real.log ((2 : ℝ) ^ 8) := by
    rw [Real.log_pow]; ring
  rw [lhs, rhs]
  exact Real.log_lt_log (by positivity) (by norm_num)

/-- 8/5 < φ, via (11/5)² = 121/25 < 5 = (√5)². -/
theorem eight_fifths_lt_goldenRatio : (8 : ℝ) / 5 < (1 + Real.sqrt 5) / 2 := by
  suffices h : 11 / 5 < Real.sqrt 5 by linarith
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  exact lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg 5) (by rw [hsq]; norm_num)

/-- log₂(3) < φ (the golden ratio). -/
theorem log2_three_lt_goldenRatio : Real.logb 2 3 < (1 + Real.sqrt 5) / 2 :=
  calc Real.logb 2 3 < 8 / 5 := logb_two_three_lt
    _ < (1 + Real.sqrt 5) / 2 := eight_fifths_lt_goldenRatio

/-! ## Entropy: log(avoidCount n)/n → log φ -/

open Real Nat Filter in
open scoped goldenRatio Topology in
/-- Upper bound: fib(m+1) ≤ φ^m, from the golden ratio recurrence. -/
private lemma fib_succ_le_goldenRatio_pow (m : ℕ) :
    (Nat.fib (m + 1) : ℝ) ≤ goldenRatio ^ m := by
  have h := goldenRatio_mul_fib_succ_add_fib m
  have hineq : goldenRatio * ↑(Nat.fib (m + 1)) ≤ goldenRatio ^ (m + 1) := by
    linarith [Nat.cast_nonneg (α := ℝ) (Nat.fib m)]
  rw [pow_succ, mul_comm (goldenRatio ^ m)] at hineq
  exact le_of_mul_le_mul_left hineq goldenRatio_pos

open Real Nat Filter in
open scoped goldenRatio Topology in
/-- Lower bound: fib(m) ≥ φ^m/(2√5) for m ≥ 2, from Binet's formula. -/
private lemma goldenRatio_pow_div_le_fib (m : ℕ) (hm : 2 ≤ m) :
    goldenRatio ^ m / (2 * Real.sqrt 5) ≤ (Nat.fib m : ℝ) := by
  rw [coe_fib_eq]
  -- Goal: φ^m / (2 * √5) ≤ (φ^m - ψ^m) / √5
  -- Equivalent to: ψ^m ≤ φ^m / 2 (after clearing denominators)
  have h5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h2s5_pos : (0 : ℝ) < 2 * Real.sqrt 5 := by positivity
  suffices hsuff : goldenConj ^ m ≤ goldenRatio ^ m / 2 by
    have hsub : goldenRatio ^ m / 2 ≤ goldenRatio ^ m - goldenConj ^ m := by linarith
    have hrewrite : goldenRatio ^ m / (2 * Real.sqrt 5) =
        goldenRatio ^ m / 2 / Real.sqrt 5 := by rw [div_div]
    rw [hrewrite]
    exact div_le_div_of_nonneg_right hsub (le_of_lt h5_pos)
  have hψm_lt_one : goldenConj ^ m < 1 := by
    have hψ_abs : |goldenConj| < 1 := by
      rw [abs_lt]; exact ⟨by linarith [neg_one_lt_goldenConj], by linarith [goldenConj_neg]⟩
    calc goldenConj ^ m ≤ |goldenConj ^ m| := le_abs_self _
      _ = |goldenConj| ^ m := abs_pow _ _
      _ < 1 := pow_lt_one₀ (abs_nonneg _) hψ_abs (by omega)
  have hφm_gt_2 : 2 < goldenRatio ^ m := by
    calc (2 : ℝ) < goldenRatio + 1 := by linarith [one_lt_goldenRatio]
      _ = goldenRatio ^ 2 := goldenRatio_sq.symm
      _ ≤ goldenRatio ^ m := pow_le_pow_right₀ (le_of_lt one_lt_goldenRatio) hm
  linarith

/-- The topological entropy of the golden mean shift is log φ. -/
theorem goldenMean_entropy :
    Filter.Tendsto (fun n => Real.log (avoidCount n) / n) Filter.atTop
      (nhds (Real.log ((1 + Real.sqrt 5) / 2))) := by
  -- Reduce to fib(n+2)
  simp_rw [avoidCount_eq_fib]
  -- Constants
  have hφ_pos : (0 : ℝ) < (1 + Real.sqrt 5) / 2 := by positivity
  have hφ_gt_one : (1 : ℝ) < (1 + Real.sqrt 5) / 2 := by
    have : (1 : ℝ) < Real.sqrt 5 := by
      have h5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 from by norm_num)
      nlinarith [Real.sqrt_nonneg 5]
    linarith
  have hlogφ_pos : (0 : ℝ) < Real.log ((1 + Real.sqrt 5) / 2) := Real.log_pos hφ_gt_one
  -- Abbreviation for readability
  set logφ := Real.log ((1 + Real.sqrt 5) / 2) with hlogφ_def
  set M := logφ + |2 * logφ - Real.log (2 * Real.sqrt 5)| + 1
  -- First reduce: f → logφ iff f - logφ → 0
  suffices h : Filter.Tendsto
      (fun n : ℕ => Real.log (↑(Nat.fib (n + 2))) / ↑n - logφ)
      Filter.atTop (nhds 0) by
    have h2 := h.add_const logφ
    simp only [zero_add, sub_add_cancel] at h2
    convert h2 using 1
  -- Now apply squeeze_zero_norm
  apply squeeze_zero_norm' (a := fun n : ℕ => M / ↑n)
  · -- Bound: ‖log(fib(n+2))/n - logφ‖ ≤ M/n
    filter_upwards [Filter.eventually_ge_atTop 1] with n (hn : 1 ≤ n)
    rw [Real.norm_eq_abs]
    have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
    have hnn : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
    rw [show Real.log (↑(Nat.fib (n + 2))) / (↑n : ℝ) - logφ =
        (Real.log (↑(Nat.fib (n + 2))) - ↑n * logφ) / ↑n from by field_simp]
    rw [abs_div, abs_of_pos hn_pos]
    apply div_le_div_of_nonneg_right _ (le_of_lt hn_pos)
    -- Need: |log(fib(n+2)) - n * logφ| ≤ M
    have hφ_def : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
    have hlog_eq : Real.log Real.goldenRatio = logφ := by rw [hφ_def]
    have hfib_pos : 0 < Nat.fib (n + 2) := Nat.fib_pos.mpr (by omega)
    have hfib_real : (0 : ℝ) < ↑(Nat.fib (n + 2)) := Nat.cast_pos.mpr hfib_pos
    -- Upper: fib(n+2) ≤ φ^(n+1), so log(fib(n+2)) ≤ (n+1)*logφ
    have hupper := fib_succ_le_goldenRatio_pow (n + 1)
    rw [show n + 1 + 1 = n + 2 from by omega] at hupper
    have hlog_upper : Real.log (↑(Nat.fib (n + 2))) ≤ (↑n + 1) * logφ := by
      have h1 := Real.log_le_log hfib_real hupper
      rw [Real.log_pow, hlog_eq, show (↑(n + 1) : ℝ) = ↑n + 1 from by push_cast; ring] at h1
      exact h1
    -- Lower: fib(n+2) ≥ φ^(n+2)/(2√5), so log(fib(n+2)) ≥ (n+2)*logφ - log(2√5)
    have h2s5_pos : (0 : ℝ) < 2 * Real.sqrt 5 := by positivity
    have hlower := goldenRatio_pow_div_le_fib (n + 2) (by omega)
    have hlog_lower : (↑n + 2) * logφ - Real.log (2 * Real.sqrt 5) ≤
        Real.log (↑(Nat.fib (n + 2))) := by
      have hdiv_pos : (0 : ℝ) < Real.goldenRatio ^ (n + 2) / (2 * Real.sqrt 5) :=
        div_pos (pow_pos Real.goldenRatio_pos _) h2s5_pos
      have h1 := Real.log_le_log hdiv_pos hlower
      rw [Real.log_div (ne_of_gt (pow_pos Real.goldenRatio_pos _)) (ne_of_gt h2s5_pos),
          Real.log_pow, hlog_eq, show (↑(n + 2) : ℝ) = ↑n + 2 from by push_cast; ring] at h1
      exact h1
    -- Combine via abs_le
    rw [abs_le]
    constructor
    · -- -M ≤ x: lower bound gives x ≥ 2*logφ - log(2√5) ≥ -|…| ≥ -M
      have h1 : -(|2 * logφ - Real.log (2 * Real.sqrt 5)|) ≤
          2 * logφ - Real.log (2 * Real.sqrt 5) := neg_abs_le _
      linarith
    · -- x ≤ M: upper bound gives x ≤ logφ ≤ M
      have h1 : 0 ≤ |2 * logφ - Real.log (2 * Real.sqrt 5)| := abs_nonneg _
      linarith
  · -- M/n → 0
    have h_inv : Filter.Tendsto (fun n : ℕ => (↑n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simp_rw [div_eq_mul_inv]
    simpa [mul_zero] using (tendsto_const_nhds (x := M)).mul h_inv

/-- Under the measure of maximal entropy on the golden mean shift,
    the maximum density of 1s (odd steps) is 1/φ² = (3 - √5)/2. -/
theorem goldenMean_max_p_odd :
    (1 : ℝ) / ((1 + Real.sqrt 5) / 2) ^ 2 = (3 - Real.sqrt 5) / 2 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h5_3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by
    have : Real.sqrt 5 ^ 3 = Real.sqrt 5 ^ 2 * Real.sqrt 5 := by ring
    rw [this, h5]
  have hpos : (0 : ℝ) < 1 + Real.sqrt 5 := by positivity
  field_simp
  nlinarith [h5, h5_3]

/-! ## Evaluation -/

#eval avoidCount 10   -- 144 = fib 12
#eval Nat.fib 12      -- 144

end Collatz
