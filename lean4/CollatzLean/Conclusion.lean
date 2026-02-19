/-
  CollatzLean/Conclusion.lean
  The Collatz conjecture: every n ≥ 1 eventually reaches 1.

  Critical path (only sorry: nu3_linear_bound):
    nu3_linear_bound (sorry: ∃ K T₀, ∀ t ≥ T₀, 3·ν₃ ≤ t + K) →
    reaches_one_of_linear_drift (CorrectionRatio.lean) →
      trajectory bounded → eventually periodic →
      cycle is trivial (Δ₃=0,1 proved; Δ₃≥2 equality case via Baker) →
    collatz_conjecture

  Off critical path: the ε-drift and walk divergence machinery in Drift.lean
  is proved but unused — the K-bound alone drives the proof.
-/
import CollatzLean.CorrectionRatio
import CollatzLean.CollatzSFT
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option linter.style.nativeDecide false

namespace Collatz

open Real

/-! ## From power bound to seq = 1

The following two lemmas are **correct** given their hypotheses. They document
the original proof strategy: if one could bound the correction term uniformly,
walk divergence would imply convergence. The difficulty is that no uniform
correction bound `correction n t ≤ C * 3^(nu3 n t)` exists.

These are retained for documentation; the actual proof chain now goes through
CorrectionRatio.lean instead. -/

/-- If (n + C) · 3^ν₃ < 2 · 2^ν₂, then collatzSeq n t = 1. -/
theorem seq_eq_one_of_pow_bound (n t C : ℕ) (hn : n ≥ 1)
    (hC : ∀ s, correction n s ≤ C * 3 ^ nu3 n s)
    (hpow : (n + C) * 3 ^ nu3 n t < 2 * 2 ^ nu2 n t) :
    collatzSeq n t = 1 := by
  have hid := collatz_identity n t
  have hcorr := hC t
  have hle : collatzSeq n t * 2 ^ nu2 n t ≤ (n + C) * 3 ^ nu3 n t :=
    calc collatzSeq n t * 2 ^ nu2 n t
        = n * 3 ^ nu3 n t + correction n t := hid
      _ ≤ n * 3 ^ nu3 n t + C * 3 ^ nu3 n t := Nat.add_le_add_left hcorr _
      _ = (n + C) * 3 ^ nu3 n t := by ring
  have hlt : collatzSeq n t * 2 ^ nu2 n t < 2 * 2 ^ nu2 n t := by linarith
  have hlt2 : collatzSeq n t < 2 := by
    by_contra h
    push_neg at h
    exact absurd hlt (not_lt.mpr (Nat.mul_le_mul_right (2 ^ nu2 n t) h))
  have hpos := collatzSeq_pos n hn t
  omega

/-- If the walk diverges and a correction bound holds, then the Collatz
    sequence reaches 1. This is correct but requires a correction bound
    hypothesis that cannot be satisfied uniformly. -/
theorem collatz_reaches_of_walk_diverges (n : ℕ) (hn : n ≥ 1)
    (C : ℕ) (hC : ∀ t, correction n t ≤ C * 3 ^ nu3 n t)
    (hdiv : Filter.Tendsto (fun t => walk n t) Filter.atTop Filter.atTop) :
    collatzReaches n := by
  -- Since walk → +∞, find T where walk n T > logb 2 (n + C)
  rw [Filter.tendsto_atTop_atTop] at hdiv
  obtain ⟨T, hT⟩ := hdiv (logb 2 (↑(n + C)) + 1)
  have hwalk : walk n T > logb 2 (↑(n + C)) := by linarith [hT T le_rfl]
  -- Setup positivity facts
  have hnC_pos : (0 : ℝ) < ↑(n + C) := by positivity
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (nu3 n T) := by positivity
  have hprod_pos : (0 : ℝ) < ↑(n + C) * (3 : ℝ) ^ (nu3 n T) := mul_pos hnC_pos h3pos
  have h2nu2_pos : (0 : ℝ) < (2 : ℝ) ^ (nu2 n T) := by positivity
  -- logb 2 of product = logb 2 (n+C) + ν₃ · logb 2 3
  have hlog_prod : logb 2 (↑(n + C) * (3 : ℝ) ^ (nu3 n T)) =
      logb 2 ↑(n + C) + ↑(nu3 n T) * logb 2 3 := by
    rw [logb_mul (ne_of_gt hnC_pos) (ne_of_gt h3pos), logb_pow]
  -- logb 2 (2^ν₂) = ν₂
  have hlog_2nu2 : logb 2 ((2 : ℝ) ^ (nu2 n T)) = ↑(nu2 n T) := by
    rw [logb_pow, logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  -- Show logb 2 (product) < logb 2 (2^ν₂)
  have hlog_lt : logb 2 (↑(n + C) * (3 : ℝ) ^ (nu3 n T)) <
      logb 2 ((2 : ℝ) ^ (nu2 n T)) := by
    rw [hlog_prod, hlog_2nu2]
    unfold walk at hwalk; linarith
  -- Convert logb inequality to log inequality
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hlog_lt' : Real.log (↑(n + C) * (3 : ℝ) ^ (nu3 n T)) <
      Real.log ((2 : ℝ) ^ (nu2 n T)) := by
    simp only [Real.logb] at hlog_lt
    have h1 := mul_lt_mul_of_pos_right hlog_lt hlog2_pos
    rwa [div_mul_cancel₀ _ hlog2_ne, div_mul_cancel₀ _ hlog2_ne] at h1
  -- Apply exp (strictly monotone) to convert log inequality to value inequality
  have hexp_lt := Real.exp_strictMono hlog_lt'
  rw [Real.exp_log hprod_pos, Real.exp_log h2nu2_pos] at hexp_lt
  -- Cast ℝ inequality to ℕ: (n+C) * 3^ν₃ < 2^ν₂
  have hlt_nat : (n + C) * 3 ^ nu3 n T < 2 ^ nu2 n T := by exact_mod_cast hexp_lt
  -- Strengthen: < 2^ν₂ implies < 2 · 2^ν₂
  have h2nu2_nat_pos : 0 < 2 ^ nu2 n T := by positivity
  have hlt_nat2 : (n + C) * 3 ^ nu3 n T < 2 * 2 ^ nu2 n T := by linarith
  exact ⟨T, seq_eq_one_of_pow_bound n T C hn hC hlt_nat2⟩

/-! ## The Collatz conjecture -/

/-- The Collatz conjecture: every positive natural number eventually reaches 1.
    Critical path: nu3_linear_bound (sorry) → reaches_one_of_linear_drift → here.
    The walk divergence and ε-drift machinery (Drift.lean) is off the critical path. -/
theorem collatz_conjecture : CollatzConjecture := by
  intro n hn
  -- Extract the K-bound from nu3_linear_bound (the sole sorry on the critical path)
  obtain ⟨K, T₀, hbound3⟩ := nu3_linear_bound n hn
  -- Apply the correction ratio proof chain
  exact reaches_one_of_linear_drift n hn K T₀ hbound3

/-! ## Equivalence: nu3_linear_bound ↔ collatzReaches -/

/-- The K-bound is equivalent to the Collatz conjecture for each n.
    Forward: K-bound → trajectory bounded → periodic → cycle = {1,2,4} → reaches 1.
    Reverse: reaches 1 → enters the 1→4→2→1 cycle → ν₃ grows as t/3 → K-bound. -/
theorem nu3_linear_bound_iff_reaches (n : ℕ) (hn : n ≥ 1) :
    (∃ K T₀, ∀ t, t ≥ T₀ → 3 * nu3 n t ≤ t + K) ↔ collatzReaches n := by
  constructor
  · intro ⟨K, T₀, hbound⟩
    exact reaches_one_of_linear_drift n hn K T₀ hbound
  · exact nu3_linear_bound_of_reaches n hn

/-! ## Evaluation -/

-- Demonstrate that correction / 3^nu3 grows unboundedly (no uniform constant C works).
-- For n=7: the sequence reaches 1 at t=16, then cycles 1→4→2→1.
-- Each cycle adds 1 odd step where correction recurrence is 3*correction + 2^nu2,
-- so correction/3^nu3 grows as (4/3)^m per cycle.
#eval (List.range 30).map fun t =>
  let c := correction 7 t
  let pow3 := 3 ^ nu3 7 t
  (t, c, if pow3 > 0 then c / pow3 else 0)

end Collatz
