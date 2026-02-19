/-
  CollatzLean/SyracuseDrift.lean
  Bridge between the Syracuse framework (Syracuse.lean) and the Walk/Drift
  framework (Walk.lean, Drift.lean).

  Key results:
  - syracuseTime: maps Syracuse step k to the corresponding Collatz step
  - collatzSeq_at_syracuseTime: collatzSeq n (syracuseTime n k) = syracuseIter n k
  - nu3_at_syracuseTime: nu3 n (syracuseTime n k) = k
  - nu2_at_syracuseTime: nu2 n (syracuseTime n k) = syracuseValSum n k
  - walk_from_syracuse: walk at Syracuse boundaries in terms of valuation sums
  - syracuse_descent_implies_reaches: Syracuse descent → collatzReaches
-/
import CollatzLean.Syracuse
import CollatzLean.Drift
import CollatzLean.CorrectionRatio
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option linter.style.nativeDecide false

namespace Collatz

open Real

/-! ## collatzSeq as iterate (re-proved; private in CorrectionRatio) -/

/-- collatzSeq n t equals (collatz^[t]) n. -/
theorem collatzSeq_eq_iterate (n t : ℕ) : collatzSeq n t = (collatz^[t]) n := by
  induction t with
  | zero => rfl
  | succ t ih => rw [collatzSeq_succ, ih, Function.iterate_succ_apply']

/-- Shifting collatzSeq: collatzSeq n (t + k) = collatzSeq (collatzSeq n t) k. -/
theorem collatzSeq_shift (n t k : ℕ) :
    collatzSeq n (t + k) = collatzSeq (collatzSeq n t) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show t + (k + 1) = (t + k) + 1 from by omega, collatzSeq_succ, ih, collatzSeq_succ]

/-! ## Syracuse time -/

/-- The Collatz time corresponding to Syracuse step k.
    After k Syracuse steps starting from odd n, we have done k odd steps
    plus syracuseValSum n k even steps (halvings). -/
def syracuseTime (n : ℕ) (k : ℕ) : ℕ := k + syracuseValSum n k

@[simp] lemma syracuseTime_zero (n : ℕ) : syracuseTime n 0 = 0 := by
  simp [syracuseTime]

lemma syracuseTime_succ (n k : ℕ) :
    syracuseTime n (k + 1) = syracuseTime n k + 1 + syracuseValAt n k := by
  simp [syracuseTime, syracuseValSum_succ, syracuseValAt]; omega

/-! ## Halving steps are even -/

/-- During the halving phase after an odd step, all steps are even.
    If collatzSeq n t is odd, then for s < val2(3·collatzSeq n t + 1),
    the step at t + 1 + s is even. -/
theorem halving_steps_even (n t : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (s : ℕ) (hs : s < val2 (3 * collatzSeq n t + 1)) :
    isEvenStep n (t + 1 + s) = true := by
  set x := collatzSeq n t with hx_def
  set m := 3 * x + 1 with hm_def
  set a := val2 m with ha_def
  have hx_pos : x ≠ 0 := collatzSeq_ne_zero n hn t
  -- collatzSeq n (t+1) = 3x+1 = m
  have hstep : collatzSeq n (t + 1) = m := by
    rw [collatzSeq_succ, collatz_odd x hx_pos hodd]
  -- collatzSeq n (t+1+s) = m / 2^s
  have hiter : collatzSeq n (t + 1 + s) = m / 2 ^ s := by
    rw [collatzSeq_shift n (t + 1) s, hstep, collatzSeq_eq_iterate m s]
    exact collatz_iter_halving m (by omega) s
      (dvd_trans (pow_dvd_pow 2 (le_of_lt hs)) (pow_val2_dvd m))
  -- m / 2^s is even because 2^(s+1) | m
  simp only [isEvenStep, hiter, decide_eq_true_eq]
  have hdvd : 2 ^ (s + 1) ∣ m :=
    dvd_trans (pow_dvd_pow 2 (by omega)) (pow_val2_dvd m)
  obtain ⟨j, hj⟩ := hdvd
  have : m / 2 ^ s = 2 * j := by
    have h1 : m = 2 ^ s * (2 * j) := by rw [hj, pow_succ]; ring
    rw [h1, Nat.mul_div_cancel_left _ (by positivity)]
  rw [this]; omega

/-! ## Core tracking: collatzSeq at Syracuse times -/

/-- At Syracuse time boundaries, the Collatz sequence equals the Syracuse iteration. -/
theorem collatzSeq_at_syracuseTime (n k : ℕ) (hn : n ≥ 1) (hodd : n % 2 = 1) :
    collatzSeq n (syracuseTime n k) = syracuseIter n k := by
  induction k with
  | zero => simp [syracuseTime, collatzSeq_zero]
  | succ k ih =>
    rw [syracuseTime_succ]
    -- At time syracuseTime n k, collatzSeq = syracuseIter n k (by IH)
    -- syracuseIter n k is odd
    have hodd_k : syracuseIter n k % 2 = 1 := syracuseIter_odd n hn hodd k
    -- Apply collatzSeq_to_syracuse at time = syracuseTime n k
    have hbridge := collatzSeq_to_syracuse n (syracuseTime n k) hn
      (by rw [ih]; exact hodd_k)
    -- hbridge: collatzSeq n (sT + 1 + val2(3 * collatzSeq n sT + 1)) = syracuse(collatzSeq n sT)
    rw [ih] at hbridge
    -- syracuseValAt n k = val2(3 * syracuseIter n k + 1)
    simp only [syracuseValAt] at hbridge ⊢
    exact hbridge

/-! ## ν₃ tracking: nu3 at Syracuse times -/

/-- Helper: nu3 is unchanged over a run of halving (even) steps. -/
private theorem nu3_unchanged_of_halving_run (n t : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1) (s : ℕ) (hs : s ≤ val2 (3 * collatzSeq n t + 1)) :
    nu3 n (t + 1 + s) = nu3 n (t + 1) := by
  induction s with
  | zero => rfl
  | succ s ih_s =>
    have hs' : s < val2 (3 * collatzSeq n t + 1) := by omega
    have hs_le : s ≤ val2 (3 * collatzSeq n t + 1) := by omega
    rw [show t + 1 + (s + 1) = (t + 1 + s) + 1 from by omega]
    rw [nu3_step_even n (t + 1 + s) (halving_steps_even n t hn hodd s hs')]
    exact ih_s hs_le

/-- At Syracuse time k, nu3 equals k. -/
theorem nu3_at_syracuseTime (n k : ℕ) (hn : n ≥ 1) (hodd : n % 2 = 1) :
    nu3 n (syracuseTime n k) = k := by
  induction k with
  | zero => simp [syracuseTime]
  | succ k ih =>
    rw [syracuseTime_succ]
    -- Between syracuseTime n k and syracuseTime n (k+1):
    -- 1 odd step at time T = syracuseTime n k, then syracuseValAt n k even steps
    set T := syracuseTime n k with hT_def
    -- collatzSeq n T is odd (= syracuseIter n k, which is odd)
    have hseq := collatzSeq_at_syracuseTime n k hn hodd
    have hodd_T : collatzSeq n T % 2 = 1 := by
      rw [hseq]; exact syracuseIter_odd n hn hodd k
    -- The step at T is odd
    have hT_odd : isOddStep n T = true := by
      simp only [isOddStep, decide_eq_true_eq]; exact hodd_T
    -- nu3 at T+1 = nu3 at T + 1 = k + 1
    have h1 : nu3 n (T + 1) = nu3 n T + 1 := nu3_step_odd n T hT_odd
    -- nu3 unchanged over the halving run
    have h2 : nu3 n (T + 1 + syracuseValAt n k) = nu3 n (T + 1) := by
      apply nu3_unchanged_of_halving_run n T hn hodd_T
      simp only [syracuseValAt]; rw [hseq]
    rw [h2, h1, ih]

/-- At Syracuse time k, nu2 equals syracuseValSum n k. -/
theorem nu2_at_syracuseTime (n k : ℕ) (hn : n ≥ 1) (hodd : n % 2 = 1) :
    nu2 n (syracuseTime n k) = syracuseValSum n k := by
  have hpart := nu_partition n (syracuseTime n k)
  have hnu3 := nu3_at_syracuseTime n k hn hodd
  -- hpart: nu2 + nu3 = syracuseTime = k + syracuseValSum
  -- hnu3: nu3 = k
  -- So nu2 = syracuseValSum
  rw [hnu3] at hpart
  have : syracuseTime n k = k + syracuseValSum n k := rfl
  omega

/-! ## Deliverables -/

/-- D1: Syracuse valuation sum equals nu2 at odd-time boundaries. -/
theorem syracuseValSum_eq_nu2_at_odd_times (n k : ℕ) (hn : n ≥ 1) (hodd : n % 2 = 1) :
    syracuseValSum n k = nu2 n (syracuseTime n k) :=
  (nu2_at_syracuseTime n k hn hodd).symm

/-- D2: The walk at Syracuse time boundaries in terms of Syracuse valuations. -/
theorem walk_from_syracuse (n k : ℕ) (hn : n ≥ 1) (hodd : n % 2 = 1) :
    walk n (syracuseTime n k) = ↑(syracuseValSum n k) - logb 2 3 * ↑k := by
  unfold walk
  rw [nu2_at_syracuseTime n k hn hodd, nu3_at_syracuseTime n k hn hodd]

/-- D3: If the Syracuse iteration reaches 1, then collatzReaches holds. -/
theorem syracuse_descent_implies_reaches (n : ℕ) (hn : n ≥ 1) (hodd : n % 2 = 1)
    (k : ℕ) (hk : syracuseIter n k = 1) :
    collatzReaches n :=
  ⟨syracuseTime n k, by rw [collatzSeq_at_syracuseTime n k hn hodd, hk]⟩

/-- D4 (backward): K-bound implies Syracuse valuation sum lower bound.
    If 3·ν₃(n,t) ≤ t + K for large t, then valSum ≥ 2k - K,
    meaning each Syracuse step averages ≥ 2 halvings (matching log₂3 ≈ 1.585). -/
theorem syracuse_valsum_lower_of_kbound (n : ℕ) (hn : n ≥ 1) (hodd : n % 2 = 1)
    (K T₀ : ℕ) (hbound : ∀ t, t ≥ T₀ → 3 * nu3 n t ≤ t + K)
    (k : ℕ) (hk : syracuseTime n k ≥ T₀) :
    2 * k ≤ syracuseValSum n k + K := by
  have h := hbound (syracuseTime n k) hk
  rw [nu3_at_syracuseTime n k hn hodd] at h
  -- h: 3k ≤ (k + syracuseValSum n k) + K
  have : syracuseTime n k = k + syracuseValSum n k := rfl
  omega

-- Concrete verification
example : syracuseTime 7 0 = 0 := by native_decide
example : syracuseTime 7 1 = 2 := by native_decide  -- 1 odd step + 1 halving
example : syracuseTime 7 3 = 7 := by native_decide  -- 3 odd steps + 4 halvings

example : collatzSeq 7 (syracuseTime 7 3) = syracuseIter 7 3 := by native_decide
example : nu3 7 (syracuseTime 7 3) = 3 := by native_decide
example : nu2 7 (syracuseTime 7 3) = syracuseValSum 7 3 := by native_decide

end Collatz
