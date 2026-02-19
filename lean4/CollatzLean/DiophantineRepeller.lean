/-
  CollatzLean/DiophantineRepeller.lean
  Diophantine repeller decomposition of nu3_linear_bound.

  Refines the sole critical-path sorry (nu3_linear_bound in Drift.lean)
  into a characterization via bounded deficit: finite_deficit_bound.

  Decomposition:
  1. hensel_attrition (HenselAttrition.lean) — v₂=1 runs require 2^{d+1} | (x+1)
  2. baker_cell_separation (this file) — dangerous cells Diophantine-separated
  3. finite_deficit_bound (this file, sorry) — deficit bounded above
  4. k_bound_of_deficit_bounded' (this file) — deficit bounded → K-bound

  The sole sorry is finite_deficit_bound (∃ D, ∀ t, deficit(t) ≤ D).
  It is equivalent to the Collatz conjecture for each n.

  NOTE: The original `finite_residence_bound` used `SlidingWindowCondition`
  (deficit non-increasing over windows), which is FALSE for n=27 and ~42.6%
  of all starting values. The SWC infrastructure is retained as correct
  implications but is no longer on the critical path. See BUG NOTE below.
-/
import CollatzLean.HenselAttrition
import CollatzLean.Baker

set_option linter.style.nativeDecide false

namespace Collatz

open Real

/-! ## Deficit step bound -/

/-- At any step, deficit increases by at most 2. -/
theorem deficit_step_le (n t : ℕ) : deficit n (t + 1) ≤ deficit n t + 2 := by
  by_cases ho : isOddStep n t = true
  · rw [deficit_step_odd n t ho]
  · have he : isEvenStep n t = true := by
      simp only [isEvenStep, isOddStep, decide_eq_true_eq] at *; omega
    rw [deficit_step_even n t he]; omega

/-- Over r steps, deficit increases by at most 2r. -/
theorem deficit_add_le (n t r : ℕ) : deficit n (t + r) ≤ deficit n t + 2 * ↑r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : t + (r + 1) = (t + r) + 1 := by omega
    calc deficit n (t + (r + 1))
        = deficit n ((t + r) + 1) := by rw [h1]
      _ ≤ deficit n (t + r) + 2 := deficit_step_le n (t + r)
      _ ≤ (deficit n t + 2 * ↑r) + 2 := by linarith
      _ = deficit n t + 2 * (↑r + 1) := by ring
      _ = deficit n t + 2 * ↑(r + 1) := by push_cast; ring

/-! ## Sliding window condition -/

/-- The sliding window condition: deficit does not increase over any window
    of W consecutive steps. This captures the Diophantine repeller property:
    dangerous v₂=1 runs are compensated by safe steps with v₂ ≥ 3 within
    every window, so the net deficit change is non-positive.

    Mathematical meaning: over W uncompressed Collatz steps, the number of
    odd steps (×3+1) never exceeds t/3 + O(1), ensuring the trajectory
    cannot sustain unbounded growth. -/
def SlidingWindowCondition (n W : ℕ) : Prop :=
  ∀ t : ℕ, deficit n (t + W) ≤ deficit n t

/-! ## k_bound_from_repeller: window condition → deficit bounded → K-bound -/

/-- Over k full windows, deficit stays ≤ 0 (telescoping from deficit(0) = 0). -/
theorem deficit_nonpos_at_multiples (n W : ℕ) (k : ℕ)
    (hW : SlidingWindowCondition n W) :
    deficit n (k * W) ≤ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : (k + 1) * W = k * W + W := by ring
    calc deficit n ((k + 1) * W)
        = deficit n (k * W + W) := by rw [h]
      _ ≤ deficit n (k * W) := hW (k * W)
      _ ≤ 0 := ih

/-- If the sliding window condition holds with W ≥ 1, deficit is bounded by 2W.

    Proof: For any t, write t = kW + r with 0 ≤ r < W.
    - deficit(kW) ≤ 0 by telescoping (deficit_nonpos_at_multiples)
    - deficit(t) ≤ deficit(kW) + 2r by deficit_add_le
    - So deficit(t) ≤ 2r < 2W. -/
theorem deficit_bounded_of_window (n W : ℕ) (hWpos : W ≥ 1)
    (hW : SlidingWindowCondition n W) :
    ∀ t : ℕ, deficit n t ≤ 2 * ↑W := by
  intro t
  have hr_lt : t % W < W := Nat.mod_lt t (by omega)
  have ht_eq : t = t / W * W + t % W := by
    have h := Nat.div_add_mod t W; rw [Nat.mul_comm] at h; exact h.symm
  calc deficit n t
      = deficit n (t / W * W + t % W) := by congr 1
    _ ≤ deficit n (t / W * W) + 2 * ↑(t % W) :=
        deficit_add_le n (t / W * W) (t % W)
    _ ≤ 0 + 2 * ↑(t % W) := by
        linarith [deficit_nonpos_at_multiples n W (t / W) hW]
    _ = 2 * ↑(t % W) := by ring
    _ ≤ 2 * ↑W := by exact_mod_cast show 2 * (t % W) ≤ 2 * W from by omega

/-- Deficit bounded above implies the K-bound (reproduced from Drift.lean
    to avoid circular imports). -/
theorem k_bound_of_deficit_bounded' (n : ℕ) (_hn : n ≥ 1)
    (hdef : ∃ D : ℤ, ∀ t, deficit n t ≤ D) :
    ∃ K : ℕ, ∃ T₀ : ℕ, ∀ t, t ≥ T₀ → 3 * nu3 n t ≤ t + K := by
  obtain ⟨D, hD⟩ := hdef
  have hD0 : 0 ≤ D := by have h0 := hD 0; simp only [deficit_zero] at h0; exact h0
  refine ⟨D.toNat, 0, fun t _ => ?_⟩
  have h := hD t
  simp only [deficit] at h
  have : (3 * nu3 n t : ℤ) ≤ ↑t + ↑D.toNat := by omega
  exact_mod_cast this

/-- **k_bound_from_repeller**: The sliding window condition implies the K-bound.

    Proof chain:
      SlidingWindowCondition n W
        → ∀ t, deficit n t ≤ 2W     (deficit_bounded_of_window)
        → ∃ K T₀, ∀ t ≥ T₀, 3·ν₃ ≤ t + K  (k_bound_of_deficit_bounded')

    This is the formal link from the Diophantine repeller to the K-bound.
    Combined with reaches_one_of_linear_drift (CorrectionRatio.lean),
    it gives the Collatz conjecture for n. -/
theorem k_bound_from_repeller (n : ℕ) (hn : n ≥ 1) (W : ℕ) (hWpos : W ≥ 1)
    (hW : SlidingWindowCondition n W) :
    ∃ K : ℕ, ∃ T₀ : ℕ, ∀ t, t ≥ T₀ → 3 * nu3 n t ≤ t + K :=
  k_bound_of_deficit_bounded' n hn ⟨2 * ↑W, deficit_bounded_of_window n W hWpos hW⟩

/-! ## Baker cell separation -/

/-- The "cell error" measures how far a cell index pair (a, b) deviates
    from the critical ratio log₂3 on the (Z/3^k)² torus.

    Cells with small |cellError| are "dangerous" — trajectories visiting
    them have v₂ close to 1 (each ×3+1 followed by only one ÷2).
    Cells with large |cellError| are "safe" — trajectories visiting
    them have v₂ ≥ 2, contributing non-positively to the deficit. -/
noncomputable def cellError (a b : ℤ) : ℝ :=
  ↑a - logb 2 3 * ↑b

/-- Connection between cellError and linearFormLog:
    cellError(a, b) · log 2 = linearFormLog(a, -b). -/
theorem cellError_linearForm (a b : ℤ) :
    cellError a b * Real.log 2 = linearFormLog a (-b) := by
  unfold cellError linearFormLog logb
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  push_cast
  ring

/-- **Baker cell separation**: For any nonzero cell index pair (a, b),
    the cell error is bounded below by an effective constant divided by
    a polynomial in max(|a|, |b|).

    This means dangerous cells (small cellError) cannot cluster on the
    torus — they are Diophantine-separated with explicit gap.

    Consequence: at any torus scale 3^k, the dangerous cells form a
    sparse set, and any trajectory must pass through safe cells
    (with v₂ ≥ 2 or v₂ ≥ 3) between dangerous encounters.

    Proof: translates baker_two_three (Baker.lean) from the logarithmic
    form |m·log 2 + n·log 3| > C/max^κ to the cell error form. -/
theorem baker_cell_separation :
    ∃ (C : ℝ) (κ : ℝ), C > 0 ∧ κ > 0 ∧
      ∀ a b : ℤ, a ≠ 0 ∨ b ≠ 0 →
        |cellError a b| > C / (max (|a| : ℝ) (|b| : ℝ)) ^ κ := by
  obtain ⟨C, κ, hC, hκ, hbaker⟩ := baker_two_three
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C / Real.log 2, κ, by positivity, hκ, ?_⟩
  intro a b hab
  -- |cellError a b| = |linearFormLog a (-b)| / log 2
  have hce : |cellError a b| = |linearFormLog a (-b)| / Real.log 2 := by
    rw [← cellError_linearForm, abs_mul, abs_of_pos hlog2_pos]
    field_simp
  -- (a, -b) ≠ (0, 0)
  have hab' : a ≠ 0 ∨ -b ≠ 0 := by
    rcases hab with ha | hb
    · exact Or.inl ha
    · exact Or.inr (neg_ne_zero.mpr hb)
  -- max |a| |-b| = max |a| |b|
  have hmax_eq : (max (|(a : ℤ)| : ℝ) (|(-b : ℤ)| : ℝ)) =
      max (|(a : ℤ)| : ℝ) (|(b : ℤ)| : ℝ) := by
    simp [abs_neg]
  -- Apply Baker's bound and simplify
  have hbak := hbaker a (-b) hab'
  rw [hmax_eq] at hbak
  -- hbak : |linearFormLog a (-b)| > C / (max |↑a| |↑b|) ^ κ
  -- Goal: |cellError a b| > C / log 2 / (max |↑a| |↑b|) ^ κ
  -- Strategy: |cellError| * log 2 = |linearFormLog| (from cellError_linearForm)
  -- so |cellError| = |linearFormLog| / log 2 > (C / max^κ) / log 2 = C / log 2 / max^κ
  have hce_mul : |cellError a b| * Real.log 2 = |linearFormLog a (-b)| := by
    rw [← cellError_linearForm, abs_mul, abs_of_pos hlog2_pos]
  rw [gt_iff_lt] at hbak ⊢
  -- hbak : C / max^κ < |linearFormLog a (-b)|
  -- Goal: C / log 2 / max^κ < |cellError a b|
  rw [hce]
  -- Goal: C / log 2 / max^κ < |linearFormLog a (-b)| / log 2
  -- Rewrite LHS to (C / max^κ) / log 2
  rw [div_div, mul_comm (Real.log 2), ← div_div]
  -- Goal: C / max^κ / log 2 < |linearFormLog a (-b)| / log 2
  -- Both sides are _ / log 2; use monotonicity of _ * (log 2)⁻¹
  conv_lhs => rw [div_eq_mul_inv]
  conv_rhs => rw [div_eq_mul_inv]
  exact mul_lt_mul_of_pos_right hbak (inv_pos.mpr hlog2_pos)

/-! ## The finite deficit bound (irreducible gap)

    BUG NOTE (2026-02-19): The original `finite_residence_bound` asserted
    `∃ W ≥ 1, SlidingWindowCondition n W`, i.e., the deficit is non-increasing
    over windows of size W. This is FALSE for many starting values:

    Counterexample: n = 27 reaches 1 at step 111 with deficit(111) = 12 > 0.
    In the 1→4→2→1 cycle, deficit stabilizes at {12, 13, 14}.
    Since deficit(0) = 0 and deficit(t) ≈ 12 for large t,
    deficit(0+W) > 0 = deficit(0) for all W ≥ 1. Hence SWC 27 W is false ∀ W.

    Similarly false for n=31 (deficit 11), n=63 (10), n=97 (11), and
    ~42.6% of numbers up to 10M (any trajectory with final deficit > 0).

    The correct formulation is the **finite deficit bound**: the deficit is
    bounded above (but NOT necessarily non-increasing). This IS equivalent to
    the K-bound and to the Collatz conjecture for each n.

    HasCompensatedRuns and SlidingWindowCondition remain as valid definitions
    in the codebase (they ARE satisfied for some n, e.g. n=3 with deficit(T)=-1),
    but they cannot serve as universal targets for all n ≥ 1. -/

/-- **Finite deficit bound**: for every n ≥ 1, the deficit is bounded above.

    This is the corrected version of the former `finite_residence_bound`.
    It states: ∃ D, ∀ t, deficit(n, t) ≤ D, meaning the deficit
    (= 3·ν₃(t) - t) never exceeds some finite constant D.

    Equivalence:
    - ↔ nu3_linear_bound (Drift.lean) via k_bound_of_deficit_bounded'
    - ↔ collatzReaches n (Conclusion.lean) via nu3_linear_bound_iff_reaches

    Evidence: For n=27, D=14 works. Computationally verified for all n ≤ 10^10
    (deficit_analysis.c). The maximum deficit grows slowly (roughly as log n).

    What would close this sorry:
    Show that the three forces (Hensel attrition, Baker cell separation,
    Weyl equidistribution) together prevent unbounded deficit accumulation.
    The skew product structure (SkewProduct.lean) and correlation decay
    (CorrelationDecay.lean) provide infrastructure, but the gap between
    "ergodicity of the skew product" and "bounded deficit for every trajectory"
    remains open. -/
theorem finite_deficit_bound (n : ℕ) (hn : n ≥ 1) :
    ∃ D : ℤ, ∀ t : ℕ, deficit n t ≤ D := by
  sorry

/-! ## Wiring: finite_deficit_bound → K-bound -/

/-- The decomposition: finite_deficit_bound → K-bound.

    Proof chain:
      finite_deficit_bound n hn          -- ∃ D, ∀ t, deficit(t) ≤ D
        → k_bound_of_deficit_bounded'    -- deficit bounded → K-bound
        = ∃ K T₀, ∀ t ≥ T₀, 3·ν₃ ≤ t + K -/
theorem nu3_linear_bound_from_repeller (n : ℕ) (hn : n ≥ 1) :
    ∃ K : ℕ, ∃ T₀ : ℕ, ∀ t, t ≥ T₀ → 3 * nu3 n t ≤ t + K :=
  k_bound_of_deficit_bounded' n hn (finite_deficit_bound n hn)

/-! ## Relationship with deficit-bounded formulation -/

/-- The sliding window condition implies deficit bounded.
    (The converse does NOT hold in general: deficit bounded allows
    oscillation, while the window condition requires monotone decay
    at window boundaries.) -/
theorem sliding_window_implies_deficit_bounded (n : ℕ) (W : ℕ) (hWpos : W ≥ 1)
    (hW : SlidingWindowCondition n W) :
    ∃ D : ℤ, ∀ t, deficit n t ≤ D :=
  ⟨2 * ↑W, deficit_bounded_of_window n W hWpos hW⟩

/-! ## Summary of the sorry decomposition -/

/-
  Original sorry chain (Drift.lean):
    nu3_linear_bound [sorry]
      → reaches_one_of_linear_drift (CorrectionRatio.lean)
      → collatz_conjecture (Conclusion.lean)

  Alternative sorry chain (this file):
    baker_two_three [sorry, Baker.lean]
      → baker_cell_separation [proved above]
    hensel_attrition [sorry-free, HenselAttrition.lean]
    finite_deficit_bound [sorry, THIS FILE — equivalent to Collatz]
      → k_bound_of_deficit_bounded' [proved above]
      → nu3_linear_bound_from_repeller [proved above]
      → (same signature as nu3_linear_bound)

  The finite_deficit_bound states: ∃ D, ∀ t, deficit(n, t) ≤ D.
  This is equivalent to:
    - nu3_linear_bound: ∃ K T₀, ∀ t ≥ T₀, 3·ν₃ ≤ t + K
    - collatzReaches n
  The deficit is bounded iff the trajectory eventually reaches 1.

  BUG NOTE (2026-02-19): The original `finite_residence_bound` used
  SlidingWindowCondition (∀ t, deficit(t+W) ≤ deficit(t)), which is FALSE
  for n=27 (deficit climbs from 0 to 12) and ~42.6% of all n ≤ 10^7.
  The SWC infrastructure (k_bound_from_repeller, deficit_bounded_of_window,
  etc.) remains correct as implications from SWC, but SWC itself is not
  universally satisfiable and is no longer on the critical path.
-/

end Collatz
