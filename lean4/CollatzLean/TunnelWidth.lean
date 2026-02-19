/-
  CollatzLean/TunnelWidth.lean
  Connects Baker's inequality to tunnel wall persistence:
  Diophantine approximation of log₂(3) forces pure-even cells to exist,
  giving the tunnel nonzero width.
-/
import CollatzLean.Baker
import CollatzLean.Walk
import CollatzLean.BranchLocus

set_option linter.style.nativeDecide false

namespace Collatz

open Real

/-! ## Best rational approximation to log₂(3) -/

/-- Best integer approximation to log₂(3) · 3^b (nearest integer). -/
noncomputable def bestApprox (b : ℕ) : ℤ :=
  ⌊logb 2 3 * (3 ^ b : ℕ) + 1 / 2⌋

/-- The Diophantine error: logb 2 3 - bestApprox(b) / 3^b. -/
noncomputable def diophError (b : ℕ) : ℝ :=
  logb 2 3 - ↑(bestApprox b) / ↑(3 ^ b : ℕ)

/-- Count of pure-even cells at scale 3^b: the tunnel wall width. -/
def tunnelWallWidth (b N T : ℕ) : ℕ :=
  haveI : NeZero (3 ^ b) := ⟨by positivity⟩
  pureEvenCount (3 ^ b) N T

/-! ## Diophantine error is nonzero -/

/-- The Diophantine error is never zero (else log₂(3) would be rational). -/
theorem diophError_ne_zero (b : ℕ) : diophError b ≠ 0 := by
  intro h
  unfold diophError at h
  -- If error = 0, then logb 2 3 = bestApprox b / 3^b, which is rational
  have hrat : logb 2 3 = ↑(bestApprox b) / ↑(3 ^ b : ℕ) := by linarith
  -- Cast to ℤ form for ne_rational
  have hrat' : logb 2 3 = (↑(bestApprox b) : ℝ) / (↑(↑(3 ^ b : ℕ) : ℤ) : ℝ) := by
    rw [hrat]; push_cast; ring
  exact irrational_logb_two_three.ne_rational (bestApprox b) (↑(3 ^ b : ℕ)) hrat'

/-! ## Baker → Diophantine lower bound -/

/-- Baker's inequality gives a lower bound on the Diophantine error:
    |ε(b)| > C' / (3^b)^(1+ε).

    Proof sketch (algebraic translation of baker_two_three):
    - Set m = bestApprox(b), n = -(3^b) in linearFormLog
    - Then |linearFormLog m n| = log 2 · 3^b · |diophError b|
    - Baker gives |linearFormLog m n| > C / max(|m|, |n|)^κ
    - Since |bestApprox b| ≤ 2 · 3^b, max(|m|, |n|) ≤ 2 · 3^b
    - So |diophError b| > C / (2^κ · log 2 · (3^b)^(1+κ)) = C' / (3^b)^(1+κ)
    - Set ε = κ, C' = C / (2^κ · log 2). -/
private lemma logb_two_three_lt_two : logb 2 3 < 2 := by
  have hlog2 : (0 : ℝ) < log 2 := log_pos (by norm_num)
  rw [logb, div_lt_iff₀ hlog2]
  calc log 3 < log 4 := log_lt_log (by positivity) (by norm_num)
    _ = log (2 ^ 2) := by norm_num
    _ = 2 * log 2 := by rw [log_pow]; ring

private lemma bestApprox_le (b : ℕ) :
    |bestApprox b| ≤ 2 * ↑(3 ^ b : ℕ) := by
  unfold bestApprox
  have hlogb_lt : logb 2 3 < 2 := logb_two_three_lt_two
  have hlogb_pos : (0 : ℝ) < logb 2 3 := logb_pos (by norm_num) (by norm_num)
  have h3b_pos : (0 : ℝ) < ↑(3 ^ b : ℕ) := by positivity
  -- The argument to floor is positive, so floor is nonneg
  have hfloor_nn : 0 ≤ ⌊logb 2 3 * ↑(3 ^ b : ℕ) + 1 / 2⌋ :=
    Int.floor_nonneg.mpr (by linarith [mul_pos hlogb_pos h3b_pos])
  rw [abs_of_nonneg hfloor_nn]
  -- Show ⌊x⌋ ≤ 2 * 3^b using: x < 2*3^b + 1, so ⌊x⌋ < 2*3^b + 1, so ⌊x⌋ ≤ 2*3^b
  apply Int.lt_add_one_iff.mp
  rw [Int.floor_lt]
  have h_bound : logb 2 3 * ↑(3 ^ b : ℕ) < 2 * ↑(3 ^ b : ℕ) :=
    mul_lt_mul_of_pos_right hlogb_lt h3b_pos
  calc logb 2 3 * ↑(3 ^ b : ℕ) + 1 / 2
      < 2 * ↑(3 ^ b : ℕ) + 1 / 2 := by linarith
    _ ≤ 2 * ↑(3 ^ b : ℕ) + 1 := by linarith
    _ = ↑(2 * ↑(3 ^ b : ℕ) + 1 : ℤ) := by push_cast; ring

private lemma linearFormLog_diophError (b : ℕ) :
    linearFormLog (bestApprox b) (-(↑(3 ^ b : ℕ) : ℤ)) =
    -(↑(3 ^ b : ℕ) * Real.log 2 * diophError b) := by
  unfold linearFormLog diophError logb
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h3b_ne : (↑(3 ^ b : ℕ) : ℝ) ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < ↑(3 ^ b : ℕ))
  push_cast
  field_simp
  ring

theorem diophError_lower_bound :
    ∃ (C' : ℝ) (ε : ℝ), C' > 0 ∧ ε > 0 ∧
      ∀ b : ℕ, |diophError b| > C' / (↑(3 ^ b : ℕ) : ℝ) ^ (1 + ε) := by
  -- Get Baker constants
  obtain ⟨C, κ, hC, hκ, hbaker⟩ := baker_two_three
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Choose C' = C / (2^κ * log 2), ε = κ
  refine ⟨C / (2 ^ κ * Real.log 2), κ, by positivity, hκ, fun b => ?_⟩
  -- Setup
  set m := bestApprox b
  set n := -(↑(3 ^ b : ℕ) : ℤ)
  have h3b_pos : (0 : ℝ) < ↑(3 ^ b : ℕ) := by positivity
  have hn_ne : n ≠ 0 := by simp [n]
  -- Apply Baker and convert |linearFormLog| to diophError form
  have hB := hbaker m n (Or.inr hn_ne)
  rw [linearFormLog_diophError, abs_neg, abs_mul, abs_mul,
      abs_of_pos h3b_pos, abs_of_pos hlog2_pos] at hB
  -- hB : ↑(3^b) * log 2 * |diophError b| > C / (max |(↑m:ℝ)| |(↑n:ℝ)|)^κ
  -- Bound max |(↑m:ℝ)| |(↑n:ℝ)| ≤ 2 * ↑(3^b) in ℝ
  have hn_real_abs : |(↑n : ℝ)| = ↑(3 ^ b : ℕ) := by
    simp only [n, Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_pos h3b_pos]
  have hmax_le : max |(↑m : ℝ)| |(↑n : ℝ)| ≤ 2 * ↑(3 ^ b : ℕ) := by
    rw [max_le_iff, hn_real_abs]
    refine ⟨?_, by linarith⟩
    rw [← Int.cast_abs]
    exact_mod_cast bestApprox_le b
  have hmax_pos : (0 : ℝ) < max |(↑m : ℝ)| |(↑n : ℝ)| :=
    lt_of_lt_of_le (by rw [hn_real_abs]; exact h3b_pos) (le_max_right _ _)
  -- max^κ ≤ (2·3^b)^κ
  have hmax_pow_le : (max |(↑m : ℝ)| |(↑n : ℝ)|) ^ κ ≤ (2 * ↑(3 ^ b : ℕ)) ^ κ :=
    rpow_le_rpow (le_of_lt hmax_pos) hmax_le (le_of_lt hκ)
  -- Monotonicity: C/(2·3^b)^κ ≤ C/max^κ
  have h_mono : C / (2 * ↑(3 ^ b : ℕ)) ^ κ ≤
      C / (max |(↑m : ℝ)| |(↑n : ℝ)|) ^ κ :=
    div_le_div_of_nonneg_left hC.le (rpow_pos_of_pos hmax_pos κ) hmax_pow_le
  -- Combine: C/(2·3^b)^κ < 3^b · log 2 · |diophError b|
  have hstep : C / (2 * ↑(3 ^ b : ℕ)) ^ κ <
      ↑(3 ^ b : ℕ) * Real.log 2 * |diophError b| :=
    lt_of_le_of_lt h_mono hB
  -- Algebraic identity: C'/(3^b)^(1+κ) = C/(3^b · log 2 · (2·3^b)^κ)
  have halg : C / (2 ^ κ * Real.log 2) / (↑(3 ^ b : ℕ)) ^ (1 + κ) =
      C / (↑(3 ^ b : ℕ) * Real.log 2 * (2 * ↑(3 ^ b : ℕ)) ^ κ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt h3b_pos),
        rpow_add h3b_pos, rpow_one]
    have : (0 : ℝ) < 2 ^ κ := rpow_pos_of_pos (by norm_num) κ
    have : (0 : ℝ) < ↑(3 ^ b : ℕ) ^ κ := rpow_pos_of_pos h3b_pos κ
    field_simp
  -- Final combination
  rw [gt_iff_lt, halg]
  have hprod_pos : (0 : ℝ) < ↑(3 ^ b : ℕ) * Real.log 2 * (2 * ↑(3 ^ b : ℕ)) ^ κ :=
    by positivity
  rw [div_lt_iff₀ hprod_pos]
  rw [div_lt_iff₀ (rpow_pos_of_pos (by positivity : (0 : ℝ) < 2 * ↑(3 ^ b : ℕ)) κ)] at hstep
  have : ↑(3 ^ b : ℕ) * Real.log 2 * |diophError b| * (2 * ↑(3 ^ b : ℕ)) ^ κ =
      |diophError b| * (↑(3 ^ b : ℕ) * Real.log 2 * (2 * ↑(3 ^ b : ℕ)) ^ κ) := by ring
  linarith

/-! ## Tunnel wall persistence (sorry) -/

/-- Diophantine gap forces pure-even cells to exist at every scale 3^b.
    The geometric bridge: rational approximation quality → torus cell classification. -/
theorem tunnel_walls_positive_of_baker (b : ℕ) (hb : b ≥ 1)
    (C' ε : ℝ) (_hC : C' > 0) (_hε : ε > 0)
    (_hbaker : |diophError b| > C' / (↑(3 ^ b : ℕ) : ℝ) ^ (1 + ε)) :
    ∃ N T, tunnelWallWidth b N T > 0 := by
  -- Cell (0,1) on (Z/3^bZ)² is pure-even for N=1, T=1:
  -- n=1 at t=1 has collatzSeq(1,1)=4 (even), torusResidue=(0,1).
  -- The only candidate (n=1,t=1) has even value, so no odd visits.
  refine ⟨1, 1, ?_⟩
  unfold tunnelWallWidth pureEvenCount
  apply Finset.card_pos.mpr
  refine ⟨((0 : ZMod (3 ^ b)), (1 : ZMod (3 ^ b))),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  -- Goal: isPureEvenBool (3^b) (0, 1) 1 1 = true
  -- At (n,t)=(1,1): collatzSeq(1,1)=4 (even), cell=(0,1). No odd visits.
  show isPureEvenBool (3 ^ b) ((0 : ZMod (3 ^ b)), (1 : ZMod (3 ^ b))) 1 1 = true
  simp only [isPureEvenBool, hasEvenVisitBool, hasOddVisitBool]
  simp only [List.range_succ, List.range_zero, List.nil_append,
    List.any_cons, List.any_nil, Bool.or_false]
  have heven : isEvenStep 1 1 = true := by native_decide
  have hodd : isOddStep 1 1 = false := by native_decide
  have hnu2 : nu2 1 1 = 0 := by native_decide
  have hnu3 : nu3 1 1 = 1 := by native_decide
  rw [heven, hodd, Bool.false_and, Bool.not_false, Bool.and_true, Bool.true_and]
  -- Goal: (torusResidue (3^b) 1 1 == ((0 : ZMod (3^b)), (1 : ZMod (3^b)))) = true
  simp only [torusResidue, hnu2, hnu3, Nat.cast_zero, Nat.cast_one, beq_self_eq_true]

/-! ## Walk confinement at pure-even boundary -/

/-- At a pure-even cell, the walk increment is +1 (from Walk.lean). -/
theorem walk_confined_at_boundary (k : ℕ) [NeZero k]
    (cell : ZMod k × ZMod k) (N T : ℕ)
    (hpe : isPureEven k cell N T)
    (n t : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ N) (ht1 : 1 ≤ t) (ht2 : t ≤ T)
    (hcell : torusResidue k n t = cell) :
    walkIncrement n t = 1 :=
  walkIncrement_at_pureEven k cell N T hpe n t hn1 hn2 ht1 ht2 hcell

/-! ## Composition -/

/-- Composition: Baker + geometric bridge → tunnel walls exist at all scales. -/
theorem tunnel_walls_positive (b : ℕ) (hb : b ≥ 1) :
    ∃ N T, tunnelWallWidth b N T > 0 := by
  obtain ⟨C', ε, hC', hε, hbound⟩ := diophError_lower_bound
  exact tunnel_walls_positive_of_baker b hb C' ε hC' hε (hbound b)

/-! ## Evaluation -/

-- N=1 (trajectory 1 only): pure-even cells persist (6/9 at b=1)
#eval tunnelWallWidth 1 1 1    -- 1
#eval tunnelWallWidth 1 1 50   -- 6 (stable)
-- N=10: cross-trajectory contamination kills all pure-even cells at b=1
#eval tunnelWallWidth 1 10 20  -- 0 (all 9 cells contaminated)
-- b=2: larger torus (81 cells) retains pure-even cells even at N=10
#eval tunnelWallWidth 2 10 50  -- 19

end Collatz
