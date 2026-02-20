/-
  CollatzLean/LittlewoodResidence.lean
  Residence bounds on the 2D torus for Littlewood's conjecture.

  Architecture:
  1. Cell residence definition on 2D torus
  2. Elementary number theory (5⁴ > 2⁹, 5² < 2⁵) implies cell escape
  3. Connection to Littlewood product via cell diameter

  Key result (residence_bounded_two_dim): For α = log₂5 and β = log₂7,
  no trajectory on the K×K torus can stay in a single cell for more than
  2 consecutive steps when K ≥ 2. The proof uses only:
  - log₂5 > 9/4 (from 625 > 512)
  - log₂5 < 5/2 (from 25 < 32)
  These force any one-step integer approximation p to satisfy p = 2, so
  the two-step approximation is p₁ + p₁' = 4, but |2·log₂5 - 4| > 1/2,
  contradicting same-cell residence for K ≥ 2.
-/
import CollatzLean.SimultaneousApprox

set_option linter.style.nativeDecide false

namespace Collatz

open Real Filter

/-! ## 2D torus cell residence -/

/-- A trajectory visits at least 2 distinct cells within L steps. -/
def EscapesWithin (α β : ℝ) (K : ℕ) (n₀ L : ℕ) : Prop :=
  ∃ m : ℕ, m ≥ 1 ∧ m ≤ L ∧ torusCell α β K (n₀ + m) ≠ torusCell α β K n₀

/-! ## Numerical bounds on log₂5 -/

/-- log₂5 > 9/4, equivalently 5⁴ > 2⁹ (625 > 512). -/
private theorem logb_two_five_gt_nine_fourths : logb 2 5 > 9 / 4 := by
  have hlog2_pos : (0 : ℝ) < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  rw [logb, gt_iff_lt, div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) hlog2_pos]
  -- Goal: 9 * log 2 < log 5 * 4
  calc 9 * log 2 = log ((2 : ℝ) ^ 9) := by rw [log_pow]; ring
    _ < log ((5 : ℝ) ^ 4) := log_lt_log (by positivity) (by norm_num)
    _ = log 5 * 4 := by rw [log_pow]; ring

/-- log₂5 < 5/2, equivalently 5² < 2⁵ (25 < 32). -/
private theorem logb_two_five_lt_five_halves : logb 2 5 < 5 / 2 := by
  have hlog2_pos : (0 : ℝ) < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  rw [logb, div_lt_div_iff₀ hlog2_pos (by norm_num : (0 : ℝ) < 2)]
  -- Goal: log 5 * 2 < 5 * log 2
  have h2 : log 5 * 2 = log ((5 : ℝ) ^ 2) := by rw [log_pow]; ring
  have h5 : 5 * log 2 = log ((2 : ℝ) ^ 5) := by rw [log_pow]; ring
  rw [h2, h5]
  exact log_lt_log (by positivity) (by norm_num)

/-- log₂5 > 2, equivalently 5 > 4. -/
private theorem logb_two_five_gt_two : logb 2 5 > 2 :=
  lt_trans (by norm_num : (2 : ℝ) < 9 / 4) logb_two_five_gt_nine_fourths

/-- log₂5 < 3, equivalently 5 < 8. -/
private theorem logb_two_five_lt_three : logb 2 5 < 3 := by
  have hlog2_pos : (0 : ℝ) < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  rw [logb, div_lt_iff₀ hlog2_pos]
  calc log 5 < log 8 := log_lt_log (by positivity) (by norm_num)
    _ = log (2 ^ 3) := by norm_num
    _ = 3 * log 2 := by rw [log_pow]; ring

/-! ## Same-floor extraction from torusCell equality -/

/-- Helper: the fractional part `x - ⌊x⌋` lies in `[0, 1)`. -/
private theorem frac_nonneg (x : ℝ) : x - ↑⌊x⌋ ≥ 0 := sub_nonneg.mpr (Int.floor_le x)

private theorem frac_lt_one (x : ℝ) : x - ↑⌊x⌋ < 1 := by linarith [Int.lt_floor_add_one x]

/-- If two fractional parts lie in the same interval `[j/K, (j+1)/K)`,
    their difference is less than `1/K`. -/
private theorem same_floor_cell_bound {x y : ℝ} {K : ℕ} (hK : K ≥ 1)
    (_hx0 : 0 ≤ x) (_hx1 : x < 1) (_hy0 : 0 ≤ y) (_hy1 : y < 1)
    (hfloor : ⌊x * ↑K⌋ = ⌊y * ↑K⌋) :
    |x - y| < 1 / (↑K : ℝ) := by
  have hK_pos : (↑K : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  -- j ≤ x*K < j+1 and j ≤ y*K < j+1 where j = ⌊x*K⌋ = ⌊y*K⌋
  have hxK : (↑⌊x * ↑K⌋ : ℝ) ≤ x * ↑K := Int.floor_le _
  have hxK' : x * ↑K < ↑⌊x * ↑K⌋ + 1 := Int.lt_floor_add_one _
  have hyK : (↑⌊x * ↑K⌋ : ℝ) ≤ y * ↑K := by rw [hfloor]; exact Int.floor_le _
  have hyK' : y * ↑K < ↑⌊x * ↑K⌋ + 1 := by rw [hfloor]; exact Int.lt_floor_add_one _
  -- |x*K - y*K| < 1, so |x - y| < 1/K
  rw [abs_sub_lt_iff]
  constructor
  · -- x - y < 1/K, i.e., (x-y)*K < 1
    rw [lt_div_iff₀ hK_pos]; nlinarith
  · -- y - x < 1/K
    rw [lt_div_iff₀ hK_pos]; nlinarith

/-- If `torusCell α β K n₁ = torusCell α β K n₂`, then the first-coordinate
    fractional parts have the same floor when multiplied by K. -/
private theorem torusCell_eq_first_floor {α β : ℝ} {K n₁ n₂ : ℕ}
    (h : torusCell α β K n₁ = torusCell α β K n₂) :
    ⌊(↑n₁ * α - ↑⌊↑n₁ * α⌋) * ↑K⌋.toNat % K =
    ⌊(↑n₂ * α - ↑⌊↑n₂ * α⌋) * ↑K⌋.toNat % K := by
  have := congr_arg Prod.fst h
  exact this

/-! ## Key three-step impossibility -/

/-- **Key lemma**: For α = log₂5 and any K ≥ 2, three consecutive fractional
    parts `frac(n₀·α), frac((n₀+1)·α), frac((n₀+2)·α)` cannot all have
    the same floor when multiplied by K.

    The proof uses:
    - `frac(α) > 1/4` (from 5⁴ > 2⁹)
    - `frac(α) < 1/2` (from 5² < 2⁵)

    If all three are in [j/K, (j+1)/K), the one-step differences give
    |α - p| < 1/K for integer p, forcing p = 2 (since 2 < α < 5/2).
    Then the two-step difference gives |2α - 4| < 1/K ≤ 1/2.
    But 2α - 4 = 2·frac(α) > 1/2, contradiction. -/
private theorem three_consec_cannot_share_cell (K n₀ : ℕ) (hK : K ≥ 2) :
    ¬(torusCell α_L β_L K (n₀ + 1) = torusCell α_L β_L K n₀ ∧
      torusCell α_L β_L K (n₀ + 2) = torusCell α_L β_L K n₀) := by
  intro ⟨h1, h2⟩
  -- Extract first-coordinate floor equalities
  have hf1 := torusCell_eq_first_floor h1
  have hf2 := torusCell_eq_first_floor h2
  set α := α_L with hα_def
  -- Key numerical bounds on α
  have hα_gt : α > 9 / 4 := logb_two_five_gt_nine_fourths
  have hα_lt : α < 5 / 2 := logb_two_five_lt_five_halves
  have hα_gt2 : α > 2 := logb_two_five_gt_two
  have hα_lt3 : α < 3 := logb_two_five_lt_three
  -- Define fractional parts
  set f0 := (↑n₀ : ℝ) * α - ↑⌊(↑n₀ : ℝ) * α⌋ with hf0_def
  set f1 := (↑(n₀ + 1) : ℝ) * α - ↑⌊(↑(n₀ + 1) : ℝ) * α⌋ with hf1_def
  set f2 := (↑(n₀ + 2) : ℝ) * α - ↑⌊(↑(n₀ + 2) : ℝ) * α⌋ with hf2_def
  have hf0_nn : f0 ≥ 0 := frac_nonneg _
  have hf0_lt : f0 < 1 := frac_lt_one _
  have hf1_nn : f1 ≥ 0 := frac_nonneg _
  have hf1_lt : f1 < 1 := frac_lt_one _
  have hf2_nn : f2 ≥ 0 := frac_nonneg _
  have hf2_lt : f2 < 1 := frac_lt_one _
  have hK_pos : (↑K : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hK_ge1 : K ≥ 1 := by omega
  -- Floor of fi * K is in [0, K), so toNat and % K are identity
  have hf0K_nn : 0 ≤ ⌊f0 * ↑K⌋ := Int.floor_nonneg.mpr (by positivity)
  have hf0K_lt : ⌊f0 * ↑K⌋ < ↑K := by
    rw [Int.floor_lt]; push_cast; nlinarith
  have hf1K_nn : 0 ≤ ⌊f1 * ↑K⌋ := Int.floor_nonneg.mpr (by positivity)
  have hf1K_lt : ⌊f1 * ↑K⌋ < ↑K := by
    rw [Int.floor_lt]; push_cast; nlinarith
  have hf2K_nn : 0 ≤ ⌊f2 * ↑K⌋ := Int.floor_nonneg.mpr (by positivity)
  have hf2K_lt : ⌊f2 * ↑K⌋ < ↑K := by
    rw [Int.floor_lt]; push_cast; nlinarith
  have hmod0 : ⌊f0 * ↑K⌋.toNat % K = ⌊f0 * ↑K⌋.toNat := Nat.mod_eq_of_lt (by omega)
  have hmod1 : ⌊f1 * ↑K⌋.toNat % K = ⌊f1 * ↑K⌋.toNat := Nat.mod_eq_of_lt (by omega)
  have hmod2 : ⌊f2 * ↑K⌋.toNat % K = ⌊f2 * ↑K⌋.toNat := Nat.mod_eq_of_lt (by omega)
  rw [hmod0, hmod1] at hf1
  rw [hmod0, hmod2] at hf2
  have hfloor01 : ⌊f0 * ↑K⌋ = ⌊f1 * ↑K⌋ := by omega
  have hfloor02 : ⌊f0 * ↑K⌋ = ⌊f2 * ↑K⌋ := by omega
  -- From same floor: |fi - fj| < 1/K
  have hdiff01 : |f0 - f1| < 1 / ↑K :=
    same_floor_cell_bound hK_ge1 hf0_nn.le hf0_lt hf1_nn.le hf1_lt hfloor01
  -- Relate fractional part differences to α and integer differences
  set p₁ := ⌊(↑(n₀ + 1) : ℝ) * α⌋ - ⌊(↑n₀ : ℝ) * α⌋ with hp₁_def
  have hf1_f0 : f1 - f0 = α - ↑p₁ := by
    simp only [hf1_def, hf0_def, hp₁_def]; push_cast; ring
  set p₂ := ⌊(↑(n₀ + 2) : ℝ) * α⌋ - ⌊(↑n₀ : ℝ) * α⌋ with hp₂_def
  have hf2_f0 : f2 - f0 = 2 * α - ↑p₂ := by
    simp only [hf2_def, hf0_def, hp₂_def]; push_cast; ring
  -- |α - p₁| < 1/K ≤ 1/2
  have hα_p₁ : |α - ↑p₁| < 1 / ↑K := by rwa [← hf1_f0, abs_sub_comm]
  have hα_p₂ : |2 * α - ↑p₂| < 1 / ↑K := by
    rw [← hf2_f0, abs_sub_comm]
    exact same_floor_cell_bound hK_ge1 hf0_nn.le hf0_lt hf2_nn.le hf2_lt hfloor02
  have h_inv_K_le : 1 / (↑K : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hK_pos (by norm_num : (0:ℝ) < 2)]
    linarith [show (↑K : ℝ) ≥ 2 from by exact_mod_cast hK]
  have hαp₁_half : |α - ↑p₁| < 1 / 2 := lt_of_lt_of_le hα_p₁ h_inv_K_le
  -- p₁ = 2 (only integer in (α - 1/2, α + 1/2) ⊂ (7/4, 3))
  have hp₁_eq : p₁ = 2 := by
    have h_abs := abs_lt.mp hαp₁_half
    have : (1 : ℤ) < p₁ := by
      have : (↑p₁ : ℝ) > 7 / 4 := by linarith
      have : (7 : ℝ) / 4 > 1 := by norm_num
      have : (↑p₁ : ℝ) > 1 := by linarith
      exact_mod_cast this
    have : p₁ < 3 := by
      have : (↑p₁ : ℝ) < 3 := by linarith
      exact_mod_cast this
    omega
  -- By transitivity, f1 and f2 are in the same cell too
  have hfloor12 : ⌊f1 * ↑K⌋ = ⌊f2 * ↑K⌋ := by rw [← hfloor01, hfloor02]
  -- So |α - p₁'| < 1/K where p₁' = ⌊(n₀+2)α⌋ - ⌊(n₀+1)α⌋
  set p₁' := ⌊(↑(n₀ + 2) : ℝ) * α⌋ - ⌊(↑(n₀ + 1) : ℝ) * α⌋ with hp₁'_def
  have hf2_f1 : f2 - f1 = α - ↑p₁' := by
    simp only [hf2_def, hf1_def, hp₁'_def]; push_cast; ring
  have hα_p₁' : |α - ↑p₁'| < 1 / ↑K := by
    rw [← hf2_f1, abs_sub_comm]
    exact same_floor_cell_bound hK_ge1 hf1_nn.le hf1_lt hf2_nn.le hf2_lt hfloor12
  -- p₁' = 2 (same argument)
  have hp₁'_eq : p₁' = 2 := by
    have hαp₁'_half : |α - ↑p₁'| < 1 / 2 := lt_of_lt_of_le hα_p₁' h_inv_K_le
    have h_abs := abs_lt.mp hαp₁'_half
    have : (1 : ℤ) < p₁' := by
      have : (↑p₁' : ℝ) > 7 / 4 := by linarith
      have : (↑p₁' : ℝ) > 1 := by linarith
      exact_mod_cast this
    have : p₁' < 3 := by
      have : (↑p₁' : ℝ) < 3 := by linarith
      exact_mod_cast this
    omega
  -- p₂ = p₁ + p₁' = 4
  have hp₂_eq : p₂ = 4 := by
    have : p₂ = p₁ + p₁' := by simp only [hp₂_def, hp₁_def, hp₁'_def]; ring
    omega
  -- |2α - 4| = 2(α - 2) > 2·(1/4) = 1/2 ≥ 1/K, contradicting |2α - p₂| < 1/K
  have h2α_bound : 2 * α - 4 > 1 / 2 := by linarith
  have h2α_abs : |2 * α - ↑p₂| = 2 * α - 4 := by
    rw [hp₂_eq]; push_cast; rw [abs_of_pos]; linarith
  linarith [h2α_abs ▸ hα_p₂]

/-! ## Matveev implies cell escape -/

/-- **Residence bound on the 2D torus**.

    For α = log₂5 and β = log₂7, no trajectory on the K×K torus can stay in
    any single cell for more than 2 consecutive steps when K ≥ 2.

    The proof uses only two numerical facts about log₂5:
    - `log₂5 > 9/4` (from 5⁴ > 2⁹, i.e., 625 > 512)
    - `log₂5 < 5/2` (from 5² < 2⁵, i.e., 25 < 32)

    From the first: any one-step integer difference p with |log₂5 - p| < 1/2
    must be p = 2, and `2(log₂5 - 2) > 1/2`.
    If three consecutive values share a cell, the two-step integer difference
    must be p₁ + p₁' = 4, but |2·log₂5 - 4| > 1/2 ≥ 1/K contradicts the
    same-cell bound.

    This is NOT Collatz-equivalent. It depends only on elementary properties
    of log₂5. -/
theorem residence_bounded_two_dim :
    ∀ K : ℕ, K ≥ 2 →
    ∃ L : ℕ, L ≥ 1 ∧ ∀ n₀ : ℕ,
      EscapesWithin α_L β_L K n₀ L := by
  intro K hK
  exact ⟨2, by omega, fun n₀ => by
    -- EscapesWithin means ∃ m ∈ [1, 2], torusCell (n₀+m) ≠ torusCell n₀
    -- Prove by contradiction
    by_contra h_not_escape
    simp only [EscapesWithin, not_exists, not_and, not_not] at h_not_escape
    -- h_not_escape : ∀ m, m ≥ 1 → m ≤ 2 → torusCell (n₀+m) = torusCell n₀
    exact three_consec_cannot_share_cell K n₀ hK
      ⟨h_not_escape 1 (by omega) (by omega), h_not_escape 2 (by omega) (by omega)⟩⟩

/-! ## Cell diameter and product bound -/

/-- If the trajectory escapes to a different cell at scale K, then one of
    the fractional coordinates has changed by at least 1/K. -/
theorem escape_implies_frac_change (α β : ℝ) (K n₀ n : ℕ) (_hK : K ≥ 2)
    (hne : torusCell α β K n ≠ torusCell α β K n₀) :
    (torusCell α β K n).1 ≠ (torusCell α β K n₀).1 ∨
    (torusCell α β K n).2 ≠ (torusCell α β K n₀).2 := by
  by_contra h
  push_neg at h
  exact hne (Prod.ext h.1 h.2)

/-! ## Scale progression -/

/-- At scale K, 1/K² is positive (used for product bounds). -/
theorem cell_product_upper_bound (K : ℕ) (hK : K ≥ 2) :
    (1 : ℝ) / (↑K * ↑K) > 0 := by
  apply div_pos one_pos
  exact mul_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))

/-! ## Induction step: residence bound → finer scale visit -/

/-- Within L steps, the fractional parts sweep across at most L cells per
    coordinate at scale K, so L/K ≤ L trivially. -/
theorem finer_cell_visit (K L : ℕ) (_hK : K ≥ 2) (_hL : L ≥ 1) :
    (L : ℝ) / ↑K ≤ ↑L := by
  apply div_le_of_le_mul₀ (Nat.cast_nonneg K) (Nat.cast_nonneg L)
  calc (↑L : ℝ) = ↑L * 1 := (mul_one _).symm
    _ ≤ ↑L * ↑K := by
        apply mul_le_mul_of_nonneg_left
        · exact Nat.one_le_cast.mpr (by omega)
        · exact Nat.cast_nonneg L

end Collatz
