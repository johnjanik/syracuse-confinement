/-
  CollatzLean/SimultaneousApprox.lean
  Core definitions for simultaneous Diophantine approximation
  and Littlewood's conjecture.

  Defines:
  - fracDist: distance to nearest integer ||x||
  - littlewoodProduct: n · ||n·α|| · ||n·β||
  - LittlewoodHolds: the conjecture for a specific pair (α, β)

  Connects to the linear form infrastructure in LinearFormThree.lean
  and to the cell coordinates used in DiophantineRepeller.lean.
-/
import CollatzLean.LinearFormThree
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

set_option linter.style.nativeDecide false

namespace Collatz

open Real Filter

/-! ## Fractional distance to nearest integer -/

/-- The distance from x to the nearest integer: ||x|| = |x - round(x)|.
    This equals min(frac(x), 1 - frac(x)) where frac(x) = x - ⌊x⌋. -/
noncomputable def fracDist (x : ℝ) : ℝ := |x - round x|

/-- fracDist is non-negative. -/
theorem fracDist_nonneg (x : ℝ) : fracDist x ≥ 0 :=
  abs_nonneg _

/-- fracDist is at most 1/2. -/
theorem fracDist_le_half (x : ℝ) : fracDist x ≤ 1 / 2 := by
  exact abs_sub_round x

/-- fracDist of an integer is 0. -/
theorem fracDist_int (n : ℤ) : fracDist (↑n : ℝ) = 0 := by
  unfold fracDist
  have : round (↑n : ℝ) = n := round_intCast n
  rw [this, sub_self, abs_zero]

/-- fracDist is zero iff x is an integer. -/
theorem fracDist_eq_zero_iff (x : ℝ) : fracDist x = 0 ↔ ∃ n : ℤ, x = ↑n := by
  unfold fracDist
  constructor
  · intro h
    rw [abs_eq_zero, sub_eq_zero] at h
    exact ⟨round x, h⟩
  · rintro ⟨n, rfl⟩
    have : round (↑n : ℝ) = n := round_intCast n
    rw [this, sub_self, abs_zero]

/-! ## Littlewood product -/

/-- The Littlewood product for a pair (α, β) at index n:
    L(n) = n · ||n·α|| · ||n·β|| -/
noncomputable def littlewoodProduct (α β : ℝ) (n : ℕ) : ℝ :=
  ↑n * fracDist (↑n * α) * fracDist (↑n * β)

/-- The Littlewood product is non-negative. -/
theorem littlewoodProduct_nonneg (α β : ℝ) (n : ℕ) :
    littlewoodProduct α β n ≥ 0 := by
  unfold littlewoodProduct
  apply mul_nonneg
  · apply mul_nonneg
    · exact Nat.cast_nonneg n
    · exact abs_nonneg _
  · exact abs_nonneg _

/-- The Littlewood product at n=0 is 0. -/
theorem littlewoodProduct_zero (α β : ℝ) : littlewoodProduct α β 0 = 0 := by
  unfold littlewoodProduct; simp

/-- The Littlewood product is 0 iff n=0, or n·α is an integer, or n·β
    is an integer. -/
theorem littlewoodProduct_eq_zero_iff (α β : ℝ) (n : ℕ) :
    littlewoodProduct α β n = 0 ↔
    n = 0 ∨ (∃ k : ℤ, ↑n * α = ↑k) ∨ (∃ k : ℤ, ↑n * β = ↑k) := by
  unfold littlewoodProduct
  rw [mul_eq_zero, mul_eq_zero]
  constructor
  · rintro ((hn | ha) | hb)
    · left; exact_mod_cast hn
    · right; left; rwa [fracDist_eq_zero_iff] at ha
    · right; right; rwa [fracDist_eq_zero_iff] at hb
  · rintro (rfl | ⟨k, hk⟩ | ⟨k, hk⟩)
    · left; left; simp
    · left; right; rw [fracDist_eq_zero_iff]; exact ⟨k, hk⟩
    · right; rw [fracDist_eq_zero_iff]; exact ⟨k, hk⟩

/-! ## Littlewood's conjecture -/

/-- **Littlewood's conjecture** for a specific pair (α, β):
    For every ε > 0, there exist arbitrarily large n with
    n · ||n·α|| · ||n·β|| < ε. -/
noncomputable def LittlewoodHolds (α β : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ littlewoodProduct α β n < ε

/-! ## Specialization to (log₂5, log₂7) -/

/-- The specific pair for our Littlewood study. -/
noncomputable def α_L : ℝ := logb 2 5
noncomputable def β_L : ℝ := logb 2 7

/-- Littlewood's conjecture for (log₂5, log₂7). -/
noncomputable def LittlewoodFor257 : Prop := LittlewoodHolds α_L β_L

/-! ## Upper bound on product via simultaneous approximation quality -/

/-- If ||n·α|| < δ₁ and ||n·β|| < δ₂, then the Littlewood product < n·δ₁·δ₂. -/
theorem littlewoodProduct_lt_of_close (α β : ℝ) (n : ℕ) (δ₁ δ₂ : ℝ)
    (hn : n ≥ 1)
    (h₁ : fracDist (↑n * α) < δ₁) (h₂ : fracDist (↑n * β) < δ₂)
    (hδ₁ : δ₁ > 0) (hδ₂ : δ₂ > 0) :
    littlewoodProduct α β n < ↑n * δ₁ * δ₂ := by
  unfold littlewoodProduct
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  calc ↑n * fracDist (↑n * α) * fracDist (↑n * β)
      ≤ ↑n * δ₁ * fracDist (↑n * β) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (le_of_lt h₁) (le_of_lt hn_pos)
        · exact fracDist_nonneg _
    _ < ↑n * δ₁ * δ₂ := by
        apply mul_lt_mul_of_pos_left h₂
        exact mul_pos hn_pos hδ₁

/-! ## Connection to 2D torus cells -/

/-- The 2D torus cell at scale K: discretize the fractional parts of
    (n·α, n·β) into a K×K grid. -/
noncomputable def torusCell (α β : ℝ) (K : ℕ) (n : ℕ) : ℕ × ℕ :=
  let fa := ↑n * α - ↑(⌊↑n * α⌋)  -- fractional part of n·α
  let fb := ↑n * β - ↑(⌊↑n * β⌋)  -- fractional part of n·β
  (⌊fa * ↑K⌋.toNat % K, ⌊fb * ↑K⌋.toNat % K)

end Collatz
