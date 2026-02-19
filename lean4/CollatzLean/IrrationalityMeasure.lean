/-
  CollatzLean/IrrationalityMeasure.lean
  Effective irrationality measure for log₂3 (Rhin 1987).

  Provides the transcendence lower bound needed by cycle elimination
  (Simons & de Weger 2005, Hercher 2024).

  Architecture:
  - Single axiom: rhin_irrationality_measure
  - All other results proved from this axiom + Baker.lean infrastructure
  - Interface: linearFormLog_lower_bound_of_rhin for cycle elimination
-/
import CollatzLean.Baker

namespace Collatz

open Real

/-! ## Rhin's effective irrationality measure -/

/-- Rhin's effective irrationality measure for log₂3.
    There exists C > 0 such that for all integers p, q with q > 0:
      |p/q - log₂3| > C / q^6

    This is a weakened form of Rhin's result (irrationality measure
    μ(log₂3) ≤ 5.125); using the integer exponent 6 avoids the need
    for real-valued powers while retaining the polynomial lower bound
    that contradicts the exponential upper bound in cycle elimination.

    Reference: G. Rhin, "Approximants de Padé et mesures effectives
    d'irrationalité", Progress in Mathematics 71 (1987), 155-164.

    This is the sole axiom in this file. All derived results are proved. -/
axiom rhin_irrationality_measure :
    ∃ (C : ℝ), C > 0 ∧
      ∀ (p : ℤ) (q : ℤ), q > 0 →
        |(↑p / ↑q : ℝ) - Real.logb 2 3| > C / (↑q : ℝ) ^ 6

/-! ## Algebraic identity: linear form ↔ rational approximation -/

/-- The linear form L·log 2 - K·log 3 equals K·(log 2)·(L/K - log₂3). -/
theorem linearForm_eq_approx (L K : ℤ) (hK : K > 0) :
    (↑L : ℝ) * Real.log 2 - ↑K * Real.log 3 =
      ↑K * Real.log 2 * ((↑L : ℝ) / ↑K - Real.logb 2 3) := by
  have hK_ne : (↑K : ℝ) ≠ 0 := ne_of_gt (Int.cast_pos.mpr hK)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold Real.logb
  field_simp

/-- Absolute value version of the algebraic identity. -/
theorem linearForm_abs_eq (L K : ℤ) (hK : K > 0) :
    |(↑L : ℝ) * Real.log 2 - ↑K * Real.log 3| =
      ↑K * Real.log 2 * |(↑L : ℝ) / ↑K - Real.logb 2 3| := by
  rw [linearForm_eq_approx L K hK, abs_mul,
      abs_of_pos (mul_pos (Int.cast_pos.mpr hK) (Real.log_pos (by norm_num)))]

/-! ## Linear form lower bound from Rhin -/

/-- Effective lower bound on |L·log 2 - K·log 3|.
    For K > 0:  |L·log 2 - K·log 3| > K · (log 2) · C / K^6
    Simplification: K · C / K^6 = C / K^5, giving a polynomial lower
    bound that contradicts the exponential upper bound from cycle equations. -/
theorem linear_form_lower_bound_rhin :
    ∃ (C : ℝ), C > 0 ∧
      ∀ (L K : ℤ), K > 0 →
        |(↑L : ℝ) * Real.log 2 - ↑K * Real.log 3| >
          ↑K * Real.log 2 * (C / (↑K : ℝ) ^ 6) := by
  obtain ⟨C, hC, hrhin⟩ := rhin_irrationality_measure
  exact ⟨C, hC, fun L K hK => by
    rw [linearForm_abs_eq L K hK]
    exact mul_lt_mul_of_pos_left (hrhin L K hK)
      (mul_pos (Int.cast_pos.mpr hK) (Real.log_pos (by norm_num)))⟩

/-! ## Connection to linearFormLog (Baker.lean) -/

/-- linearFormLog m n equals m·log 2 - (-n)·log 3 (subtraction form). -/
theorem linearFormLog_sub_eq (m n : ℤ) :
    linearFormLog m n = ↑m * Real.log 2 - ↑(-n) * Real.log 3 := by
  unfold linearFormLog
  simp only [Int.cast_neg]
  ring

/-- Lower bound on |linearFormLog m n| for n < 0 (the cycle case).
    In cycle notation: m = ν₂ (even steps), K = -n = ν₃ (odd steps).
    The bound is: |linearFormLog m n| > K · (log 2) · C / K^6. -/
theorem linearFormLog_lower_bound_of_rhin :
    ∃ (C : ℝ), C > 0 ∧
      ∀ (m n : ℤ), n < 0 →
        |linearFormLog m n| >
          ↑(-n) * Real.log 2 * (C / (↑(-n) : ℝ) ^ 6) := by
  obtain ⟨C, hC, hbound⟩ := linear_form_lower_bound_rhin
  exact ⟨C, hC, fun m n hn => by
    rw [linearFormLog_sub_eq m n]
    exact hbound m (-n) (by omega)⟩

/-! ## Positivity of the bound for specific parameters -/

/-- The Rhin bound gives a positive lower bound for any specific K ≥ 1. -/
theorem rhin_bound_pos (L K : ℤ) (hK : K ≥ 1) :
    ∃ (b : ℝ), b > 0 ∧ |(↑L : ℝ) * Real.log 2 - ↑K * Real.log 3| > b := by
  obtain ⟨C, hC, hbound⟩ := linear_form_lower_bound_rhin
  have hK_pos : K > 0 := by omega
  have hK_cast_pos : (↑K : ℝ) > 0 := Int.cast_pos.mpr hK_pos
  refine ⟨↑K * Real.log 2 * (C / (↑K : ℝ) ^ 6), ?_, hbound L K hK_pos⟩
  apply mul_pos (mul_pos hK_cast_pos (Real.log_pos (by norm_num)))
  exact div_pos hC (pow_pos hK_cast_pos 6)

end Collatz
