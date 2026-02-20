import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Complex.Norm

open Complex Real
noncomputable section

-- Test: what does `norm_eq_zero` look like?
-- And test div_le_div_iff name
#check @div_le_div_iff
#check Complex.norm_ofReal
-- Test: can we show ((2*(T:ℝ)+1):ℂ) = ↑R ?
example (T : ℕ) : ((2 * (T : ℝ) + 1) : ℂ) = (↑(2 * (↑T : ℝ) + 1) : ℂ) := by
  push_cast; ring

-- So ((2*(T:ℝ)+1)^2:ℂ) = (↑R)^2 by norm_pow
-- Can we go: norm_pow ∘ norm_ofReal?
example (T : ℕ) : ‖((2 * (T : ℝ) + 1) ^ 2 : ℂ)‖ = (2 * (↑T : ℝ) + 1) ^ 2 := by
  have h1 : ((2 * (T : ℝ) + 1) ^ 2 : ℂ) = ((↑(2 * (↑T : ℝ) + 1) : ℂ)) ^ 2 := by
    push_cast; ring
  rw [h1, norm_pow, Complex.norm_ofReal, abs_of_nonneg (by positivity)]

end
