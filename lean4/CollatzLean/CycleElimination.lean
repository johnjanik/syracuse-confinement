/-
  CollatzLean/CycleElimination.lean

  Cycle elimination: analytical infrastructure + main theorem.

  Architecture:
  - cycle_lower_bound: polynomial lower bound on |Λ| from Rhin's irrationality
    measure (proved, uses IrrationalityMeasure.lean)
  - cycle_upper_bound: log(1+x) < x upper bound on Λ from cycle equation
    (proved, pure analysis)
  - cycleLinearForm_pos: positivity of the linear form (proved)
  - cycle_elim_from_rhin: main cycle elimination theorem, delegates to
    SteinerCycle.lean's baker_no_balanced_cycle which decomposes into:
    * Δ₃ ≤ 79: proved via K-bound + Hercher's theorem (no m-cycle for m ≤ 91)
    * Δ₃ ≥ 80: sorry (frontier — requires extending Hercher beyond m = 91)

  The analytical bounds (cycle_lower_bound, cycle_upper_bound) are kept as
  sorry-free infrastructure for future work on the Δ₃ ≥ 80 case, where a
  tighter correction-based upper bound could replace the naive log(1+x) < x.

  References:
  - Rhin (1987), effective irrationality measure for log₂3
  - Steiner (1977), cycle equation structure
  - Simons & de Weger (2005), computational cycle elimination
  - Hercher (2024), extended to m ≤ 91
-/
import CollatzLean.Baker
import CollatzLean.IrrationalityMeasure
import CollatzLean.SteinerCycle

namespace Collatz

open Real

/-! ## The linear form from cycle parameters -/

/-- The linear form Λ = ν₂·log 2 - ν₃·log 3, expressed via linearFormLog.
    For a cycle with ν₂ even steps and ν₃ odd steps, this measures how close
    the ratio ν₂/ν₃ is to log₂3 ≈ 1.585. -/
noncomputable def cycleLinearForm (c₀ p : ℕ) : ℝ :=
  linearFormLog (cycleNu2 c₀ p : ℤ) (-(cycleNu3 c₀ p : ℤ))

/-- The cycle linear form equals ν₂·log 2 - ν₃·log 3. -/
theorem cycleLinearForm_eq (c₀ p : ℕ) :
    cycleLinearForm c₀ p =
      (cycleNu2 c₀ p : ℝ) * Real.log 2 - (cycleNu3 c₀ p : ℝ) * Real.log 3 := by
  unfold cycleLinearForm linearFormLog
  push_cast
  ring

/-! ## Lower bound from Rhin -/

/-- The Rhin irrationality measure gives a polynomial lower bound on the
    cycle linear form. For ν₃ ≥ 1:
      |Λ| > ν₃ · log 2 · C / ν₃^6
    which simplifies to C · log 2 / ν₃^5.

    This is the key "transcendence input" — the linear form cannot be
    too close to zero because log₂3 is not well-approximable by rationals. -/
theorem cycle_lower_bound :
    ∃ (C : ℝ), C > 0 ∧
      ∀ (c₀ p : ℕ), cycleNu3 c₀ p ≥ 1 →
        |cycleLinearForm c₀ p| >
          ↑(cycleNu3 c₀ p) * Real.log 2 * (C / (↑(cycleNu3 c₀ p) : ℝ) ^ 6) := by
  obtain ⟨C, hC, hbound⟩ := linearFormLog_lower_bound_of_rhin
  exact ⟨C, hC, fun c₀ p hν₃ => by
    unfold cycleLinearForm
    have hν₃_neg : (-(cycleNu3 c₀ p : ℤ)) < 0 := by omega
    have h := hbound (cycleNu2 c₀ p : ℤ) (-(cycleNu3 c₀ p : ℤ)) hν₃_neg
    simp only [neg_neg, Int.cast_natCast] at h
    exact h⟩

/-! ## Upper bound from cycle equation -/

/-- Upper bound on the linear form from the cycle equation.

    From the cycle identity c₀ · 2^ν₂ = c₀ · 3^ν₃ + correction, periodicity
    gives 2^ν₂/3^ν₃ = 1 + corr/(c₀ · 3^ν₃), so
    Λ = ν₂·log 2 - ν₃·log 3 = log(2^ν₂/3^ν₃) = log(1 + corr/(c₀·3^ν₃)).

    Since log(x) < x - 1 for x > 0, x ≠ 1 (Mathlib: Real.log_lt_sub_one_of_pos),
    we get Λ < (2^ν₂ - 3^ν₃)/3^ν₃.

    This bound is available as sorry-free infrastructure for future work on
    tighter cycle elimination. -/
theorem cycle_upper_bound (c₀ p : ℕ)
    (_hc : c₀ ≥ 2)
    (_hcycle : collatzStep^[p] c₀ = c₀)
    (_hν₃ : cycleNu3 c₀ p ≥ 1)
    (hexp : 2 ^ cycleNu2 c₀ p > 3 ^ cycleNu3 c₀ p) :
    cycleLinearForm c₀ p <
      ((2 : ℝ) ^ cycleNu2 c₀ p - (3 : ℝ) ^ cycleNu3 c₀ p) /
        (3 : ℝ) ^ cycleNu3 c₀ p := by
  rw [cycleLinearForm_eq]
  -- Positivity facts
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ cycleNu3 c₀ p := by positivity
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ cycleNu2 c₀ p := by positivity
  have h3ne : (3 : ℝ) ^ cycleNu3 c₀ p ≠ 0 := ne_of_gt h3pos
  have h2ne : (2 : ℝ) ^ cycleNu2 c₀ p ≠ 0 := ne_of_gt h2pos
  -- Rewrite LHS as log(2^ν₂ / 3^ν₃)
  have hlhs : (↑(cycleNu2 c₀ p) : ℝ) * Real.log 2 - (↑(cycleNu3 c₀ p) : ℝ) * Real.log 3 =
      Real.log ((2 : ℝ) ^ cycleNu2 c₀ p / (3 : ℝ) ^ cycleNu3 c₀ p) := by
    rw [Real.log_div h2ne h3ne, Real.log_pow, Real.log_pow]
  rw [hlhs]
  -- Set x = 2^ν₂ / 3^ν₃, show x > 1
  set x := (2 : ℝ) ^ cycleNu2 c₀ p / (3 : ℝ) ^ cycleNu3 c₀ p with hx_def
  have hx_pos : 0 < x := div_pos h2pos h3pos
  have hx_gt1 : x > 1 := by
    rw [hx_def, gt_iff_lt, one_lt_div h3pos]
    exact_mod_cast hexp
  -- log(x) < x - 1 for x > 0, x ≠ 1
  have hlog_lt := Real.log_lt_sub_one_of_pos hx_pos (ne_of_gt hx_gt1)
  -- x - 1 = (2^ν₂ - 3^ν₃) / 3^ν₃
  have hx_sub : x - 1 = ((2 : ℝ) ^ cycleNu2 c₀ p - (3 : ℝ) ^ cycleNu3 c₀ p) /
      (3 : ℝ) ^ cycleNu3 c₀ p := by
    rw [hx_def, div_sub_one h3ne]
  linarith

/-! ## Positivity of cycle linear form -/

/-- The cycle linear form is positive when 2^ν₂ > 3^ν₃. -/
theorem cycleLinearForm_pos (c₀ p : ℕ)
    (hexp : 2 ^ cycleNu2 c₀ p > 3 ^ cycleNu3 c₀ p) :
    cycleLinearForm c₀ p > 0 := by
  rw [cycleLinearForm_eq]
  have hlog2 : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have hlog3 : Real.log 3 > 0 := Real.log_pos (by norm_num)
  -- 2^ν₂ > 3^ν₃ implies ν₂·log 2 > ν₃·log 3 (since log is monotone)
  have h2 : Real.log ((2 : ℝ) ^ cycleNu2 c₀ p) >
             Real.log ((3 : ℝ) ^ cycleNu3 c₀ p) := by
    apply Real.log_lt_log
    · positivity
    · exact_mod_cast hexp
  rw [Real.log_pow, Real.log_pow] at h2
  linarith

/-! ## Main theorem: cycle elimination -/

/-- Cycle elimination via Steiner/Hercher analysis.

    No non-trivial Collatz cycle exists with period p = 3·Δ₃ for Δ₃ ≥ 2.
    Any such cycle must pass through 1.

    Delegates to SteinerCycle.lean's baker_no_balanced_cycle, which decomposes:
    - Δ₃ ≤ 79: proved (K-bound gives ν₃ ≤ 91, then Hercher eliminates)
    - Δ₃ ≥ 80: sorry (frontier — requires extending Hercher beyond m = 91)

    References: Steiner (1977), Simons & de Weger (2005), Hercher (2024). -/
theorem cycle_elim_from_rhin (Δ₃ : ℕ) (hΔ : Δ₃ ≥ 2)
    (c₀ : ℕ) (hc : c₀ ≥ 1)
    (hcycle : collatzStep^[3 * Δ₃] c₀ = c₀) :
    ∃ t, t < 3 * Δ₃ ∧ collatzStep^[t] c₀ = 1 :=
  baker_no_balanced_cycle Δ₃ hΔ c₀ hc hcycle

end Collatz
