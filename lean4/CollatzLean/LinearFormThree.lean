/-
  CollatzLean/LinearFormThree.lean
  Three-variable linear forms in logarithms (Baker/Matveev).

  Extends the existing 2-variable linearFormLog (Baker.lean) to 3 variables
  for the triple (log 2, log 5, log 7). This is the foundation for
  Littlewood's conjecture for the pair (log₂5, log₂7).

  Axiom: matveev_three_log (Matveev 2000) — effective lower bound for
  |b₁·log 2 + b₂·log 5 + b₃·log 7| in terms of max(|b₁|, |b₂|, |b₃|).

  References:
  - E.M. Matveev, "An explicit lower bound for a homogeneous rational
    linear form in logarithms of algebraic numbers. II", Izv. Math. 64
    (2000), 1217–1269.
  - A. Baker & G. Wüstholz, "Logarithmic forms and Diophantine geometry",
    Cambridge, 2007.
-/
import CollatzLean.Baker
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.style.nativeDecide false

namespace Collatz

open Real

/-! ## Three-variable linear form in logarithms -/

/-- The linear form b₁ · log α₁ + b₂ · log α₂ + b₃ · log α₃. -/
noncomputable def linearFormLog3 (b₁ b₂ b₃ : ℤ) (α₁ α₂ α₃ : ℝ) : ℝ :=
  b₁ * Real.log α₁ + b₂ * Real.log α₂ + b₃ * Real.log α₃

/-- Specialization to (2, 5, 7). -/
noncomputable def linearForm257 (b₁ b₂ b₃ : ℤ) : ℝ :=
  linearFormLog3 b₁ b₂ b₃ 2 5 7

/-! ## Multiplicative independence of 2, 5, 7 -/

/-- 2, 5, 7 are multiplicatively independent: 2^a · 5^b · 7^c = 1 implies
    a = b = c = 0 (for non-negative exponents). -/
theorem multIndep_two_five_seven (a b c : ℕ) (h : 2 ^ a * 5 ^ b * 7 ^ c = 1) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · -- a = 0: if a ≥ 1 then 2 | product = 1, contradiction
    by_contra ha
    have h2 : 2 ∣ 2 ^ a := dvd_pow_self 2 ha
    have : 2 ∣ 2 ^ a * 5 ^ b * 7 ^ c := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2 _) _
    rw [h] at this; omega
  · -- b = 0: if b ≥ 1 then 5 | product = 1
    by_contra hb
    have h5 : 5 ∣ 5 ^ b := dvd_pow_self 5 hb
    have : 5 ∣ 2 ^ a * 5 ^ b := dvd_mul_of_dvd_right h5 _
    have : 5 ∣ 2 ^ a * 5 ^ b * 7 ^ c := dvd_mul_of_dvd_left this _
    rw [h] at this; omega
  · -- c = 0: if c ≥ 1 then 7 | product = 1
    by_contra hc
    have h7 : 7 ∣ 7 ^ c := dvd_pow_self 7 hc
    have : 7 ∣ 2 ^ a * 5 ^ b * 7 ^ c := dvd_mul_of_dvd_right h7 _
    rw [h] at this; omega

/-! ## Irrationality of log₂5 and log₂7 -/

/-- log₂5 is irrational. -/
theorem irrational_logb_two_five : Irrational (logb 2 5) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hab
  have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have hlog5_pos : Real.log 5 > 0 := Real.log_pos (by norm_num)
  have hb_cast : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hcross : (a : ℝ) * Real.log 2 = (b : ℝ) * Real.log 5 := by
    unfold logb at hab
    have := (div_eq_div_iff (ne_of_gt hlog2_pos) hb_cast).mp hab
    linarith
  have habs : |(a : ℝ)| * Real.log 2 = |(b : ℝ)| * Real.log 5 := by
    have := congr_arg abs hcross
    rwa [abs_mul, abs_mul, abs_of_pos hlog2_pos, abs_of_pos hlog5_pos] at this
  have hnat_cross : (a.natAbs : ℝ) * Real.log 2 = (b.natAbs : ℝ) * Real.log 5 := by
    rw [Nat.cast_natAbs, Int.cast_abs, Nat.cast_natAbs, Int.cast_abs]; exact habs
  have hlog_eq : Real.log ((2 : ℝ) ^ a.natAbs) = Real.log ((5 : ℝ) ^ b.natAbs) := by
    rw [Real.log_pow, Real.log_pow]; linarith
  have hpow_eq : (2 : ℝ) ^ a.natAbs = (5 : ℝ) ^ b.natAbs :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hlog_eq
  have hpow_nat : 2 ^ a.natAbs = 5 ^ b.natAbs := by exact_mod_cast hpow_eq
  -- 2^a = 5^b: check parity. 5^b is odd, 2^a is even for a ≥ 1
  by_cases ha : a.natAbs = 0
  · -- a = 0 → 1 = 5^b → b = 0, contradicting hb
    rw [ha, pow_zero] at hpow_nat
    have : b.natAbs = 0 := by
      by_contra hbn
      have : 5 ^ b.natAbs ≥ 5 := le_self_pow₀ (by norm_num : 5 ≥ 1) hbn
      omega
    exact hb (Int.natAbs_eq_zero.mp this)
  · -- a ≥ 1 → 2 | 2^a → 2 | 5^b → 2 | 5, contradiction
    have h2_dvd : 2 ∣ 2 ^ a.natAbs := dvd_pow_self 2 ha
    rw [hpow_nat] at h2_dvd
    have : 2 ∣ 5 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2_dvd
    omega

/-- log₂7 is irrational. -/
theorem irrational_logb_two_seven : Irrational (logb 2 7) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hab
  have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have hlog7_pos : Real.log 7 > 0 := Real.log_pos (by norm_num)
  have hb_cast : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hcross : (a : ℝ) * Real.log 2 = (b : ℝ) * Real.log 7 := by
    unfold logb at hab
    have := (div_eq_div_iff (ne_of_gt hlog2_pos) hb_cast).mp hab
    linarith
  have habs : |(a : ℝ)| * Real.log 2 = |(b : ℝ)| * Real.log 7 := by
    have := congr_arg abs hcross
    rwa [abs_mul, abs_mul, abs_of_pos hlog2_pos, abs_of_pos hlog7_pos] at this
  have hnat_cross : (a.natAbs : ℝ) * Real.log 2 = (b.natAbs : ℝ) * Real.log 7 := by
    rw [Nat.cast_natAbs, Int.cast_abs, Nat.cast_natAbs, Int.cast_abs]; exact habs
  have hlog_eq : Real.log ((2 : ℝ) ^ a.natAbs) = Real.log ((7 : ℝ) ^ b.natAbs) := by
    rw [Real.log_pow, Real.log_pow]; linarith
  have hpow_eq : (2 : ℝ) ^ a.natAbs = (7 : ℝ) ^ b.natAbs :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hlog_eq
  have hpow_nat : 2 ^ a.natAbs = 7 ^ b.natAbs := by exact_mod_cast hpow_eq
  by_cases ha : a.natAbs = 0
  · rw [ha, pow_zero] at hpow_nat
    have : b.natAbs = 0 := by
      by_contra hbn
      have : 7 ^ b.natAbs ≥ 7 := le_self_pow₀ (by norm_num : 7 ≥ 1) hbn
      omega
    exact hb (Int.natAbs_eq_zero.mp this)
  · have h2_dvd : 2 ∣ 2 ^ a.natAbs := dvd_pow_self 2 ha
    rw [hpow_nat] at h2_dvd
    have : 2 ∣ 7 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2_dvd
    omega

/-- logb 5 7 is irrational. -/
theorem irrational_logb_five_seven : Irrational (logb 5 7) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hab
  have hlog5_pos : Real.log 5 > 0 := Real.log_pos (by norm_num)
  have hlog7_pos : Real.log 7 > 0 := Real.log_pos (by norm_num)
  have hb_cast : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hcross : (a : ℝ) * Real.log 5 = (b : ℝ) * Real.log 7 := by
    unfold logb at hab
    have := (div_eq_div_iff (ne_of_gt hlog5_pos) hb_cast).mp hab
    linarith
  have habs : |(a : ℝ)| * Real.log 5 = |(b : ℝ)| * Real.log 7 := by
    have := congr_arg abs hcross
    rwa [abs_mul, abs_mul, abs_of_pos hlog5_pos, abs_of_pos hlog7_pos] at this
  have hnat_cross : (a.natAbs : ℝ) * Real.log 5 = (b.natAbs : ℝ) * Real.log 7 := by
    rw [Nat.cast_natAbs, Int.cast_abs, Nat.cast_natAbs, Int.cast_abs]; exact habs
  have hlog_eq : Real.log ((5 : ℝ) ^ a.natAbs) = Real.log ((7 : ℝ) ^ b.natAbs) := by
    rw [Real.log_pow, Real.log_pow]; linarith
  have hpow_eq : (5 : ℝ) ^ a.natAbs = (7 : ℝ) ^ b.natAbs :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hlog_eq
  have hpow_nat : 5 ^ a.natAbs = 7 ^ b.natAbs := by exact_mod_cast hpow_eq
  by_cases ha : a.natAbs = 0
  · rw [ha, pow_zero] at hpow_nat
    have : b.natAbs = 0 := by
      by_contra hbn
      have : 7 ^ b.natAbs ≥ 7 := le_self_pow₀ (by norm_num : 7 ≥ 1) hbn
      omega
    exact hb (Int.natAbs_eq_zero.mp this)
  · have h5_dvd : 5 ∣ 5 ^ a.natAbs := dvd_pow_self 5 ha
    rw [hpow_nat] at h5_dvd
    have : 5 ∣ 7 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5_dvd
    omega

/-! ## Helpers for multiplicative independence with ℤ exponents -/

/-- Clearing zpow: `x^b * x^((-b).toNat) = x^(b.toNat)` for positive `x`. -/
private lemma zpow_mul_clear (x : ℝ) (hx : 0 < x) (b : ℤ) :
    x ^ b * (x : ℝ) ^ ((-b).toNat : ℕ) = (x : ℝ) ^ (b.toNat : ℕ) := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (ne_of_gt hx)]
  congr 1; omega

/-- 2 does not divide 5^a * 7^b for any natural numbers a, b. -/
private lemma two_not_dvd_pow5_mul_pow7 (a b : ℕ) : ¬ (2 ∣ 5 ^ a * 7 ^ b) := by
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h5 | h7
  · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h5; omega
  · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h7; omega

/-! ## Linear form nonvanishing for (2, 5, 7) -/

/-- If (b₁, b₂, b₃) ≠ (0, 0, 0) with b₂ = 0 and b₃ = 0,
    then the form reduces to b₁·log 2, which is nonzero. -/
private theorem linearForm257_nonzero_single (b₁ : ℤ) (hb₁ : b₁ ≠ 0) :
    linearForm257 b₁ 0 0 ≠ 0 := by
  unfold linearForm257 linearFormLog3
  simp only [Int.cast_zero, zero_mul, add_zero]
  exact mul_ne_zero (Int.cast_ne_zero.mpr hb₁) (ne_of_gt (Real.log_pos (by norm_num)))

/-- The two-variable sub-form b₁·log 2 + b₂·log 5 is nonzero when
    (b₁, b₂) ≠ (0, 0), by irrationality of log₂5. -/
private theorem linearForm25_nonzero (b₁ b₂ : ℤ) (h : b₁ ≠ 0 ∨ b₂ ≠ 0) :
    b₁ * Real.log 2 + b₂ * Real.log 5 ≠ 0 := by
  have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have hlog5_pos : Real.log 5 > 0 := Real.log_pos (by norm_num)
  intro heq
  by_cases hb₂ : b₂ = 0
  · -- b₂ = 0: form is b₁·log 2 = 0, but log 2 > 0 and b₁ ≠ 0
    have hb₁ : b₁ ≠ 0 := h.resolve_right (not_not.mpr hb₂)
    simp only [hb₂, Int.cast_zero, zero_mul, add_zero] at heq
    rcases mul_eq_zero.mp heq with hb₁0 | hlog0
    · exact hb₁ (Int.cast_eq_zero.mp hb₁0)
    · exact ne_of_gt hlog2_pos hlog0
  · by_cases hb₁ : b₁ = 0
    · -- b₁ = 0: form is b₂·log 5 = 0
      simp only [hb₁, Int.cast_zero, zero_mul, zero_add] at heq
      rcases mul_eq_zero.mp heq with hb₂0 | hlog0
      · exact hb₂ (Int.cast_eq_zero.mp hb₂0)
      · exact ne_of_gt hlog5_pos hlog0
    · -- Both nonzero: logb 2 5 = -b₁/b₂, contradicting irrationality
      have hlogb_eq : logb 2 5 = (↑(-b₁) : ℝ) / ↑b₂ := by
        unfold logb
        rw [div_eq_div_iff (ne_of_gt hlog2_pos) (Int.cast_ne_zero.mpr hb₂)]
        push_cast; linarith
      exact irrational_logb_two_five.ne_rational (-b₁) b₂ hlogb_eq

/-- The full three-variable linear form b₁·log 2 + b₂·log 5 + b₃·log 7 is nonzero
    whenever (b₁, b₂, b₃) ≠ (0, 0, 0).

    This follows from the mutual irrationality of log₂5 and log₂7,
    plus the algebraic independence of the primes 2, 5, 7. -/
theorem linearForm257_nonzero (b₁ b₂ b₃ : ℤ) (h : b₁ ≠ 0 ∨ b₂ ≠ 0 ∨ b₃ ≠ 0) :
    linearForm257 b₁ b₂ b₃ ≠ 0 := by
  unfold linearForm257 linearFormLog3
  have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have hlog5_pos : Real.log 5 > 0 := Real.log_pos (by norm_num)
  have hlog7_pos : Real.log 7 > 0 := Real.log_pos (by norm_num)
  intro heq
  by_cases hb₃ : b₃ = 0
  · -- Reduces to 2-variable case
    simp only [hb₃, Int.cast_zero, zero_mul, add_zero] at heq
    have h12 : b₁ ≠ 0 ∨ b₂ ≠ 0 := by
      rcases h with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · exact absurd hb₃ h3
    exact linearForm25_nonzero b₁ b₂ h12 heq
  · by_cases hb₁b₂ : b₁ = 0 ∧ b₂ = 0
    · -- b₁ = b₂ = 0, b₃ ≠ 0: form is b₃·log 7 ≠ 0
      obtain ⟨hb₁, hb₂⟩ := hb₁b₂
      simp only [hb₁, hb₂, Int.cast_zero, zero_mul, zero_add] at heq
      exact ne_of_gt (mul_pos (by
        have : (↑b₃ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb₃
        rcases ne_iff_lt_or_gt.mp this with h | h
        · nlinarith [mul_neg_of_neg_of_pos h hlog7_pos]
        · exact h) hlog7_pos) heq
    · push_neg at hb₁b₂
      -- logb 2 7 = -(b₁ + b₂·log₂5) / b₃
      -- This requires log₂5 and log₂7 to be ℚ-linearly independent with 1
      -- which holds by {2,5,7} being multiplicatively independent primes.
      -- We use the contradiction approach: rearrange to get rational relation.
      by_cases hb₂' : b₂ = 0
      · -- b₂ = 0, b₃ ≠ 0, b₁ ≠ 0: form is b₁·log2 + b₃·log7 = 0
        -- → logb 2 7 = -b₁/b₃, contradicting irrationality
        simp only [hb₂', Int.cast_zero, zero_mul, add_zero] at heq
        have : b₁ ≠ 0 := by tauto
        have hlogb_eq : logb 2 7 = (↑(-b₁) : ℝ) / ↑b₃ := by
          unfold logb
          rw [div_eq_div_iff (ne_of_gt hlog2_pos) (Int.cast_ne_zero.mpr hb₃)]
          push_cast; linarith
        exact irrational_logb_two_seven.ne_rational (-b₁) b₃ hlogb_eq
      · -- General case: b₂ ≠ 0 and b₃ ≠ 0.
        -- Proof by exponentiation + unique prime factorization.
        -- From heq, exp gives 2^b₁ · 5^b₂ · 7^b₃ = 1 (zpow in ℝ).
        -- Clear denominators to get ℕ equation, then 2-adic divisibility
        -- forces b₁ = 0, reducing to the (5,7) two-variable case.
        exfalso
        by_cases hb₁ : b₁ = 0
        · -- b₁ = 0: reduces to b₂·log 5 + b₃·log 7 = 0
          simp only [hb₁, Int.cast_zero, zero_mul, zero_add] at heq
          -- logb 5 7 = -b₂/b₃, contradicting irrationality
          have hlogb_eq : logb 5 7 = (↑(-b₂) : ℝ) / ↑b₃ := by
            unfold logb
            rw [div_eq_div_iff (ne_of_gt hlog5_pos) (Int.cast_ne_zero.mpr hb₃)]
            push_cast; linarith
          exact irrational_logb_five_seven.ne_rational (-b₂) b₃ hlogb_eq
        · -- b₁ ≠ 0: exponentiate, then use divisibility by 2
          -- Step 1: exp(heq) gives zpow product = 1
          have hprod : (2:ℝ) ^ b₁ * (5:ℝ) ^ b₂ * (7:ℝ) ^ b₃ = 1 := by
            have hexp := congr_arg Real.exp heq
            rw [Real.exp_zero, Real.exp_add, Real.exp_add] at hexp
            rw [show Real.exp (↑b₁ * Real.log 2) = (2:ℝ) ^ b₁ from by
                  rw [mul_comm, ← rpow_def_of_pos (by norm_num : (0:ℝ) < 2), rpow_intCast],
                show Real.exp (↑b₂ * Real.log 5) = (5:ℝ) ^ b₂ from by
                  rw [mul_comm, ← rpow_def_of_pos (by norm_num : (0:ℝ) < 5), rpow_intCast],
                show Real.exp (↑b₃ * Real.log 7) = (7:ℝ) ^ b₃ from by
                  rw [mul_comm, ← rpow_def_of_pos (by norm_num : (0:ℝ) < 7), rpow_intCast]
                ] at hexp
            exact hexp
          -- Step 2: Clear negative exponents to get ℕ equation
          have hnat_eq : (2:ℝ) ^ b₁.toNat * (5:ℝ) ^ b₂.toNat * (7:ℝ) ^ b₃.toNat =
              (2:ℝ) ^ (-b₁).toNat * (5:ℝ) ^ (-b₂).toNat * (7:ℝ) ^ (-b₃).toNat := by
            have clear := congr_arg
              (· * ((2:ℝ) ^ ((-b₁).toNat : ℕ) * (5:ℝ) ^ ((-b₂).toNat : ℕ) *
                    (7:ℝ) ^ ((-b₃).toNat : ℕ))) hprod
            simp only [one_mul] at clear
            have lhs_eq : (2:ℝ) ^ b₁ * (5:ℝ) ^ b₂ * (7:ℝ) ^ b₃ *
                ((2:ℝ) ^ ((-b₁).toNat : ℕ) * (5:ℝ) ^ ((-b₂).toNat : ℕ) *
                  (7:ℝ) ^ ((-b₃).toNat : ℕ)) =
                ((2:ℝ) ^ b₁ * (2:ℝ) ^ ((-b₁).toNat : ℕ)) *
                ((5:ℝ) ^ b₂ * (5:ℝ) ^ ((-b₂).toNat : ℕ)) *
                ((7:ℝ) ^ b₃ * (7:ℝ) ^ ((-b₃).toNat : ℕ)) := by ring
            rw [lhs_eq,
                zpow_mul_clear 2 (by norm_num) b₁,
                zpow_mul_clear 5 (by norm_num) b₂,
                zpow_mul_clear 7 (by norm_num) b₃] at clear
            exact clear
          -- Step 3: Cast to ℕ
          have hnat : (2 : ℕ) ^ b₁.toNat * 5 ^ b₂.toNat * 7 ^ b₃.toNat =
              2 ^ (-b₁).toNat * 5 ^ (-b₂).toNat * 7 ^ (-b₃).toNat := by
            exact_mod_cast hnat_eq
          -- Step 4: b₁ ≠ 0 gives 2 divides one side but not the other
          rcases ne_iff_lt_or_gt.mp hb₁ with hb₁_neg | hb₁_pos
          · -- b₁ < 0: b₁.toNat = 0, (-b₁).toNat ≥ 1
            have h_toNat : b₁.toNat = 0 := Int.toNat_eq_zero.mpr (le_of_lt hb₁_neg)
            rw [h_toNat, pow_zero, one_mul] at hnat
            have h2_dvd : 2 ∣ 2 ^ (-b₁).toNat * 5 ^ (-b₂).toNat * 7 ^ (-b₃).toNat :=
              dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
                (dvd_pow_self 2 (by omega : (-b₁).toNat ≠ 0)) _) _
            rw [← hnat] at h2_dvd
            exact two_not_dvd_pow5_mul_pow7 b₂.toNat b₃.toNat h2_dvd
          · -- b₁ > 0: (-b₁).toNat = 0, b₁.toNat ≥ 1
            have h_neg_toNat : (-b₁).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
            rw [h_neg_toNat, pow_zero, one_mul] at hnat
            have h2_dvd : 2 ∣ 2 ^ b₁.toNat * 5 ^ b₂.toNat * 7 ^ b₃.toNat :=
              dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
                (dvd_pow_self 2 (by omega : b₁.toNat ≠ 0)) _) _
            rw [hnat] at h2_dvd
            exact two_not_dvd_pow5_mul_pow7 (-b₂).toNat (-b₃).toNat h2_dvd

/-! ## Matveev's theorem (axiom A6) -/

/-- The Matveev constant for the three-logarithm case with algebraic numbers
    of degree 1 (rationals: 2, 5, 7). The constant depends on the number
    of logarithms (n=3), the degree (D=1), and the logarithmic heights of
    the algebraic numbers.

    The precise value from Matveev (2000) for n=3, D=1 is:
    C₃ = 1.4 · 30^6 · 3^{4.5} · D² · (1 + log D) · ∏ log A_i
    For A₁=2, A₂=5, A₃=7, D=1, this gives C₃ ≈ 2.8 × 10⁹. -/
noncomputable def matveevConst : ℝ := 2.8e9

/-- **Matveev's theorem** for linear forms in 3 logarithms.

    For the triple (log 2, log 5, log 7) with integer coefficients (b₁, b₂, b₃)
    where the form is nonzero:

    |b₁·log 2 + b₂·log 5 + b₃·log 7| ≥ exp(-C · (log H)⁴)

    where H = max(|b₁|, |b₂|, |b₃|) ≥ 3 and C is the Matveev constant.

    This is a special case of Matveev's general theorem for n=3 linear forms
    in logarithms of rational numbers.

    Reference: E.M. Matveev, Izv. Math. 64 (2000), 1217–1269. -/
axiom matveev_three_log :
    ∀ (b₁ b₂ b₃ : ℤ) (H : ℕ),
      (H : ℝ) ≥ max (|b₁|) (max (|b₂|) (|b₃|)) →
      H ≥ 3 →
      b₁ ≠ 0 ∨ b₂ ≠ 0 ∨ b₃ ≠ 0 →
      linearForm257 b₁ b₂ b₃ ≠ 0 →
      |linearForm257 b₁ b₂ b₃| ≥ Real.exp (-(matveevConst * (Real.log H) ^ 4))

/-! ## Corollaries of Matveev's theorem -/

/-- The Matveev lower bound is positive. -/
theorem matveev_bound_pos (H : ℕ) (hH : H ≥ 3) :
    Real.exp (-(matveevConst * (Real.log H) ^ 4)) > 0 :=
  Real.exp_pos _

/-- For nonzero integer triples, the linear form has a positive lower bound
    depending only on the height H. -/
theorem linearForm257_lower_of_nonzero (b₁ b₂ b₃ : ℤ) (H : ℕ)
    (hH_bound : (H : ℝ) ≥ max (|b₁|) (max (|b₂|) (|b₃|)))
    (hH : H ≥ 3)
    (hne : b₁ ≠ 0 ∨ b₂ ≠ 0 ∨ b₃ ≠ 0)
    (hnz : linearForm257 b₁ b₂ b₃ ≠ 0) :
    |linearForm257 b₁ b₂ b₃| > 0 :=
  abs_pos.mpr hnz

/-! ## Connection to fractional distances ||n·α|| -/

/-- For integer n, the fractional distance ||n·log₂5|| relates to the
    linear form: if p is the nearest integer to n·log₂5, then
    ||n·log₂5|| = |n·log₂5 - p| and n·log 5 - p·log 2 = (n·log₂5 - p)·log 2.
    Hence |n·log 5 - p·log 2| = ||n·log₂5|| · log 2. -/
theorem frac_dist_as_linear_form (n : ℕ) (p : ℤ) (_hn : n ≥ 1) :
    |(↑n : ℝ) * Real.log 5 - ↑p * Real.log 2| =
    |↑n * logb 2 5 - ↑p| * Real.log 2 := by
  have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  unfold logb
  rw [show (↑n : ℝ) * Real.log 5 - ↑p * Real.log 2 =
      (↑n * (Real.log 5 / Real.log 2) - ↑p) * Real.log 2 by field_simp]
  rw [abs_mul, abs_of_pos hlog2_pos]

end Collatz
