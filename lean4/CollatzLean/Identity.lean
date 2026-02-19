/-
  CollatzLean/Identity.lean
  The cleared multiplicative identity connecting winding numbers
  to Collatz sequence values:
    collatzSeq n t * 2^(nu2 n t) = n * 3^(nu3 n t) + correction n t
-/
import CollatzLean.Winding

namespace Collatz

/-! ## Correction term -/

/-- The correction term accumulating the "+1" from each 3n+1 step,
    cleared of denominators. -/
def correction (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
    if isEvenStep n t then correction n t
    else 3 * correction n t + 2 ^ nu2 n t

/-! ## Helper lemmas -/

/-- collatz m = m / 2 when m is even (including m = 0). -/
theorem collatz_even_general (m : ℕ) (he : m % 2 = 0) : collatz m = m / 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [collatz]
  · exact collatz_even m (by omega) he

/-- Every step is either even or odd. -/
theorem even_or_odd_step (n t : ℕ) : isEvenStep n t = true ∨ isOddStep n t = true := by
  simp only [isEvenStep, isOddStep, decide_eq_true_eq]
  omega

/-- Division by 2 then multiplication by 2 recovers an even number. -/
theorem div_two_mul_two (m : ℕ) (he : m % 2 = 0) : m / 2 * 2 = m :=
  Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero he)

/-! ## Correction step lemmas -/

@[simp] theorem correction_zero (n : ℕ) : correction n 0 = 0 := rfl

theorem correction_succ_even (n t : ℕ) (he : isEvenStep n t = true) :
    correction n (t + 1) = correction n t := by
  simp only [correction]
  simp [he]

theorem correction_succ_odd (n t : ℕ) (ho : isOddStep n t = true) :
    correction n (t + 1) = 3 * correction n t + 2 ^ nu2 n t := by
  have hne : isEvenStep n t = false := by
    simp only [isEvenStep, isOddStep] at *
    simp [decide_eq_true_eq] at *
    omega
  simp only [correction]
  simp [hne]

/-! ## Main identity -/

/-- The cleared multiplicative identity for the Collatz sequence. -/
theorem collatz_identity (n t : ℕ) :
    collatzSeq n t * 2 ^ nu2 n t = n * 3 ^ nu3 n t + correction n t := by
  induction t with
  | zero => simp [collatzSeq]
  | succ t ih =>
    rcases even_or_odd_step n t with he | ho
    · -- Even step: collatzSeq n (t+1) = collatzSeq n t / 2
      have hmod : collatzSeq n t % 2 = 0 := by
        simp only [isEvenStep, decide_eq_true_eq] at he; exact he
      rw [collatzSeq_succ, collatz_even_general _ hmod,
          nu2_step_even n t he, nu3_step_even n t he,
          correction_succ_even n t he, pow_succ]
      have h : collatzSeq n t / 2 * (2 ^ nu2 n t * 2)
             = collatzSeq n t / 2 * 2 * 2 ^ nu2 n t := by ring
      rw [h, div_two_mul_two _ hmod, ih]
    · -- Odd step: collatzSeq n (t+1) = 3 * collatzSeq n t + 1
      have hmod : collatzSeq n t % 2 = 1 := by
        simp only [isOddStep, decide_eq_true_eq] at ho; exact ho
      have hne : collatzSeq n t ≠ 0 := by omega
      rw [collatzSeq_succ, collatz_odd _ hne hmod,
          nu2_step_odd n t ho, nu3_step_odd n t ho,
          correction_succ_odd n t ho, pow_succ]
      have hlhs : (3 * collatzSeq n t + 1) * 2 ^ nu2 n t
                = 3 * (collatzSeq n t * 2 ^ nu2 n t) + 2 ^ nu2 n t := by ring
      have hrhs : n * (3 ^ nu3 n t * 3) + (3 * correction n t + 2 ^ nu2 n t)
                = 3 * (n * 3 ^ nu3 n t + correction n t) + 2 ^ nu2 n t := by ring
      rw [hlhs, hrhs, ih]

/-! ## Verification -/

-- Verify identity for n=7 at t=17
#eval collatzSeq 7 17 * 2 ^ nu2 7 17 == 7 * 3 ^ nu3 7 17 + correction 7 17

-- Verify identity for n=27 at t=111
#eval collatzSeq 27 111 * 2 ^ nu2 27 111 == 27 * 3 ^ nu3 27 111 + correction 27 111

end Collatz
