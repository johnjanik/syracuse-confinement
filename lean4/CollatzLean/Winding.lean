/-
  CollatzLean/Winding.lean
  ν₂ and ν₃ counters: the number of even/odd steps in the
  first t steps of the Collatz sequence, and the partition lemma.
-/
import CollatzLean.Parity
import Mathlib.Tactic

namespace Collatz

/-! ## Even/odd step counters -/

/-- Number of even steps among the first t steps of collatzSeq n. -/
def nu2 (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => nu2 n t + if isEvenStep n t then 1 else 0

/-- Number of odd steps among the first t steps of collatzSeq n. -/
def nu3 (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => nu3 n t + if isOddStep n t then 1 else 0

/-! ## Base cases -/

@[simp] theorem nu2_zero (n : ℕ) : nu2 n 0 = 0 := rfl
@[simp] theorem nu3_zero (n : ℕ) : nu3 n 0 = 0 := rfl

/-! ## Step increment rules -/

theorem nu2_step_even (n t : ℕ) (he : isEvenStep n t = true) :
    nu2 n (t + 1) = nu2 n t + 1 := by
  simp [nu2, he]

theorem nu2_step_odd (n t : ℕ) (ho : isOddStep n t = true) :
    nu2 n (t + 1) = nu2 n t := by
  simp only [nu2]
  have : isEvenStep n t = false := by
    simp only [isEvenStep, isOddStep] at *
    simp [decide_eq_true_eq] at *
    omega
  simp [this]

theorem nu3_step_odd (n t : ℕ) (ho : isOddStep n t = true) :
    nu3 n (t + 1) = nu3 n t + 1 := by
  simp [nu3, ho]

theorem nu3_step_even (n t : ℕ) (he : isEvenStep n t = true) :
    nu3 n (t + 1) = nu3 n t := by
  simp only [nu3]
  have : isOddStep n t = false := by
    simp only [isEvenStep, isOddStep] at *
    simp [decide_eq_true_eq] at *
    omega
  simp [this]

/-! ## Partition lemma -/

/-- The total number of even and odd steps sums to t. -/
theorem nu_partition (n t : ℕ) : nu2 n t + nu3 n t = t := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [nu2, nu3]
    by_cases he : isEvenStep n t
    · have ho : isOddStep n t = false := by
        simp only [isEvenStep, isOddStep] at *
        simp [decide_eq_true_eq] at *
        omega
      simp [he, ho]
      omega
    · have ho : isOddStep n t = true := by
        simp only [isEvenStep, isOddStep] at *
        simp [decide_eq_true_eq] at *
        omega
      simp [he, ho]
      omega

end Collatz
