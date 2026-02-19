/-
  CollatzLean/Parity.lean
  The "11" constraint: 3n+1 is always even when n is odd,
  so two consecutive odd steps are impossible.
-/
import CollatzLean.Basic
import Mathlib.Tactic

namespace Collatz

/-! ## Parity helpers -/

/-- Whether the Collatz sequence value at step t is even. -/
def isEvenStep (n t : ℕ) : Bool := collatzSeq n t % 2 = 0

/-- Whether the Collatz sequence value at step t is odd. -/
def isOddStep (n t : ℕ) : Bool := collatzSeq n t % 2 = 1

/-- Parity bit: 0 for even, 1 for odd. -/
def parityBit (n t : ℕ) : Fin 2 :=
  if collatzSeq n t % 2 = 0 then 0 else 1

/-! ## Core arithmetic fact -/

/-- 3m + 1 is even whenever m is odd. -/
theorem odd_step_produces_even (m : ℕ) (hm : m % 2 = 1) : (3 * m + 1) % 2 = 0 := by
  omega

/-! ## Collatz-specific parity results -/

/-- Applying collatz to a nonzero odd number yields an even number. -/
theorem collatz_odd_result_even (n : ℕ) (hn : n ≠ 0) (ho : n % 2 = 1) :
    (collatz n) % 2 = 0 := by
  rw [collatz_odd n hn ho]
  omega

/-- The "11" constraint: if step t is odd (and nonzero), step t+1 is even. -/
theorem no_consecutive_odd_steps (n t : ℕ)
    (hn : collatzSeq n t ≠ 0)
    (hodd : isOddStep n t = true) :
    isOddStep n (t + 1) = false := by
  have h1 : collatzSeq n t % 2 = 1 := by
    simp only [isOddStep] at hodd
    exact of_decide_eq_true hodd
  have h2 : (collatz (collatzSeq n t)) % 2 = 0 :=
    collatz_odd_result_even _ hn h1
  change isOddStep n (t + 1) = false
  simp only [isOddStep, collatzSeq_succ]
  exact decide_eq_false (by omega)

end Collatz
