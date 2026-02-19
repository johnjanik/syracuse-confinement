/-
  CollatzLean/Basic.lean
  Foundational definitions for the Collatz conjecture:
  the Collatz map, iterated sequence, stopping time, and
  the conjecture statement, plus small verifications.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace Collatz

/-! ## The Collatz map -/

/-- The Collatz map on natural numbers.
    Even n ↦ n / 2, odd n ↦ 3n + 1, with 0 ↦ 0. -/
def collatz (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 2 = 0 then n / 2
  else 3 * n + 1

/-! ## Case-split lemmas -/

theorem collatz_zero : collatz 0 = 0 := by
  simp [collatz]

theorem collatz_even (n : ℕ) (hn : n ≠ 0) (he : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, hn, he]

theorem collatz_odd (n : ℕ) (hn : n ≠ 0) (ho : n % 2 = 1) : collatz n = 3 * n + 1 := by
  simp [collatz, hn]
  omega

/-! ## Iterated Collatz sequence -/

/-- The iterated Collatz sequence starting from n.
    `collatzSeq n 0 = n` and `collatzSeq n (t+1) = collatz (collatzSeq n t)`. -/
def collatzSeq (n : ℕ) : ℕ → ℕ
  | 0 => n
  | t + 1 => collatz (collatzSeq n t)

theorem collatzSeq_zero (n : ℕ) : collatzSeq n 0 = n := rfl

theorem collatzSeq_succ (n t : ℕ) : collatzSeq n (t + 1) = collatz (collatzSeq n t) := rfl

/-! ## Stopping time and the conjecture -/

/-- Whether the sequence starting at n reaches 1. -/
def collatzReaches (n : ℕ) : Prop := ∃ k, collatzSeq n k = 1

/-- The Collatz conjecture: every positive natural number eventually reaches 1. -/
def CollatzConjecture : Prop := ∀ n : ℕ, n ≥ 1 → collatzReaches n

/-! ## Positivity -/

theorem collatz_pos (n : ℕ) (hn : n ≥ 1) : collatz n ≥ 1 := by
  unfold collatz
  split_ifs with h1 h2 <;> omega

/-! ## Small verifications -/

theorem collatz_two : collatz 2 = 1 := by native_decide

theorem collatz_one : collatz 1 = 4 := by native_decide

/-- The 1 → 4 → 2 → 1 cycle takes 3 steps. -/
theorem collatz_cycle : collatzSeq 1 3 = 1 := by native_decide

/-- n = 2 reaches 1 in 1 step. -/
theorem reaches_two : collatzReaches 2 := ⟨1, by native_decide⟩

/-- n = 4 reaches 1 in 2 steps. -/
theorem reaches_four : collatzReaches 4 := ⟨2, by native_decide⟩

#eval collatzSeq 27 111   -- should output 1
#eval collatzSeq 2 1      -- should output 1
#eval collatzSeq 1 3      -- should output 1

#check @CollatzConjecture

end Collatz
