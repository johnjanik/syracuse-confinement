/-
  CollatzLean/CollatzSFT.lean
  Connect the Collatz parity sequence to the golden mean shift:
  the parity sequence of any Collatz orbit starting from n ≥ 1
  lies in the golden mean shift (no two consecutive 1s / odd steps).
-/
import CollatzLean.SFT
import CollatzLean.Parity

namespace Collatz

/-! ## Parity sequence as a full shift element -/

/-- The parity sequence of the Collatz orbit starting from n,
    viewed as an element of FullShift (Fin 2). -/
def collatzParitySeq (n : ℕ) : FullShift (Fin 2) :=
  fun t => parityBit n t

/-! ## Positivity of Collatz iterates -/

/-- Every iterate of the Collatz sequence starting from n ≥ 1 remains ≥ 1. -/
theorem collatzSeq_pos (n : ℕ) (hn : n ≥ 1) (t : ℕ) : collatzSeq n t ≥ 1 := by
  induction t with
  | zero => simp [collatzSeq]; omega
  | succ t ih =>
    rw [collatzSeq_succ]
    exact collatz_pos (collatzSeq n t) ih

/-! ## Main theorem: Collatz parity lies in golden mean shift -/

/-- The parity sequence of any Collatz orbit starting from n ≥ 1
    lies in the golden mean shift (no two consecutive odd steps). -/
theorem collatzParitySeq_in_goldenMean (n : ℕ) (hn : n ≥ 1) :
    InGoldenMeanShift (collatzParitySeq n) := by
  intro i ⟨h0, h1⟩
  -- h0 : collatzParitySeq n i = 1, h1 : collatzParitySeq n (i + 1) = 1
  -- This means parityBit n i = 1 and parityBit n (i + 1) = 1
  -- parityBit = 1 means isOddStep = true
  have hodd_i : isOddStep n i = true := by
    simp only [collatzParitySeq, parityBit] at h0
    simp only [isOddStep]
    split_ifs at h0 with h
    · exact absurd h0 (by decide)
    · simp [decide_eq_true_eq]
      omega
  have hpos_i : collatzSeq n i ≠ 0 := by
    have := collatzSeq_pos n hn i; omega
  have := no_consecutive_odd_steps n i hpos_i hodd_i
  -- this : isOddStep n (i + 1) = false
  -- But h1 says parityBit n (i + 1) = 1, which means isOddStep n (i + 1) = true
  have hodd_i1 : isOddStep n (i + 1) = true := by
    simp only [collatzParitySeq, parityBit] at h1
    simp only [isOddStep]
    split_ifs at h1 with h
    · exact absurd h1 (by decide)
    · simp [decide_eq_true_eq]
      omega
  exact absurd hodd_i1 (by rw [this]; decide)

/-! ## Evaluation -/

-- Check parity sequence for n=7: should be in golden mean shift
#eval (List.range 20).map (fun t => (collatzParitySeq 7 t).val)
-- Check parity sequence for n=27
#eval (List.range 20).map (fun t => (collatzParitySeq 27 t).val)

end Collatz
