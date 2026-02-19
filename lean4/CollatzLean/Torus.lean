/-
  CollatzLean/Torus.lean
  ZMod torus residues: mapping (ν₂, ν₃) into ZMod k × ZMod k
  and proving the advance rules for even/odd steps.
-/
import CollatzLean.Winding
import Mathlib.Data.ZMod.Basic

namespace Collatz

/-! ## Torus residue -/

/-- The torus residue of the winding numbers modulo k. -/
def torusResidue (k : ℕ) (n t : ℕ) : ZMod k × ZMod k :=
  ((nu2 n t : ZMod k), (nu3 n t : ZMod k))

/-! ## Advance rules -/

theorem torus_advance_even (k : ℕ) (n t : ℕ) (he : isEvenStep n t = true) :
    torusResidue k n (t + 1) =
      ((torusResidue k n t).1 + 1, (torusResidue k n t).2) := by
  unfold torusResidue
  rw [nu2_step_even n t he, nu3_step_even n t he]
  congr 1
  push_cast
  ring

theorem torus_advance_odd (k : ℕ) (n t : ℕ) (ho : isOddStep n t = true) :
    torusResidue k n (t + 1) =
      ((torusResidue k n t).1, (torusResidue k n t).2 + 1) := by
  unfold torusResidue
  rw [nu2_step_odd n t ho, nu3_step_odd n t ho]
  congr 1
  push_cast
  ring

end Collatz
