/-
  CollatzLean/SFT.lean
  Core symbolic dynamics definitions: full shift, shift map,
  words, subword extraction, SFT membership, and the golden mean shift.
-/
import Mathlib.Tactic

namespace Collatz

/-! ## Full shift and shift map -/

/-- One-sided infinite sequences over alphabet A. -/
def FullShift (A : Type*) := ℕ → A

/-- The shift map: drop the first symbol. σ(x)(n) = x(n+1). -/
def shiftMap {A : Type*} (x : FullShift A) : FullShift A :=
  fun n => x (n + 1)

/-! ## Finite words and subword extraction -/

/-- A finite word of length k over alphabet A. -/
def Word (A : Type*) (k : ℕ) := Fin k → A

/-- Extract a subword of length k starting at position i. -/
def extractWord {A : Type*} (x : FullShift A) (i : ℕ) (k : ℕ) : Word A k :=
  fun j => x (i + j.val)

/-! ## Forbidden-word avoidance and SFT -/

/-- A sequence avoids a word w if w never appears as a subword. -/
def Avoids {A : Type*} [DecidableEq A] (x : FullShift A) {k : ℕ} (w : Word A k) : Prop :=
  ∀ i : ℕ, extractWord x i k ≠ w

/-- SFT membership: a sequence belongs to the SFT if it avoids all forbidden words. -/
def SFTMem {A : Type*} [DecidableEq A]
    (forbidden : List (Σ k, Word A k)) (x : FullShift A) : Prop :=
  ∀ p ∈ forbidden, Avoids x p.2

/-! ## Shift-invariance of SFTs -/

/-- The shift map preserves SFT membership. -/
theorem shiftMap_preserves_SFT {A : Type*} [DecidableEq A]
    (forbidden : List (Σ k, Word A k)) (x : FullShift A)
    (hx : SFTMem forbidden x) : SFTMem forbidden (shiftMap x) := by
  intro p hp i hcontra
  have := hx p hp (i + 1)
  apply this
  funext j
  have hj := congr_fun hcontra j
  simp only [extractWord, shiftMap] at hj ⊢
  rw [show i + 1 + ↑j = i + ↑j + 1 from by omega]
  exact hj

/-! ## Golden mean shift -/

/-- The golden mean shift: no two consecutive 1s.
    Defined directly as the no-consecutive-1s property. -/
def InGoldenMeanShift (x : FullShift (Fin 2)) : Prop :=
  ∀ i : ℕ, ¬(x i = 1 ∧ x (i + 1) = 1)

/-- The forbidden bigram "11" for the golden mean shift. -/
def goldenMeanForbidden : List (Σ k, Word (Fin 2) k) :=
  [⟨2, fun _ => 1⟩]

/-- InGoldenMeanShift is equivalent to avoiding the bigram "11". -/
theorem inGoldenMeanShift_iff (x : FullShift (Fin 2)) :
    InGoldenMeanShift x ↔ SFTMem goldenMeanForbidden x := by
  constructor
  · intro h p hp i hcontra
    simp only [goldenMeanForbidden, List.mem_singleton] at hp
    subst hp
    simp only at hcontra
    have h0 := congr_fun hcontra ⟨0, by omega⟩
    have h1 := congr_fun hcontra ⟨1, by omega⟩
    simp only [extractWord] at h0 h1
    exact h i ⟨h0, h1⟩
  · intro h i ⟨h0, h1⟩
    have := h ⟨2, fun _ => (1 : Fin 2)⟩ (List.mem_singleton.mpr rfl) i
    apply this
    funext ⟨j, hj⟩
    simp only [extractWord]
    interval_cases j <;> simpa

/-- The shift map preserves the golden mean shift. -/
theorem shiftMap_goldenMean (x : FullShift (Fin 2))
    (hx : InGoldenMeanShift x) : InGoldenMeanShift (shiftMap x) := by
  intro i ⟨h0, h1⟩
  exact hx (i + 1) ⟨h0, h1⟩

/-! ## Evaluation helpers -/

/-- Decidable membership for the golden mean shift (first n positions). -/
def checkGoldenMean (x : ℕ → Fin 2) (n : ℕ) : Bool :=
  (List.range n).all fun i => !(x i == 1 && x (i + 1) == 1)

#eval checkGoldenMean (fun i => if i % 2 = 0 then 1 else 0) 20  -- true: 1010...
#eval checkGoldenMean (fun _ => 1) 20  -- false: 1111...
#eval checkGoldenMean (fun _ => 0) 20  -- true: 0000...

end Collatz
