/-
  CollatzLean/StructuralPureEven.lean
  Structural (universal) version of pure-even cells:
  a cell is structural pure-even if every trajectory visiting it
  takes an even step, for ALL n,t — not just a bounded range.
  This is the foundation for the Baker-Feldman bridge (Definition 7.4).
-/
import CollatzLean.BranchLocus

namespace Collatz

/-! ## Structural definitions -/

/-- A cell is structural pure-even if every trajectory that visits it does so
    at an even step. Universal (N/T-free) version of `isPureEven`.
    Corresponds to Definition 7.4 in the manuscript. -/
def isStructuralPureEven (k : ℕ) [NeZero k] (cell : ZMod k × ZMod k) : Prop :=
  ∀ n, n ≥ 1 → ∀ t, t ≥ 1 → torusResidue k n t = cell → isEvenStep n t = true

/-- A cell forces double halving if every odd-step visit has value ≡ 1 (mod 4),
    guaranteeing two subsequent even steps. -/
def forcesDoubleHalving (k : ℕ) [NeZero k] (cell : ZMod k × ZMod k) : Prop :=
  ∀ n, n ≥ 1 → ∀ t, t ≥ 1 → torusResidue k n t = cell →
    isOddStep n t = true → collatzSeq n t % 4 = 1

/-- The structural sieve S_k: the set of structural pure-even cells (Lemma 7.5). -/
def structuralSieve (k : ℕ) [NeZero k] : Set (ZMod k × ZMod k) :=
  { cell | isStructuralPureEven k cell }

/-! ## Theorems connecting structural and empirical definitions -/

/-- A structural pure-even cell has no odd visits for any bounded range. -/
theorem structural_implies_no_odd_visit (k : ℕ) [NeZero k]
    (cell : ZMod k × ZMod k) (N T : ℕ)
    (hstr : isStructuralPureEven k cell) :
    ¬hasOddVisit k cell N T := by
  intro ⟨n, hn1, _, t, ht1, _, hodd, hcell⟩
  have heven := hstr n hn1 t ht1 hcell
  simp only [isEvenStep, isOddStep] at heven hodd
  simp [decide_eq_true_eq] at heven hodd
  omega

/-- Structural pure-even + at least one even visit → empirical pure-even. -/
theorem structural_and_visited_implies_empirical (k : ℕ) [NeZero k]
    (cell : ZMod k × ZMod k) (N T : ℕ)
    (hstr : isStructuralPureEven k cell)
    (hvisit : hasEvenVisit k cell N T) :
    isPureEven k cell N T :=
  ⟨hvisit, structural_implies_no_odd_visit k cell N T hstr⟩

/-! ## Arithmetic lemmas for double halving -/

/-- If m ≡ 1 (mod 4), then 3m+1 ≡ 0 (mod 4). -/
theorem mod4_one_double_halving (m : ℕ) (hm : m % 4 = 1) : (3 * m + 1) % 4 = 0 := by
  omega

/-- Structural pure-even implies forces double halving (vacuously:
    no odd visits means the premise is never satisfied). -/
theorem structural_implies_forces_double_halving (k : ℕ) [NeZero k]
    (cell : ZMod k × ZMod k)
    (hstr : isStructuralPureEven k cell) :
    forcesDoubleHalving k cell := by
  intro n hn t ht hcell hodd
  have heven := hstr n hn t ht hcell
  simp only [isEvenStep, isOddStep] at heven hodd
  simp [decide_eq_true_eq] at heven hodd
  omega

/-- If collatzSeq n t is odd, nonzero, and ≡ 1 (mod 4),
    then steps t+1 and t+2 are both even. -/
theorem double_halving_two_even_steps (n t : ℕ)
    (hnonzero : collatzSeq n t ≠ 0)
    (hodd : collatzSeq n t % 2 = 1)
    (hmod4 : collatzSeq n t % 4 = 1) :
    isEvenStep n (t + 1) = true ∧ isEvenStep n (t + 2) = true := by
  -- Step t+1: collatz maps odd a to 3a+1 which is even
  have h1 : collatzSeq n (t + 1) = 3 * collatzSeq n t + 1 := by
    rw [collatzSeq_succ, collatz_odd _ hnonzero hodd]
  have h1_even : collatzSeq n (t + 1) % 2 = 0 := by omega
  have h1_ne : collatzSeq n (t + 1) ≠ 0 := by omega
  -- Step t+2: collatz halves the even value; result is even since a ≡ 1 (mod 4)
  have h2 : collatzSeq n (t + 2) = collatzSeq n (t + 1) / 2 := by
    change collatz (collatzSeq n (t + 1)) = _
    exact collatz_even _ h1_ne h1_even
  constructor
  · simp only [isEvenStep, h1, decide_eq_true_eq]; omega
  · simp only [isEvenStep, h2, h1, decide_eq_true_eq]; omega

end Collatz
