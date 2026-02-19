/-
  CollatzLean/BranchLocus.lean
  Branch locus classification on the (ℤ/kℤ)² torus:
  cells are classified as branch (both even and odd visits),
  pure-even, or pure-odd. The tunnel is defined as branch ∪ pure-even.
-/
import CollatzLean.Torus
import Mathlib.Data.ZMod.Basic

set_option linter.style.nativeDecide false

namespace Collatz

/-! ## Prop versions of visit predicates -/

/-- Cell has an even visit: ∃ n ∈ [1,N], t ∈ [1,T] with even step landing at cell. -/
def hasEvenVisit (k : ℕ) [NeZero k] (cell : ZMod k × ZMod k) (N T : ℕ) : Prop :=
  ∃ n, 1 ≤ n ∧ n ≤ N ∧ ∃ t, 1 ≤ t ∧ t ≤ T ∧
    isEvenStep n t = true ∧ torusResidue k n t = cell

/-- Cell has an odd visit: ∃ n ∈ [1,N], t ∈ [1,T] with odd step landing at cell. -/
def hasOddVisit (k : ℕ) [NeZero k] (cell : ZMod k × ZMod k) (N T : ℕ) : Prop :=
  ∃ n, 1 ≤ n ∧ n ≤ N ∧ ∃ t, 1 ≤ t ∧ t ≤ T ∧
    isOddStep n t = true ∧ torusResidue k n t = cell

/-- A branch cell has both even and odd visits. -/
def isBranchCell (k : ℕ) [NeZero k] (cell : ZMod k × ZMod k) (N T : ℕ) : Prop :=
  hasEvenVisit k cell N T ∧ hasOddVisit k cell N T

/-- A pure-even cell has even visits but no odd visits. -/
def isPureEven (k : ℕ) [NeZero k] (cell : ZMod k × ZMod k) (N T : ℕ) : Prop :=
  hasEvenVisit k cell N T ∧ ¬hasOddVisit k cell N T

/-- A pure-odd cell has odd visits but no even visits. -/
def isPureOdd (k : ℕ) [NeZero k] (cell : ZMod k × ZMod k) (N T : ℕ) : Prop :=
  hasOddVisit k cell N T ∧ ¬hasEvenVisit k cell N T

/-- The tunnel: the set of cells that are branch or pure-even. -/
def tunnel (k : ℕ) [NeZero k] (N T : ℕ) : Set (ZMod k × ZMod k) :=
  { cell | isBranchCell k cell N T ∨ isPureEven k cell N T }

/-! ## Cell trichotomy -/

/-- Every visited cell is exactly one of: branch, pure-even, or pure-odd.
    Unvisited cells are none of the three. -/
theorem cell_trichotomy (k : ℕ) [NeZero k] (cell : ZMod k × ZMod k) (N T : ℕ) :
    (isBranchCell k cell N T ∨ isPureEven k cell N T ∨ isPureOdd k cell N T) ∨
    (¬hasEvenVisit k cell N T ∧ ¬hasOddVisit k cell N T) := by
  by_cases he : hasEvenVisit k cell N T <;> by_cases ho : hasOddVisit k cell N T
  · left; left; exact ⟨he, ho⟩
  · left; right; left; exact ⟨he, ho⟩
  · left; right; right; exact ⟨ho, he⟩
  · right; exact ⟨he, ho⟩

/-- At a pure-even cell, every visit that lands there is an even step. -/
theorem pureEven_forces_even (k : ℕ) [NeZero k] (cell : ZMod k × ZMod k) (N T : ℕ)
    (hpe : isPureEven k cell N T)
    (n t : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ N) (ht1 : 1 ≤ t) (ht2 : t ≤ T)
    (hcell : torusResidue k n t = cell) :
    isEvenStep n t = true := by
  by_contra h
  push_neg at h
  have hodd : isOddStep n t = true := by
    simp only [isEvenStep, isOddStep] at *
    simp [decide_eq_true_eq] at *
    omega
  exact hpe.2 ⟨n, hn1, hn2, t, ht1, ht2, hodd, hcell⟩

/-! ## Computable (Bool) versions -/

/-- Decidable check: does cell have an even visit from n ∈ [1,N], t ∈ [1,T]? -/
def hasEvenVisitBool (k : ℕ) [NeZero k] [DecidableEq (ZMod k)]
    (cell : ZMod k × ZMod k) (N T : ℕ) : Bool :=
  (List.range N).any fun n =>
    (List.range T).any fun t =>
      isEvenStep (n + 1) (t + 1) && (torusResidue k (n + 1) (t + 1) == cell)

/-- Decidable check: does cell have an odd visit from n ∈ [1,N], t ∈ [1,T]? -/
def hasOddVisitBool (k : ℕ) [NeZero k] [DecidableEq (ZMod k)]
    (cell : ZMod k × ZMod k) (N T : ℕ) : Bool :=
  (List.range N).any fun n =>
    (List.range T).any fun t =>
      isOddStep (n + 1) (t + 1) && (torusResidue k (n + 1) (t + 1) == cell)

/-- Decidable check: is cell a branch cell? -/
def isBranchCellBool (k : ℕ) [NeZero k] [DecidableEq (ZMod k)]
    (cell : ZMod k × ZMod k) (N T : ℕ) : Bool :=
  hasEvenVisitBool k cell N T && hasOddVisitBool k cell N T

/-- Decidable check: is cell pure-even? -/
def isPureEvenBool (k : ℕ) [NeZero k] [DecidableEq (ZMod k)]
    (cell : ZMod k × ZMod k) (N T : ℕ) : Bool :=
  hasEvenVisitBool k cell N T && !hasOddVisitBool k cell N T

/-! ## Counting functions -/

/-- Count of branch cells on the k×k torus. -/
def branchCount (k : ℕ) [NeZero k] [DecidableEq (ZMod k)] (N T : ℕ) : ℕ :=
  (Finset.univ.filter fun cell : ZMod k × ZMod k => isBranchCellBool k cell N T).card

/-- Count of pure-even cells on the k×k torus. -/
def pureEvenCount (k : ℕ) [NeZero k] [DecidableEq (ZMod k)] (N T : ℕ) : ℕ :=
  (Finset.univ.filter fun cell : ZMod k × ZMod k => isPureEvenBool k cell N T).card

/-! ## Verified computations -/

/-- Branch count at k=12: 43 of 144 cells are branch cells. -/
theorem branch_count_12 :
    branchCount 12 10 50 = 43 := by native_decide

/-- Pure-even cells exist at k=12, showing the tunnel has walls. -/
theorem pureEven_walls_exist :
    pureEvenCount 12 10 50 > 0 := by native_decide

/-! ## Evaluation -/

#eval branchCount 6 50 200
#eval pureEvenCount 6 50 200

end Collatz
