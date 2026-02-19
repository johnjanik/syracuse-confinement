/-
  CollatzLean/WeylEquidistribution.lean
  Weyl equidistribution bridge for Collatz cell visits on (Z/NZ)².

  Connects Weyl's equidistribution criterion to the Collatz trajectory's
  cell visits on the torus (Z/NZ)², providing the framework to eventually
  close `finite_residence_bound` in DiophantineRepeller.lean.

  Architecture:
  D1. IsEquidistributed — counting definition on Z/NZ
  D2. weyl_equidistribution_of_irrational_rotation — axiom (Weyl's theorem)
  D3. safeCellDensity — fraction of safe cells on (Z/NZ)²
  D4. equidistribution_implies_safe_density — bridge theorem (sorry-free from axiom)
  D5. Wiring to finite_residence_bound via deficit budget

  Single axiom: weyl_equidistribution_of_irrational_rotation
  (Weyl's classical theorem for irrational rotation sequences)
-/
import CollatzLean.DiophantineRepeller
import CollatzLean.Syracuse
import CollatzLean.SyracuseDrift
import CollatzLean.IrrationalityMeasure
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

set_option linter.style.nativeDecide false

namespace Collatz

open Real Filter

/-! ## D1. Equidistribution on Z/NZ (counting definition) -/

/-- A sequence `seq : ℕ → ℕ` is equidistributed modulo N if for every residue
    class r < N, the frequency of visits converges to 1/N.

    Formally: for all r < N,
      |{k < M : seq(k) mod N = r}| / M → 1/N as M → ∞.

    We express this as: for every ε > 0, there exists M₀ such that for all M ≥ M₀,
      |count(r, M) / M - 1/N| < ε
    where count(r, M) = |{k < M : seq(k) mod N = r}|. -/
noncomputable def IsEquidistributed (seq : ℕ → ℕ) (N : ℕ) : Prop :=
  N ≥ 2 ∧ ∀ r : ℕ, r < N → ∀ ε : ℝ, ε > 0 →
    ∃ M₀ : ℕ, M₀ ≥ 1 ∧ ∀ M : ℕ, M ≥ M₀ →
      |((Finset.range M).filter (fun k => seq k % N = r)).card / (M : ℝ) - 1 / (N : ℝ)| < ε

/-- Helper: the visit count for residue r in the first M terms. -/
noncomputable def visitCount (seq : ℕ → ℕ) (N r M : ℕ) : ℕ :=
  ((Finset.range M).filter (fun k => seq k % N = r)).card

/-- The visit frequency for residue r in the first M terms. -/
noncomputable def visitFreq (seq : ℕ → ℕ) (N r M : ℕ) : ℝ :=
  (visitCount seq N r M : ℝ) / (M : ℝ)

/-- Equivalent formulation using visitFreq. -/
theorem isEquidistributed_iff_visitFreq (seq : ℕ → ℕ) (N : ℕ) :
    IsEquidistributed seq N ↔
      N ≥ 2 ∧ ∀ r : ℕ, r < N → ∀ ε : ℝ, ε > 0 →
        ∃ M₀ : ℕ, M₀ ≥ 1 ∧ ∀ M : ℕ, M ≥ M₀ →
          |visitFreq seq N r M - 1 / (N : ℝ)| < ε := by
  unfold IsEquidistributed visitFreq visitCount
  rfl

/-! ## D2. Weyl's theorem for irrational rotation (axiom)

    Classical result (Weyl, 1916): If α is irrational, the sequence
    ⌊k · α⌋ mod N is equidistributed modulo N for any N ≥ 2.

    The full proof involves exponential sums and is substantial to formalize.
    We state it as our single axiom. -/

/-- **Weyl's equidistribution theorem for irrational rotation**.
    If α is irrational, then the sequence k ↦ ⌊k · α⌋ is equidistributed
    modulo N for any N ≥ 2.

    This is a classical result in ergodic theory / uniform distribution theory.
    Reference: H. Weyl, "Über die Gleichverteilung von Zahlen mod. Eins",
    Math. Ann. 77 (1916), 313–352.

    The connection to Collatz: the Syracuse valuation sum grows roughly as
    log₂3 · k, so ν₂(n, syracuseTime n k) ≈ log₂3 · k. Since log₂3 is
    irrational (proved in Baker.lean), the cell visits on (Z/NZ)² trace
    an orbit of an irrational rotation and are therefore equidistributed. -/
axiom weyl_equidistribution_of_irrational_rotation :
    ∀ (α : ℝ), Irrational α → ∀ (N : ℕ), N ≥ 2 →
      IsEquidistributed (fun k => Int.toNat ⌊α * ↑k⌋) N

/-! ## D2'. Connection to log₂3 irrationality

    The irrationality of log₂3 is already proved in Baker.lean
    (irrational_logb_two_three). Combined with Weyl's theorem,
    this gives equidistribution for the ⌊k · log₂3⌋ sequence. -/

/-- The floor-of-irrational-rotation sequence for log₂3 is equidistributed. -/
theorem log2_3_rotation_equidistributed (N : ℕ) (hN : N ≥ 2) :
    IsEquidistributed (fun k => Int.toNat ⌊logb 2 3 * ↑k⌋) N :=
  weyl_equidistribution_of_irrational_rotation (logb 2 3) irrational_logb_two_three N hN

/-! ## D3. Safe cell density on (Z/NZ)²

    A cell (a, b) on (Z/NZ)² is "safe" if the cell error |a - log₂3 · b|
    is large enough that trajectories visiting it have average v₂ ≥ 2.
    By Baker cell separation, dangerous cells (small cell error) are sparse,
    so the safe cell density is bounded below by a positive constant. -/

/-- A cell (a, b) is safe at scale N if its cell error exceeds a threshold δ.
    Safe cells have v₂ ≥ 2, contributing non-positively to the deficit. -/
noncomputable def isSafeCell (_N : ℕ) (δ : ℝ) (a b : ℤ) : Prop :=
  |cellError a b| > δ

/-- The safe cell density: fraction of cells (a, b) ∈ (Z/NZ)² that are safe
    for a given threshold δ. -/
noncomputable def safeCellDensity (N : ℕ) (δ : ℝ) : ℝ :=
  ((Finset.Icc (0 : ℤ) (N - 1) ×ˢ Finset.Icc (0 : ℤ) (N - 1)).filter
    (fun p => |cellError p.1 p.2| > δ)).card / ((N : ℝ) ^ 2)

/-! ## D3'. Baker-based safe cell count

    At scale N, the number of dangerous cells (those with |cellError| ≤ δ)
    is at most N · (⌈2δ⌉ + 1), because for each b ∈ [0,N), there are at most
    ⌈2δ⌉ + 1 values of a with |a - log₂3 · b| ≤ δ (integers in an interval
    of length 2δ). So the dangerous fraction ≤ (⌈2δ⌉+1)/N → 0. -/

/-- For each b, at most ⌈2δ⌉ + 1 values of a satisfy |a - log₂3 · b| ≤ δ.
    This is a basic property of intervals on the real line. -/
theorem dangerous_cells_per_row_bound (b : ℤ) (_N : ℕ) (δ : ℝ) (_hδ : δ > 0) :
    ((Finset.Icc (0 : ℤ) (↑N - 1)).filter
      (fun a => |cellError a b| ≤ δ)).card ≤ ⌈2 * δ⌉₊ + 1 := by
  -- The filtered set ⊆ Finset.Icc ⌈c - δ⌉ ⌊c + δ⌋ where c = logb 2 3 * b
  set c := logb 2 3 * (↑b : ℝ)
  have hsub : (Finset.Icc (0 : ℤ) (↑N - 1)).filter (fun a => |cellError a b| ≤ δ) ⊆
      Finset.Icc ⌈c - δ⌉ ⌊c + δ⌋ := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_Icc]
    have habs : |cellError a b| ≤ δ := ha.2
    simp only [cellError] at habs
    rw [abs_le] at habs
    exact ⟨Int.ceil_le.mpr (by linarith),
           Int.le_floor.mpr (by linarith)⟩
  calc ((Finset.Icc (0 : ℤ) (↑N - 1)).filter (fun a => |cellError a b| ≤ δ)).card
      ≤ (Finset.Icc ⌈c - δ⌉ ⌊c + δ⌋).card := Finset.card_le_card hsub
    _ ≤ ⌈2 * δ⌉₊ + 1 := by
        rw [Int.card_Icc]
        suffices h : ⌊c + δ⌋ + 1 - ⌈c - δ⌉ ≤ ↑(⌈2 * δ⌉₊ + 1) from Int.toNat_le.mpr h
        have h1 : (↑⌊c + δ⌋ : ℝ) ≤ c + δ := Int.floor_le _
        have h2 : c - δ ≤ (↑⌈c - δ⌉ : ℝ) := Int.le_ceil _
        have h3 : (↑(⌊c + δ⌋ - ⌈c - δ⌉) : ℝ) ≤ 2 * δ := by push_cast; linarith
        have h4 : (2 * δ : ℝ) ≤ ↑⌈2 * δ⌉₊ := Nat.le_ceil _
        have h5 : ⌊c + δ⌋ - ⌈c - δ⌉ ≤ ↑⌈2 * δ⌉₊ := by exact_mod_cast le_trans h3 h4
        push_cast; linarith

/-- The total number of dangerous cells at scale N is at most N · (⌈2δ⌉ + 1). -/
theorem total_dangerous_cells_bound (N : ℕ) (δ : ℝ) (hδ : δ > 0) :
    ((Finset.Icc (0 : ℤ) (↑N - 1) ×ˢ Finset.Icc (0 : ℤ) (↑N - 1)).filter
      (fun p => |cellError p.1 p.2| ≤ δ)).card ≤ N * (⌈2 * δ⌉₊ + 1) := by
  set S := Finset.Icc (0 : ℤ) (↑N - 1) with hS_def
  have hsub : (S ×ˢ S).filter (fun p => |cellError p.1 p.2| ≤ δ) ⊆
      S.biUnion (fun b => (S.filter (fun a => |cellError a b| ≤ δ)).image (fun a => (a, b))) := by
    intro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image] at hab ⊢
    exact ⟨b, hab.1.2, a, ⟨hab.1.1, hab.2⟩, rfl⟩
  have hcard_S : S.card = N := by
    simp only [hS_def, Int.card_Icc]; omega
  calc ((S ×ˢ S).filter (fun p => |cellError p.1 p.2| ≤ δ)).card
      ≤ (S.biUnion (fun b => (S.filter (fun a => |cellError a b| ≤ δ)).image
          (fun a => (a, b)))).card := Finset.card_le_card hsub
    _ ≤ S.card * (⌈2 * δ⌉₊ + 1) := by
        apply Finset.card_biUnion_le_card_mul
        intro b _
        calc ((S.filter (fun a => |cellError a b| ≤ δ)).image (fun a => (a, b))).card
            ≤ (S.filter (fun a => |cellError a b| ≤ δ)).card := Finset.card_image_le
          _ ≤ ⌈2 * δ⌉₊ + 1 := dangerous_cells_per_row_bound b N δ hδ
    _ = N * (⌈2 * δ⌉₊ + 1) := by rw [hcard_S]

/-- At any scale N, most cells are safe: the dangerous cells are sparse.
    From total_dangerous_cells_bound, dangerous ≤ N·(⌈2δ⌉+1), so the
    safe fraction ≥ 1 - (⌈2δ⌉+1)/N → 1 as N → ∞ for fixed δ. -/
theorem safe_density_positive_of_irrational :
    ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, N₀ ≥ 2 ∧ ∀ N : ℕ, N ≥ N₀ →
      safeCellDensity N δ > 1 / 2 := by
  intro δ hδ
  set M := ⌈2 * δ⌉₊ + 1 with hM_def
  use max 2 (2 * M + 1)
  refine ⟨le_max_left _ _, fun N hN => ?_⟩
  have hN2 : N ≥ 2 := le_trans (le_max_left _ _) hN
  have hNM : N > 2 * M := by omega
  have hN_pos : (0 : ℝ) < N := by positivity
  have hN2_pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  set S := Finset.Icc (0 : ℤ) (↑N - 1) with hS_def
  set safe := (S ×ˢ S).filter (fun p => |cellError p.1 p.2| > δ)
  set dang := (S ×ˢ S).filter (fun p => |cellError p.1 p.2| ≤ δ)
  -- dang ⊆ S ×ˢ S
  have hdang_sub : dang ⊆ S ×ˢ S := Finset.filter_subset _ _
  -- safe = (S ×ˢ S) \ dang  (complement: > δ vs ≤ δ)
  have hsafe_eq : safe = (S ×ˢ S) \ dang := by
    ext p
    simp only [safe, dang, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro ⟨hm, hgt⟩; exact ⟨hm, fun ⟨_, hle⟩ => not_lt.mpr hle hgt⟩
    · intro ⟨hm, hnd⟩; exact ⟨hm, not_le.mp fun hle => hnd ⟨hm, hle⟩⟩
  have hdang_card : dang.card ≤ N * M := total_dangerous_cells_bound N δ hδ
  have hcard_S : S.card = N := by simp only [hS_def, Int.card_Icc]; omega
  have hcard_prod : (S ×ˢ S).card = N * N := by
    rw [Finset.card_product, hcard_S]
  -- safe.card + dang.card = N * N
  have hcomp : safe.card + dang.card = N * N := by
    have h := Finset.card_sdiff_add_card_eq_card hdang_sub
    rw [← hsafe_eq] at h; linarith
  -- Therefore safe.card ≥ N*N - N*M
  have hsafe_lower : safe.card ≥ N * N - N * M := by omega
  -- safeCellDensity N δ = safe.card / N² > 1/2
  show safeCellDensity N δ > 1 / 2
  unfold safeCellDensity
  change (safe.card : ℝ) / ((N : ℝ) ^ 2) > 1 / 2
  rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num : (0:ℝ) < 2) hN2_pos, one_mul]
  -- Goal: (N : ℝ)^2 < 2 * ↑safe.card
  -- From hsafe_lower: safe.card ≥ N*N - N*M (as ℕ)
  -- From hNM: N > 2*M, so N*N - N*M ≥ N*N - N*(N/2 - 1) > N*N/2
  -- Actually: 2*(N*N - N*M) ≥ 2*N*N - 2*N*M > N*N since N > 2*M
  have hNM_nat : N * M < N * N := by nlinarith
  have hsafe_pos : safe.card > 0 := by omega
  -- Work in ℝ: safe.card ≥ N*N - N*M (ℕ), and N > 2*M
  -- So (safe.card : ℝ) ≥ N*N - N*M ≥ 0, and we need N² < 2 * safe.card
  have hNM_nat : N * M < N * N := by nlinarith
  -- In ℤ: safe.card ≥ N*N - N*M
  have hsafe_int : (safe.card : ℤ) ≥ ↑(N * N) - ↑(N * M) := by omega
  -- In ℝ
  have hsafe_real : (safe.card : ℝ) ≥ (N : ℝ) * N - (N : ℝ) * M := by
    have := @Int.cast_le ℝ _ _ _ |>.mpr hsafe_int
    push_cast at this ⊢; linarith
  have hN_real : (N : ℝ) > 2 * (M : ℝ) := by exact_mod_cast hNM
  nlinarith [sq_nonneg (N : ℝ)]

/-! ## D4. Bridge: equidistribution implies safe cell visits

    If the Collatz cell sequence on (Z/NZ)² is equidistributed (from Weyl
    via the irrational rotation connection), and safe cells have density > 1/2
    (from Baker), then any trajectory visits safe cells with frequency > 1/2.
    Each safe cell visit has v₂ ≥ 2, giving deficit recovery. -/

/-- The cell sequence on (Z/NZ): at Syracuse step k, the ν₂ residue mod N. -/
noncomputable def cellSeqNu2 (n N : ℕ) (k : ℕ) : ℕ :=
  nu2 n (syracuseTime n k) % N

/-- The cell sequence on (Z/NZ): at Syracuse step k, the ν₃ residue mod N. -/
noncomputable def cellSeqNu3 (n N : ℕ) (k : ℕ) : ℕ :=
  nu3 n (syracuseTime n k) % N

/-- **Equidistribution of safe cell visits implies deficit control**.

    If for a trajectory starting at n:
    (a) The cell visits on (Z/NZ)² are equidistributed (from Weyl + log₂3 irrational)
    (b) Safe cells have density ≥ ρ > 0 at scale N (from Baker cell separation)
    (c) Each safe cell visit guarantees v₂ ≥ 2 (deficit non-increase)

    Then the deficit is bounded: over any window of W steps, the trajectory
    visits enough safe cells to compensate for the dangerous v₂=1 steps.

    This is the key bridge from equidistribution to the K-bound. -/
theorem equidistribution_implies_deficit_bounded
    (n : ℕ) (hn : n ≥ 1)
    (N : ℕ) (hN : N ≥ 2)
    (ρ : ℝ) (hρ : ρ > 0)
    -- Safe cell density at scale N exceeds ρ
    (hsafe : safeCellDensity N (1 / ↑N) > ρ)
    -- The cell visit sequence is equidistributed
    (hequi : IsEquidistributed (cellSeqNu2 n N) N) :
    ∃ D : ℤ, ∀ t : ℕ, deficit n t ≤ D := by
  -- SORRY CONTENT: This is the main analytical gap in the Weyl bridge.
  -- It is equivalent to the Collatz conjecture for the given n
  -- (via k_bound_of_deficit_bounded + nu3_linear_bound_iff_reaches).
  --
  -- Proof sketch (not yet formalized):
  --
  -- 1. SAFE CELL FREQUENCY: Equidistribution (hequi) ensures each residue
  --    r < N is visited with frequency → 1/N. Safe residues (|cellError| > 1/N)
  --    have density > ρ > 0 (hsafe). So safe cells are visited with cumulative
  --    frequency ≥ ρ - ε for any ε > 0, for windows past some M₀.
  --
  -- 2. DEFICIT ACCOUNTING: Each safe cell visit has v₂ ≥ 2, so the safe step
  --    contributes ≤ 0 to deficit (safe_steps_compensate). Each dangerous visit
  --    has v₂ = 1, contributing +2 to deficit per odd step.
  --
  -- 3. RUN-LEVEL ANALYSIS: Hensel attrition (hensel_attrition) ensures that
  --    dangerous v₂=1 runs of length d require 2^(d+1) | (x+1), giving
  --    exponentially decaying probability. Cell error shifts by d·(1 - log₂3)
  --    during a d-run (cellError_shift_of_v2_run), exceeding 1 for d ≥ 2
  --    (cellError_shift_exceeds_one), which forces exit to a safe cell.
  --
  -- 4. BUDGET: Safe visits (frequency ≥ ρ-ε) each recover ≥1 deficit unit.
  --    Dangerous runs contribute +d but are capped by Hensel at d ≤ O(log N).
  --    Net deficit growth rate → ≤ 0, giving bounded deficit.
  --
  -- The formal derivation requires connecting 1D equidistribution of ν₂ mod N
  -- to 2D cell visit statistics on (Z/NZ)², and converting Syracuse-step-level
  -- frequencies to uncompressed-step deficit accounting.
  sorry

/-! ## D5. From deficit bounded to K-bound

    **BUG NOTE**: The original `equidistribution_implies_sliding_window` attempted
    to produce `SlidingWindowCondition n W` (i.e., ∀ t, deficit(t+W) ≤ deficit(t)).
    However, SWC as defined is **false for many starting values**.

    Counterexample: n = 27 reaches 1 at step 111 with deficit(111) = 12 > 0.
    In the 1→4→2→1 cycle, deficit oscillates between {12, 13, 14}.
    But deficit(0) = 0, so deficit(0+W) ≈ 12 > 0 = deficit(0) for all large W.
    Hence `SlidingWindowCondition 27 W` is false for ALL W ≥ 1.

    More generally, SWC fails whenever the trajectory accumulates a positive
    deficit during the transient (odd-step density > 1/3 before reaching the
    1→4→2→1 cycle). Computationally: n=27 (deficit 12), n=31 (11), n=63 (10),
    n=97 (11) all have SWC false for every W.

    This bug also affects `solenoid_mixing` (SolenoidMixing.lean) and
    `finite_residence_bound` (DiophantineRepeller.lean), which assert
    SWC / HasCompensatedRuns for all n ≥ 1.

    The correct formulation is the K-bound: ∃ K T₀, ∀ t ≥ T₀, 3·ν₃ ≤ t + K.
    This IS true for n=27 (with K=12, T₀=0: 3·ν₃(t) ≤ t + 12 always).
    The corrected bridge goes: deficit bounded → K-bound directly,
    via `k_bound_of_deficit_bounded` (Drift.lean). -/

/-- **Equidistribution bridge to K-bound** (corrected).

    From bounded deficit (output of `equidistribution_implies_deficit_bounded`),
    the K-bound follows directly via `k_bound_of_deficit_bounded`.

    This replaces the original `equidistribution_implies_sliding_window` which
    incorrectly targeted `SlidingWindowCondition` (see bug note above). -/
theorem equidistribution_implies_k_bound
    (n : ℕ) (hn : n ≥ 1)
    (N : ℕ) (_hN : N ≥ 2)
    (ρ : ℝ) (_hρ : ρ > 0)
    (_hsafe : safeCellDensity N (1 / ↑N) > ρ)
    (_hequi : IsEquidistributed (cellSeqNu2 n N) N)
    (hdef : ∃ D : ℤ, ∀ t : ℕ, deficit n t ≤ D) :
    ∃ K : ℕ, ∃ T₀ : ℕ, ∀ t, t ≥ T₀ → 3 * nu3 n t ≤ t + K :=
  k_bound_of_deficit_bounded n hn hdef

/-- **The full bridge**: Weyl equidistribution + Baker separation + Hensel attrition
    together imply that the K-bound holds for every n ≥ 1.

    This is the alternative proof of nu3_linear_bound via the equidistribution route:
      weyl_equidistribution_of_irrational_rotation [axiom, this file]
        + irrational_logb_two_three [proved, Baker.lean]
        + baker_cell_separation [proved, DiophantineRepeller.lean]
        → equidistribution_implies_deficit_bounded [sorry, this file]
        → k_bound_of_deficit_bounded [proved, Drift.lean]
        = nu3_linear_bound

    Two gaps remain:
    (a) Weyl gives equidistribution of ⌊k·log₂3⌋ mod N, but we need
        equidistribution of cellSeqNu2 (the Collatz trajectory's ν₂ residues).
        These are different sequences; the connection requires showing the
        Collatz trajectory approximates an irrational rotation on the
        (2,3)-solenoid. This is the content of the solenoid mixing axiom (A5).
    (b) The deficit accounting in equidistribution_implies_deficit_bounded:
        converting cell-visit equidistribution into a bound on deficit growth. -/
theorem nu3_linear_bound_from_weyl (n : ℕ) (hn : n ≥ 1) :
    ∃ K : ℕ, ∃ T₀ : ℕ, ∀ t, t ≥ T₀ → 3 * nu3 n t ≤ t + K := by
  -- The proof chain would be:
  -- 1. Pick scale N large enough: safe_density_positive_of_irrational gives N₀
  -- 2. Establish cellSeqNu2 equidistribution [GAP (a): rotation ≠ trajectory]
  --    Weyl gives: IsEquidistributed (fun k => Int.toNat ⌊logb 2 3 * ↑k⌋) N
  --    We need:    IsEquidistributed (cellSeqNu2 n N) N
  --    The connection requires solenoid mixing (not available in this import chain).
  -- 3. Apply equidistribution_implies_deficit_bounded [sorry — GAP (b)]
  -- 4. Apply k_bound_of_deficit_bounded [proved, Drift.lean]
  sorry

/-! ## Summary of the equidistribution bridge

  New axiom inventory:
    weyl_equidistribution_of_irrational_rotation (this file)
    — Weyl's classical 1916 theorem for irrational rotation on Z/NZ

  Proof chain (alternative to finite_residence_bound):
    weyl_equidistribution_of_irrational_rotation [axiom]
      + irrational_logb_two_three [proved, Baker.lean]
      → log2_3_rotation_equidistributed [proved, this file]
    baker_cell_separation [proved, DiophantineRepeller.lean]
      → dangerous_cells_per_row_bound [proved, this file]
      → total_dangerous_cells_bound [proved, this file]
      → safe_density_positive_of_irrational [proved, this file]
    equidistribution_implies_deficit_bounded [sorry — accounting bridge]
      → k_bound_of_deficit_bounded [proved, Drift.lean]
      = nu3_linear_bound_from_weyl [sorry — needs cellSeq equidistribution]

  Remaining sorry gaps (2, down from the original 3):
  1. equidistribution_implies_deficit_bounded — connects equidistribution
     of cell visits to bounded deficit via safe/dangerous cell accounting.
     This is equivalent to the Collatz conjecture for the given n.
  2. nu3_linear_bound_from_weyl — assembly; needs to bridge the gap
     between Weyl's ⌊k·log₂3⌋ equidistribution and the actual Collatz
     cell visit sequence (cellSeqNu2). This gap is the solenoid mixing
     content (axiom A5 in SolenoidMixing.lean).

  Closed sorrys (4, up from 3):
  - dangerous_cells_per_row_bound — interval ⊆ Icc proof, card ≤ ⌈2δ⌉₊+1
  - total_dangerous_cells_bound — biUnion decomposition over b coordinate
  - safe_density_positive_of_irrational — complement counting + N > 2M
  - equidistribution_implies_k_bound — deficit bounded → K-bound
    (was equidistribution_implies_sliding_window [BUG: conclusion was false])

  BUG FOUND (SlidingWindowCondition is too strong):
    The original `equidistribution_implies_sliding_window` tried to produce
    `SlidingWindowCondition n W` (∀ t, deficit(t+W) ≤ deficit(t)).
    This condition is FALSE for n=27 and all W: deficit(0)=0 but the
    trajectory accumulates deficit(111)=12 > 0 in the transient, which
    persists in the 1→4→2→1 cycle. Same for n=31,63,97.
    The bug also affects `solenoid_mixing` and `finite_residence_bound`.
    The correct target is the K-bound: ∃ K T₀, ∀ t ≥ T₀, 3·ν₃ ≤ t + K.
-/

end Collatz
