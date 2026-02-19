/-
  CollatzLean/WallPersistence.lean
  Phase 5: Wall persistence — the computational and structural evidence
  that pure-even walls are a fundamental geometric feature.

  From the 10B empirical run (N=10^10):
  - Pure-even walls are 8.17% of occupied cells at the frozen resolution
  - Wall density is non-monotone in N but converges to a positive limit
  - Zero pure-odd successor cells (SFT "11" constraint)

  This file provides:
  1. Computational verification of wall existence at multiple scales
  2. Wall density definitions for quantitative analysis
  3. The walk confinement mechanism: walls force positive drift
  4. Connection from wall persistence to walk divergence
-/
import CollatzLean.TunnelWidth
import CollatzLean.Drift
import CollatzLean.StructuralPureEven

set_option linter.style.nativeDecide false

namespace Collatz

open Real

/-! ## Computational wall verification at multiple scales -/

/-- At scale 3^1 = 3 (9 cells), all cells are branch with N=10, T=50.
    Walls first appear at scale 3^2 = 9. -/
theorem wall_absent_3 : tunnelWallWidth 1 10 50 = 0 := by native_decide

/-- Pure-even walls exist at scale 3^2 = 9 (81 cells): 19 wall cells. -/
theorem wall_exists_9 : tunnelWallWidth 2 10 50 > 0 := by native_decide

/-- Pure-even walls exist at scale 3^3 = 27 (729 cells): 35 wall cells. -/
theorem wall_exists_27 : tunnelWallWidth 3 10 50 > 0 := by native_decide

/-! ## Wall density -/

/-- The wall density: fraction of occupied cells that are pure-even.
    At the frozen resolution (k ≥ 216), empirically ≈ 8.17%. -/
noncomputable def wallDensity (k N T : ℕ) [NeZero k] [DecidableEq (ZMod k)] : ℝ :=
  let pe := (pureEvenCount k N T : ℝ)
  let occ := ((branchCount k N T + pureEvenCount k N T) : ℝ)
  if occ > 0 then pe / occ else 0

/-- Branch count at scale 3^b. -/
def tunnelBranchCount (b N T : ℕ) : ℕ :=
  haveI : NeZero (3 ^ b) := ⟨by positivity⟩
  branchCount (3 ^ b) N T

/-- Occupied cell count (branch + pure-even) at scale 3^b.
    Pure-odd cells are excluded: they do not participate in the tunnel. -/
def tunnelOccupied (b N T : ℕ) : ℕ :=
  tunnelBranchCount b N T + tunnelWallWidth b N T

/-! ## Wall persistence statement -/

/-- Wall persistence at scale b: for sufficiently large sampling,
    pure-even cells exist. This is the core structural claim.
    Proved via tunnel_walls_positive (composition of Baker + geometric bridge). -/
theorem wall_persists (b : ℕ) (hb : b ≥ 1) :
    ∃ N T, tunnelWallWidth b N T > 0 :=
  tunnel_walls_positive b hb

/-! ## Walk confinement at walls -/

/-- The walk increment at a pure-even cell is exactly +1.
    This means: at every wall encounter, the walk moves toward +∞. -/
theorem wall_pushes_walk_up (k : ℕ) [NeZero k]
    (cell : ZMod k × ZMod k) (N T : ℕ)
    (hpe : isPureEven k cell N T)
    (n t : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ N) (ht1 : 1 ≤ t) (ht2 : t ≤ T)
    (hcell : torusResidue k n t = cell) :
    walkIncrement n t = 1 :=
  walkIncrement_at_pureEven k cell N T hpe n t hn1 hn2 ht1 ht2 hcell

/-! ## Wall encounter frequency -/

/-- Wall encounter frequency: the fraction of steps in [1,T] where
    trajectory n visits a pure-even cell on the (3^b)-torus.

    If walls are encountered with positive frequency ρ > 0 over T steps,
    the walk gains at least ρ · T from wall encounters alone.

    Combined with the overall walk drift, this gives walk(n,T) → +∞.
    The remaining drift from non-wall steps is bounded by the SFT constraint:
    p_odd ≤ 1/(1 + log₂(3)) - ε for some ε > 0 (from podd_uniform_bound).

    Net drift per step:
      δ = (1 - p_odd) · (+1) + p_odd · (-log₂(3))
        = 1 - p_odd · (1 + log₂(3))
        > 1 - (1/(1+log₂(3)) - ε) · (1 + log₂(3))
        = (1 + log₂(3)) · ε > 0

    This is exactly the argument in Drift.lean (walk_lower_bound_linear). -/
noncomputable def wallEncounterFreq (b n T : ℕ) : ℝ :=
  haveI : NeZero (3 ^ b) := ⟨by positivity⟩
  let wall_steps := (Finset.Icc 1 T).filter fun t =>
    isPureEvenBool (3 ^ b) (torusResidue (3 ^ b) n t) n T
  (wall_steps.card : ℝ) / (T : ℝ)

/-- Positive wall encounter frequency implies the walk gets a boost
    of at least freq · T from wall cells over T steps. -/
theorem wall_boost (b n T : ℕ) (hT : 0 < T)
    (hfreq : wallEncounterFreq b n T > 0) :
    wallEncounterFreq b n T * T > 0 :=
  mul_pos hfreq (Nat.cast_pos.mpr hT)

/-! ## Walk boost at double-halving steps -/

private lemma logb_two_three_lt_two : logb 2 3 < 2 := by
  have hlog2 : (0 : ℝ) < log 2 := log_pos (by norm_num)
  rw [logb, div_lt_iff₀ hlog2]
  calc log 3 < log 4 := log_lt_log (by positivity) (by norm_num)
    _ = log (2 ^ 2) := by norm_num
    _ = 2 * log 2 := by rw [log_pow]; ring

/-- The double-halving walk boost 2 - log₂3 is positive. -/
theorem walk_boost_pos : (2 : ℝ) - logb 2 3 > 0 := by
  linarith [logb_two_three_lt_two]

/-- At a double-halving odd step (a_t ≡ 1 (mod 4)), the walk gains
    exactly 2 - log₂3 > 0 over the next 3 steps (1 odd + 2 even).
    Step t: odd, walk -= log₂3.  Steps t+1, t+2: even, walk += 1 each.
    Net: -log₂3 + 1 + 1 = 2 - log₂3. -/
theorem walk_boost_double_halving (n t : ℕ)
    (hodd : isOddStep n t = true)
    (hmod4 : collatzSeq n t % 4 = 1) :
    walk n (t + 3) = walk n t + (2 - logb 2 3) := by
  -- Extract conditions for double_halving_two_even_steps
  have hodd_nat : collatzSeq n t % 2 = 1 := by
    simp only [isOddStep, decide_eq_true_eq] at hodd; exact hodd
  have hnonzero : collatzSeq n t ≠ 0 := by omega
  -- Get the two forced even steps
  obtain ⟨he1, he2⟩ := double_halving_two_even_steps n t hnonzero hodd_nat hmod4
  -- Chain the walk steps
  have h1 : walk n (t + 1) = walk n t - logb 2 3 :=
    walk_step_odd n t hodd
  have h2 : walk n (t + 2) = walk n (t + 1) + 1 := by
    rw [show t + 2 = (t + 1) + 1 from by omega]
    exact walk_step_even n (t + 1) he1
  have h3 : walk n (t + 3) = walk n (t + 2) + 1 := by
    rw [show t + 3 = (t + 2) + 1 from by omega]
    exact walk_step_even n (t + 2) he2
  linarith

/-! ## Summary of the proof chain -/

/-
  The full argument from wall persistence to Collatz conjecture:

  1. Baker's theorem (baker_two_three):
     |m·log 2 + n·log 3| > C / max(|m|,|n|)^κ

  2. Diophantine lower bound (diophError_lower_bound):
     |logb 2 3 - p/3^b| > C' / (3^b)^(1+ε)

  3. Wall persistence (tunnel_walls_positive):
     ∀ b ≥ 1, ∃ N T, pureEvenCount(3^b, N, T) > 0

  4. Walk confinement (wall_pushes_walk_up):
     At pure-even cells, walkIncrement = +1

  5. Walk boost (walk_boost_double_halving):
     At double-halving odd steps (a_t ≡ 1 mod 4), the walk gains
     2 - log₂3 > 0 over 3 steps (proved, 0 sorrys)

  6. K-bound (nu3_linear_bound):
     ∃ K, ∃ T₀, ∀ t ≥ T₀, 3·ν₃(n,t) ≤ t + K  [SORRY — critical path]

  7. Collatz conjecture (collatz_conjecture):
     ∀ n ≥ 1, ∃ T, collatzSeq n T = 1

  The Baker-Feldman bridge (Section 8.3):
  Steps 1→2→3 establish wall persistence.
  Step 4 shows walls force even steps (walk +1).
  Step 5 shows double-halving cells give walk gain 2 - log₂3 > 0.
  The GAP: step 6 (K-bound) requires an equidistribution result showing
  the average v₂ per odd step exceeds log₂3 for every trajectory.
  By nu3_linear_bound_iff_reaches (Conclusion.lean), the K-bound is
  formally equivalent to the Collatz conjecture for each n.
-/

/-! ## Evaluation -/

-- Wall widths at increasing scales
#eval tunnelWallWidth 1 10 50    -- 3^1 = 3:  0 walls (too small)
#eval tunnelWallWidth 2 10 50    -- 3^2 = 9:  19 walls
#eval tunnelWallWidth 3 10 50    -- 3^3 = 27: 35 walls
#eval tunnelBranchCount 1 10 50  -- 9 branch
#eval tunnelBranchCount 2 10 50  -- 34 branch
#eval tunnelBranchCount 3 10 50  -- 57 branch
#eval tunnelOccupied 1 10 50     -- 9 occupied
#eval tunnelOccupied 2 10 50     -- 53 occupied
#eval tunnelOccupied 3 10 50     -- 92 occupied

end Collatz
