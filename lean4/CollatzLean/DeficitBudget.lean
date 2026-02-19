/-
  CollatzLean/DeficitBudget.lean
  Deficit budget framework connecting Hensel attrition (v₂=1 run statistics)
  to the SlidingWindowCondition (DiophantineRepeller.lean).

  All theorems sorry-free. Reduces finite_residence_bound to a pure
  equidistribution / even-density statement about the Collatz trajectory.

  Key results:
  - deficit_budget_of_window: deficit change ≤ Δν₃ + 1 per window (D1)
  - safe_steps_compensate: Δν₂ ≥ 2·Δν₃ → deficit non-increasing (D2)
  - v2_run_bounded_deficit_contrib: run of d costs d over 2d+3 steps (D3)
  - sliding_window_of_safe_density: even-density → SlidingWindowCondition (D4)
-/
import CollatzLean.DiophantineRepeller

set_option linter.style.nativeDecide false

namespace Collatz

/-! ## Monotonicity of step counters -/

/-- ν₃ increases by at most 1 per step. -/
theorem nu3_step_le (n s : ℕ) : nu3 n s ≤ nu3 n (s + 1) := by
  change nu3 n s ≤ nu3 n s + if isOddStep n s then 1 else 0
  split <;> omega

/-- ν₂ increases by at most 1 per step. -/
theorem nu2_step_le (n s : ℕ) : nu2 n s ≤ nu2 n (s + 1) := by
  change nu2 n s ≤ nu2 n s + if isEvenStep n s then 1 else 0
  split <;> omega

/-- ν₃ is monotone over multiple steps. -/
theorem nu3_le_add (n s k : ℕ) : nu3 n s ≤ nu3 n (s + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : s + (k + 1) = (s + k) + 1 := by omega
    rw [this]; exact le_trans ih (nu3_step_le n (s + k))

/-- ν₂ is monotone over multiple steps. -/
theorem nu2_le_add (n s k : ℕ) : nu2 n s ≤ nu2 n (s + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : s + (k + 1) = (s + k) + 1 := by omega
    rw [this]; exact le_trans ih (nu2_step_le n (s + k))

/-! ## No-consecutive-odd constraint and pair bound -/

/-- In any two consecutive steps for n ≥ 1, at most one is odd.
    Direct consequence of no_consecutive_odd_steps. -/
theorem nu3_pair_bound (n s : ℕ) (hn : n ≥ 1) :
    nu3 n (s + 2) - nu3 n s ≤ 1 := by
  by_cases ho : isOddStep n s = true
  · -- Step s is odd → step s+1 must be even (not odd)
    have hne := collatzSeq_ne_zero n hn s
    have hf := no_consecutive_odd_steps n s hne ho
    have h1 : nu3 n (s + 1) = nu3 n s + 1 := nu3_step_odd n s ho
    have h2 : nu3 n (s + 2) = nu3 n (s + 1) := by
      rw [show s + 2 = (s + 1) + 1 from by omega]
      exact nu3_step_even n (s + 1) (by
        simp only [isEvenStep, isOddStep, decide_eq_true_eq,
          decide_eq_false_iff_not] at hf ⊢; omega)
    omega
  · -- Step s is not odd → nu3 doesn't increment at s
    have he : isEvenStep n s = true := by
      simp only [isOddStep, decide_eq_true_eq] at ho
      simp only [isEvenStep, decide_eq_true_eq]; omega
    have h1 : nu3 n (s + 1) = nu3 n s := nu3_step_even n s he
    -- nu3(s+2) = nu3(s+1) + (0 or 1) ≤ nu3(s+1) + 1
    have h2 : nu3 n (s + 2) ≤ nu3 n (s + 1) + 1 := by
      have : nu3 n (s + 2) = nu3 n (s + 1) +
        if isOddStep n (s + 1) then 1 else 0 := by
        change nu3 n ((s + 1) + 1) = _; rfl
      rw [this]; split <;> omega
    omega

/-! ## Odd step bounds over windows -/

/-- In 2k steps starting from t, at most k are odd (for n ≥ 1).
    Proved by induction using the pair bound. -/
theorem nu3_bounded (n t : ℕ) (hn : n ≥ 1) (k : ℕ) :
    nu3 n (t + 2 * k) ≤ nu3 n t + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := nu3_pair_bound n (t + 2 * k) hn
    have hm := nu3_le_add n t (2 * k)
    have : t + 2 * (k + 1) = (t + 2 * k) + 2 := by ring
    rw [this]; omega

/-- **D1 prerequisite**: In W steps, 2·Δν₃ ≤ W + 1.
    This is the constraint from no_consecutive_odd_steps. -/
theorem odd_steps_le_half_ceil (n t W : ℕ) (hn : n ≥ 1) :
    2 * (nu3 n (t + W) - nu3 n t) ≤ W + 1 := by
  set k := W / 2 with hk_def
  have hbd := nu3_bounded n t hn k
  have hm := nu3_le_add n t (2 * k)
  rcases (show W % 2 = 0 ∨ W % 2 = 1 from by omega) with heven | hodd
  · -- W even: W = 2k, so nu3(t+W) = nu3(t+2k) ≤ nu3(t)+k
    have hW : W = 2 * k := by omega
    have : t + W = t + 2 * k := by omega
    rw [this] at *; omega
  · -- W odd: W = 2k+1
    have hW : W = 2 * k + 1 := by omega
    -- nu3(t+2k+1) - nu3(t+2k) ≤ 1 by one-step bound
    have h_one : nu3 n (t + 2 * k + 1) - nu3 n (t + 2 * k) ≤ 1 := by
      show nu3 n ((t + 2 * k) + 1) - nu3 n (t + 2 * k) ≤ 1
      simp only [nu3]; split <;> omega
    -- t + W = t + 2*k + 1
    have htW : t + W = t + 2 * k + 1 := by omega
    rw [htW]; omega

/-! ## Core deficit algebra for windows -/

/-- The deficit change over W steps: an exact identity. -/
theorem deficit_change_eq (n t W : ℕ) :
    deficit n (t + W) - deficit n t =
    3 * (↑(nu3 n (t + W)) - ↑(nu3 n t) : ℤ) - ↑W := by
  simp only [deficit]; push_cast; ring

/-- Deficit change using ℕ subtraction (safe by ν₃ monotonicity). -/
theorem deficit_change_nat (n t W : ℕ) :
    deficit n (t + W) - deficit n t =
    3 * ↑(nu3 n (t + W) - nu3 n t) - (↑W : ℤ) := by
  have h := nu3_le_add n t W
  simp only [deficit]; push_cast; omega

/-- Deficit change in Δν₃/Δν₂ form: deficit change = 2·Δν₃ - Δν₂. -/
theorem deficit_change_alt (n t W : ℕ) :
    deficit n (t + W) - deficit n t =
    2 * ↑(nu3 n (t + W) - nu3 n t) - ↑(nu2 n (t + W) - nu2 n t) := by
  have hp1 := nu_partition n t
  have hp2 := nu_partition n (t + W)
  have hm3 := nu3_le_add n t W
  have hm2 := nu2_le_add n t W
  simp only [deficit]; push_cast; omega

/-! ## D1: Deficit budget of a window -/

/-- **deficit_budget_of_window (D1)**: The deficit change over W steps is
    bounded by the number of odd steps (plus 1 for boundary effects).

    Since each v₂=1 compressed pair contributes +1 to deficit and uses 1
    odd step, and safe compressed steps (v₂≥2) contribute ≤ 0, the number
    of v₂=1 pairs ≤ Δν₃. Therefore:
      deficit(t+W) - deficit(t) ≤ Δν₃ + 1 ≤ (number of v₂=1 pairs) + 1

    The +1 accounts for a possible boundary odd step at the end of the window. -/
theorem deficit_budget_of_window (n t W : ℕ) (hn : n ≥ 1) :
    deficit n (t + W) - deficit n t ≤ ↑(nu3 n (t + W) - nu3 n t) + 1 := by
  have hchange := deficit_change_nat n t W
  have hbound := odd_steps_le_half_ceil n t W hn
  omega

/-! ## D2: Safe steps compensate -/

/-- **safe_steps_compensate (D2)**: If even steps in the window are at least
    twice the odd steps (Δν₂ ≥ 2·Δν₃), the deficit does not increase.

    Interpretation: Each compressed Collatz step has 1 odd + v₂ even steps.
    - v₂=1 pair: deficit change = +2-1 = +1 (dangerous)
    - v₂=2 step: deficit change = +2-2 = 0 (neutral)
    - v₂≥3 step: deficit change = +2-v₂ ≤ -1 (safe, compensates one v₂=1)

    The condition Δν₂ ≥ 2·Δν₃ ensures enough safe steps to absorb all
    v₂=1 contributions. -/
theorem safe_steps_compensate (n t W : ℕ)
    (h : nu2 n (t + W) - nu2 n t ≥ 2 * (nu3 n (t + W) - nu3 n t)) :
    deficit n (t + W) ≤ deficit n t := by
  have hm3 := nu3_le_add n t W
  have hm2 := nu2_le_add n t W
  have hchange := deficit_change_alt n t W
  omega

/-! ## D3: v₂=1 run deficit contribution -/

/-- **v2_run_bounded_deficit_contrib (D3)**: A maximal v₂=1 run of length d
    followed by its exit contributes exactly d to the deficit over 2d+3
    uncompressed steps.

    The deficit cost per step is d/(2d+3) < 1/2, meaning the deficit
    growth rate during a run is bounded below 1/2. This ensures that
    even the worst-case v₂=1 runs leave room for compensation by safe steps
    in the remainder of the window. -/
theorem v2_run_bounded_deficit_contrib (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1)
    (hexit : oddCollatzStep (oddCollatzIter (collatzSeq n t) d) % 2 = 0) :
    deficit n (t + 2 * d + 3) = deficit n t + ↑d ∧ 2 * d < 2 * d + 3 :=
  ⟨deficit_of_run_plus_exit n t d hn hodd hrun hexit, by omega⟩

/-- The deficit cost per uncompressed step during a run + exit is less than 1/2.
    Formally: 2·d < 2·d + 3, so d/(2d+3) < 1/2. -/
theorem v2_run_rate_lt_half (d : ℕ) : 2 * d < 2 * d + 3 := by omega

/-! ## D4: Sliding window from safe density -/

/-- **SlidingWindowCondition ↔ odd density ≤ 1/3**: The sliding window condition
    holds if and only if in every window of W steps, the number of odd steps
    is at most W/3 (equivalently, 3·Δν₃ ≤ W).

    This is the key characterization: finite_residence_bound reduces to the
    pure equidistribution statement that odd step density never exceeds 1/3
    in any window of bounded size. -/
theorem sliding_window_iff_odd_density (n W : ℕ) :
    SlidingWindowCondition n W ↔
    ∀ t, 3 * (nu3 n (t + W) - nu3 n t) ≤ W := by
  constructor
  · intro h t
    have hdef := h t  -- deficit(t+W) ≤ deficit(t)
    have hchange := deficit_change_nat n t W
    omega
  · intro h t
    have hchange := deficit_change_nat n t W
    have := h t
    omega

/-- **sliding_window_of_even_density (D4, part 1)**: If every window of W steps
    has Δν₂ ≥ 2·Δν₃, then SlidingWindowCondition holds. -/
theorem sliding_window_of_even_density (n W : ℕ)
    (h : ∀ t, nu2 n (t + W) - nu2 n t ≥ 2 * (nu3 n (t + W) - nu3 n t)) :
    SlidingWindowCondition n W :=
  fun t => safe_steps_compensate n t W (h t)

/-- **sliding_window_of_safe_density (D4, full reduction)**: If in every window
    of W steps, at least a fraction α of the steps are "safe" (contributing
    deficit ≤ -1), AND the v₂=1 contribution is compensated, then the sliding
    window condition holds.

    More precisely: 3·Δν₃ ≤ W in every window suffices. This is equivalent
    to: the odd step proportion in every window is at most 1/3.

    Connection to finite_residence_bound:
    - finite_residence_bound asks for ∃ W ≥ 1, SlidingWindowCondition n W
    - By this theorem, it suffices to find W such that 3·Δν₃ ≤ W in every window
    - This is a pure equidistribution statement on the (2,3)-solenoid:
      the trajectory visits odd steps (×3+1) at most 1/3 of the time -/
theorem sliding_window_of_safe_density (n : ℕ) (_hn : n ≥ 1)
    (W : ℕ) (hW : W ≥ 1) (h : ∀ t, 3 * (nu3 n (t + W) - nu3 n t) ≤ W) :
    ∃ W' : ℕ, W' ≥ 1 ∧ SlidingWindowCondition n W' :=
  ⟨W, hW, (sliding_window_iff_odd_density n W).mpr h⟩

/-! ## Quantitative budget: v₂≥3 compensates v₂=1 -/

/-- A "safe 3-step block" (1 odd + 2 even) leaves the deficit unchanged.
    Already proved as deficit_nonincreasing_at_safe_step — this rephrases
    it as an exact equality when exactly 2 even steps follow. -/
theorem deficit_safe_block_eq (n t : ℕ)
    (ho : isOddStep n t = true) (he1 : isEvenStep n (t + 1) = true)
    (he2 : isEvenStep n (t + 2) = true) :
    deficit n (t + 3) = deficit n t + (2 - 1 - 1 : ℤ) := by
  have s1 := deficit_step_odd n t ho
  have s2 : deficit n (t + 2) = deficit n (t + 1) - 1 := by
    rw [show t + 2 = (t + 1) + 1 from by omega]
    exact deficit_step_even n (t + 1) he1
  have s3 : deficit n (t + 3) = deficit n (t + 2) - 1 := by
    rw [show t + 3 = (t + 2) + 1 from by omega]
    exact deficit_step_even n (t + 2) he2
  omega

/-- A "safe+ 4-step block" (1 odd + 3 even) decreases deficit by 1.
    This is the key recovery mechanism: each v₂≥3 step compensates
    one v₂=1 pair's deficit contribution. -/
theorem deficit_safe_plus_block (n t : ℕ)
    (ho : isOddStep n t = true)
    (he1 : isEvenStep n (t + 1) = true)
    (he2 : isEvenStep n (t + 2) = true)
    (he3 : isEvenStep n (t + 3) = true) :
    deficit n (t + 4) ≤ deficit n t - 1 := by
  have s1 := deficit_step_odd n t ho
  have s2 : deficit n (t + 2) = deficit n (t + 1) - 1 := by
    rw [show t + 2 = (t + 1) + 1 from by omega]
    exact deficit_step_even n (t + 1) he1
  have s3 : deficit n (t + 3) = deficit n (t + 2) - 1 := by
    rw [show t + 3 = (t + 2) + 1 from by omega]
    exact deficit_step_even n (t + 2) he2
  have s4 : deficit n (t + 4) = deficit n (t + 3) - 1 := by
    rw [show t + 4 = (t + 3) + 1 from by omega]
    exact deficit_step_even n (t + 3) he3
  omega

/-- A v₂=1 pair (1 odd + 1 even, next step is odd again) increases deficit by 1. -/
theorem deficit_v2_one_pair (n t : ℕ)
    (ho : isOddStep n t = true) (he : isEvenStep n (t + 1) = true) :
    deficit n (t + 2) = deficit n t + 1 := by
  have s1 := deficit_step_odd n t ho
  have s2 : deficit n (t + 2) = deficit n (t + 1) - 1 := by
    rw [show t + 2 = (t + 1) + 1 from by omega]
    exact deficit_step_even n (t + 1) he
  omega

/-! ## Summary of the deficit budget reduction -/

/-
  The deficit budget framework reduces finite_residence_bound to:

    ∃ W ≥ 1, ∀ t, 3 · (ν₃(n, t+W) - ν₃(n, t)) ≤ W

  This is a pure EQUIDISTRIBUTION statement: the proportion of odd steps
  (×3+1 operations) in the Collatz sequence never exceeds 1/3 in any
  window of W consecutive steps.

  Proof chain (all sorry-free):
    odd_density ≤ 1/3 in every W-window
      → sliding_window_iff_odd_density  → SlidingWindowCondition n W
      → k_bound_from_repeller           → ∃ K T₀, ∀ t≥T₀, 3·ν₃≤t+K
      → reaches_one_of_linear_drift     → collatzReaches n

  The budget accounting:
    - v₂=1 pair: +1 deficit over 2 steps (deficit_v2_one_pair)
    - v₂=2 block: 0 deficit over 3 steps (deficit_safe_block_eq)
    - v₂≥3 block: ≤-1 deficit over ≥4 steps (deficit_safe_plus_block)
    - Run of d: +d deficit over 2d+3 steps (deficit_of_run_plus_exit)
    - Rate < 1/2 per step (v2_run_rate_lt_half)

  Each v₂≥3 compressed step compensates one v₂=1 pair. The equidistribution
  condition ensures enough v₂≥3 steps occur in every window to maintain
  deficit non-growth (SlidingWindowCondition).
-/

-- Concrete verification
example : deficit 7 0 = 0 := by native_decide
example : deficit 7 4 = 2 := by native_decide   -- after v₂=1 pairs
example : deficit 7 16 = -1 := by native_decide  -- safe steps compensated

end Collatz
