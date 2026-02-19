/-
  CollatzLean/HenselAttrition.lean
  Hensel attrition: d consecutive v₂=1 steps in the compressed
  Collatz sequence require x ≡ -1 (mod 2^(d+1)).
  Attrition rate exactly 2^{-d}. Pure modular arithmetic — no Baker needed.
-/
import CollatzLean.Walk
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace Collatz

/-! ## Compressed odd Collatz step -/

/-- The compressed odd Collatz step: T(x) = (3x+1)/2.
    Meaningful for odd x, where 3x+1 is even so the division is exact. -/
def oddCollatzStep (x : ℕ) : ℕ := (3 * x + 1) / 2

/-- Iterate the compressed odd step d times. -/
def oddCollatzIter (x : ℕ) : ℕ → ℕ
  | 0 => x
  | d + 1 => oddCollatzStep (oddCollatzIter x d)

@[simp] lemma oddCollatzIter_zero (x : ℕ) : oddCollatzIter x 0 = x := rfl

@[simp] lemma oddCollatzIter_succ' (x d : ℕ) :
    oddCollatzIter x (d + 1) = oddCollatzStep (oddCollatzIter x d) := rfl

/-- Shift: iterating d+1 times from x = iterating d times from T(x). -/
theorem oddCollatzIter_shift (x : ℕ) (d : ℕ) :
    oddCollatzIter x (d + 1) = oddCollatzIter (oddCollatzStep x) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change oddCollatzStep (oddCollatzIter x (d + 1)) =
         oddCollatzStep (oddCollatzIter (oddCollatzStep x) d)
    rw [ih]

/-! ## Key algebraic identity -/

/-- When x is odd, 2 * (T(x) + 1) = 3 * (x + 1).
    This identity avoids division and is the core of Hensel attrition. -/
theorem oddCollatzStep_key (x : ℕ) (hx : x % 2 = 1) :
    2 * (oddCollatzStep x + 1) = 3 * (x + 1) := by
  unfold oddCollatzStep; omega

/-- When x is odd, T(x) is well-defined: 2 * T(x) = 3 * x + 1. -/
theorem two_mul_oddCollatzStep (x : ℕ) (hx : x % 2 = 1) :
    2 * oddCollatzStep x = 3 * x + 1 := by
  unfold oddCollatzStep; omega

/-! ## Forward step: divisibility propagation -/

/-- If 2^(k+1) | (x+1) and x is odd, then 2^k | (T(x)+1). -/
theorem forward_step (x k : ℕ) (hx : x % 2 = 1) (h : 2 ^ (k + 1) ∣ x + 1) :
    2 ^ k ∣ oddCollatzStep x + 1 := by
  obtain ⟨m, hm⟩ := h
  have key := oddCollatzStep_key x hx
  have h1 : oddCollatzStep x + 1 = 3 * (2 ^ k * m) := by
    have : 2 * (oddCollatzStep x + 1) = 2 * (3 * (2 ^ k * m)) := by
      rw [key, hm, pow_succ]; ring
    omega
  exact ⟨3 * m, by linarith⟩

/-! ## Backward step: divisibility recovery -/

/-- If x is odd and 2^k | (T(x)+1), then 2^(k+1) | (x+1). -/
theorem backward_step (x k : ℕ) (hx : x % 2 = 1)
    (h : 2 ^ k ∣ oddCollatzStep x + 1) :
    2 ^ (k + 1) ∣ x + 1 := by
  obtain ⟨m, hm⟩ := h
  have key := oddCollatzStep_key x hx
  have h1 : 2 ^ (k + 1) * m = 3 * (x + 1) := by
    rw [pow_succ, mul_assoc]
    linarith
  have hcop : Nat.Coprime (2 ^ (k + 1)) 3 := by
    apply Nat.Coprime.pow_left
    decide
  exact hcop.dvd_of_dvd_mul_left ⟨m, h1.symm⟩

/-! ## Main theorem: Hensel attrition -/

/-- **Hensel attrition (forward direction)**: If 2^(d+1) | (x+1) and x is odd,
    then all d+1 iterates T^0(x), ..., T^d(x) are odd.
    This means d consecutive v₂=1 steps are possible. -/
theorem hensel_forward (x d : ℕ) (hx : x % 2 = 1) (h : 2 ^ (d + 1) ∣ x + 1) :
    ∀ i, i ≤ d → oddCollatzIter x i % 2 = 1 := by
  induction d generalizing x with
  | zero =>
    intro i hi
    interval_cases i
    exact hx
  | succ d ih =>
    intro i hi
    -- From 2^(d+2) | (x+1), derive 2^(d+1) | (T(x)+1) via forward_step
    have hTdvd : 2 ^ (d + 1) ∣ oddCollatzStep x + 1 :=
      forward_step x (d + 1) hx h
    -- T(x) is odd (since 2^(d+1) | (T(x)+1) with d+1 ≥ 1)
    have hTodd : oddCollatzStep x % 2 = 1 := by
      obtain ⟨m, hm⟩ := hTdvd
      have : oddCollatzStep x + 1 = 2 * (2 ^ d * m) := by
        rw [hm, pow_succ]; ring
      omega
    -- Apply IH to T(x): all iterates of T(x) up to d are odd
    have ih' := ih (oddCollatzStep x) hTodd hTdvd
    -- Split on whether i = 0 or i = j + 1
    cases i with
    | zero => exact hx
    | succ j =>
      rw [oddCollatzIter_shift]
      exact ih' j (by omega)

/-- **Hensel attrition (backward direction)**: If all iterates T^0(x), ..., T^d(x)
    are odd, then 2^(d+1) | (x+1). -/
theorem hensel_backward (x d : ℕ) (hx : x % 2 = 1)
    (hall : ∀ i, i ≤ d → oddCollatzIter x i % 2 = 1) :
    2 ^ (d + 1) ∣ x + 1 := by
  induction d generalizing x with
  | zero =>
    -- 2^1 | (x+1) since x is odd
    exact ⟨(x + 1) / 2, by omega⟩
  | succ d ih =>
    -- T(x) is odd (from hall at i = 1)
    have hTodd : oddCollatzStep x % 2 = 1 := by
      have := hall 1 (by omega)
      rwa [oddCollatzIter_shift, oddCollatzIter_zero] at this
    -- All iterates of T(x) up to d are odd
    have hall' : ∀ i, i ≤ d → oddCollatzIter (oddCollatzStep x) i % 2 = 1 := by
      intro i hi
      have := hall (i + 1) (by omega)
      rwa [oddCollatzIter_shift] at this
    -- By IH: 2^(d+1) | (T(x)+1)
    have hTdvd := ih (oddCollatzStep x) hTodd hall'
    -- By backward_step: 2^(d+2) | (x+1)
    exact backward_step x (d + 1) hx hTdvd

/-- **Hensel attrition theorem**: d consecutive v₂=1 steps starting from odd x
    are possible if and only if x ≡ -1 (mod 2^(d+1)), i.e., 2^(d+1) | (x+1).
    The fraction of odd numbers satisfying this is exactly 2^{-d}. -/
theorem hensel_attrition (x d : ℕ) (hx : x % 2 = 1) :
    (∀ i, i ≤ d → oddCollatzIter x i % 2 = 1) ↔ 2 ^ (d + 1) ∣ x + 1 :=
  ⟨hensel_backward x d hx, hensel_forward x d hx⟩

/-! ## Concrete verification -/

-- T(3) = 5 (odd), T(5) = 8 (even). So 3 has exactly 1 consecutive v₂=1 step.
-- 3 + 1 = 4 = 2², and indeed 2^(1+1) | 4 but 2^(2+1) ∤ 4.
example : oddCollatzStep 3 = 5 := by native_decide
example : oddCollatzStep 5 = 8 := by native_decide
example : oddCollatzStep 7 = 11 := by native_decide
example : oddCollatzStep 11 = 17 := by native_decide

-- x = 7: T(7) = 11, T(11) = 17, both odd. 7+1 = 8 = 2³. Two v₂=1 steps.
example : 2 ^ 3 ∣ (7 + 1) := ⟨1, by norm_num⟩
example : oddCollatzIter 7 0 % 2 = 1 := by native_decide
example : oddCollatzIter 7 1 % 2 = 1 := by native_decide
example : oddCollatzIter 7 2 % 2 = 1 := by native_decide

-- x = 15: 15+1 = 16 = 2⁴. Three v₂=1 steps.
example : 2 ^ 4 ∣ (15 + 1) := ⟨1, by norm_num⟩
example : oddCollatzIter 15 3 % 2 = 1 := by native_decide

/-! ## Bridge to collatz -/

/-- Two steps of collatz on an odd nonzero number equals oddCollatzStep. -/
theorem collatz_two_steps_eq_oddCollatzStep (x : ℕ) (hx : x % 2 = 1) (hpos : x ≠ 0) :
    collatz (collatz x) = oddCollatzStep x := by
  rw [collatz_odd x hpos hx]
  have heven : (3 * x + 1) % 2 = 0 := by omega
  have hpos' : 3 * x + 1 ≠ 0 := by omega
  rw [collatz_even (3 * x + 1) hpos' heven]
  rfl

/-- If collatzSeq n t is odd and nonzero, then collatzSeq n (t+2) = T(collatzSeq n t). -/
theorem collatzSeq_two_steps (n t : ℕ) (hodd : collatzSeq n t % 2 = 1)
    (hpos : collatzSeq n t ≠ 0) :
    collatzSeq n (t + 2) = oddCollatzStep (collatzSeq n t) := by
  simp only [collatzSeq_succ]
  exact collatz_two_steps_eq_oddCollatzStep (collatzSeq n t) hodd hpos

/-! ## Dangerous exit forced -/

/-- After a maximal run of v₂=1 steps, the next step has v₂ ≥ 2.
    If a is odd but T(a) is even, then 4 | (3a + 1). -/
theorem dangerous_exit_forced (a : ℕ) (ha : a % 2 = 1)
    (hexit : oddCollatzStep a % 2 = 0) :
    4 ∣ 3 * a + 1 := by
  unfold oddCollatzStep at hexit
  omega

/-! ## Positivity preservation -/

/-- The Collatz sequence stays positive for positive starting values. -/
theorem collatzSeq_pos (n : ℕ) (hn : n ≥ 1) (t : ℕ) : collatzSeq n t ≥ 1 := by
  induction t with
  | zero => simp [collatzSeq]; omega
  | succ t ih => exact le_of_eq rfl |>.trans (collatz_pos (collatzSeq n t) ih)

theorem collatzSeq_ne_zero (n : ℕ) (hn : n ≥ 1) (t : ℕ) : collatzSeq n t ≠ 0 := by
  have := collatzSeq_pos n hn t; omega

/-! ## Multi-step bridge: v₂=1 runs in collatzSeq -/

/-- During d consecutive v₂=1 steps, collatzSeq at even offsets tracks oddCollatzIter. -/
theorem collatzSeq_tracks_oddCollatzIter (n t d : ℕ) (hn : n ≥ 1)
    (_hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1) :
    ∀ i, i ≤ d → collatzSeq n (t + 2 * i) = oddCollatzIter (collatzSeq n t) i := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i ≤ d := by omega
    have hprev := ih (le_of_lt (by omega : i < i + 1) |>.trans hi)
    -- collatzSeq n (t + 2*i) is odd and positive
    have hodd_i : collatzSeq n (t + 2 * i) % 2 = 1 := by
      rw [hprev]; exact hrun i hi'
    have hpos_i : collatzSeq n (t + 2 * i) ≠ 0 :=
      collatzSeq_ne_zero n hn (t + 2 * i)
    -- Two uncompressed steps advance by one compressed step
    have : t + 2 * (i + 1) = (t + 2 * i) + 2 := by ring
    rw [this, collatzSeq_two_steps n (t + 2 * i) hodd_i hpos_i]
    simp [oddCollatzIter, hprev]

/-- During a v₂=1 run, odd-indexed steps are odd (in the parity sense). -/
theorem isOddStep_during_v2_run (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1) :
    ∀ i, i < d → isOddStep n (t + 2 * i) = true := by
  intro i hi
  have htrack := collatzSeq_tracks_oddCollatzIter n t d hn hodd hrun i (by omega)
  simp only [isOddStep, decide_eq_true_eq]
  rw [htrack]
  exact hrun i (by omega)

/-- During a v₂=1 run, even-indexed steps are even (the halving steps). -/
theorem isEvenStep_during_v2_run (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1) :
    ∀ i, i < d → isEvenStep n (t + 2 * i + 1) = true := by
  intro i hi
  -- At step t+2i, the value is odd; by no_consecutive_odd_steps, step t+2i+1 is even
  have hodd_step := isOddStep_during_v2_run n t d hn hodd hrun i hi
  have hpos := collatzSeq_ne_zero n hn (t + 2 * i)
  have := no_consecutive_odd_steps n (t + 2 * i) hpos hodd_step
  simp only [isEvenStep, isOddStep, decide_eq_true_eq, decide_eq_false_iff_not] at this ⊢
  omega

/-! ## Winding number accounting for v₂=1 runs -/

/-- During d consecutive v₂=1 steps, ν₃ increases by exactly d. -/
theorem nu3_of_v2_run (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1) :
    nu3 n (t + 2 * d) = nu3 n t + d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hrun' : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1 :=
      fun i hi => hrun i (by omega)
    have ih_val := ih hrun'
    -- Step t+2d is odd, step t+2d+1 is even
    have hodd_d := isOddStep_during_v2_run n t (d + 1) hn hodd hrun d (by omega)
    have heven_d := isEvenStep_during_v2_run n t (d + 1) hn hodd hrun d (by omega)
    -- nu3(t+2(d+1)) = nu3(t+2d+2) = nu3(t+2d+1) + 0 = nu3(t+2d) + 1
    have step1 : nu3 n (t + 2 * d + 1) = nu3 n (t + 2 * d) + 1 :=
      nu3_step_odd n (t + 2 * d) hodd_d
    have step2 : nu3 n (t + 2 * d + 2) = nu3 n (t + 2 * d + 1) :=
      nu3_step_even n (t + 2 * d + 1) heven_d
    have : t + 2 * (d + 1) = t + 2 * d + 2 := by ring
    rw [this, step2, step1, ih_val]
    ring

/-- During d consecutive v₂=1 steps, ν₂ increases by exactly d. -/
theorem nu2_of_v2_run (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1) :
    nu2 n (t + 2 * d) = nu2 n t + d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hrun' : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1 :=
      fun i hi => hrun i (by omega)
    have ih_val := ih hrun'
    have hodd_d := isOddStep_during_v2_run n t (d + 1) hn hodd hrun d (by omega)
    have heven_d := isEvenStep_during_v2_run n t (d + 1) hn hodd hrun d (by omega)
    -- nu2(t+2d+1) = nu2(t+2d) (odd step, nu2 unchanged)
    -- nu2(t+2d+2) = nu2(t+2d+1) + 1 (even step, nu2 increments)
    have step1 : nu2 n (t + 2 * d + 1) = nu2 n (t + 2 * d) :=
      nu2_step_odd n (t + 2 * d) hodd_d
    have step2 : nu2 n (t + 2 * d + 2) = nu2 n (t + 2 * d + 1) + 1 :=
      nu2_step_even n (t + 2 * d + 1) heven_d
    have : t + 2 * (d + 1) = t + 2 * d + 2 := by ring
    rw [this, step2, step1, ih_val]
    ring

/-- **Equal winding**: During d consecutive v₂=1 steps, ν₂ and ν₃ increase
    by the same amount d. The walk contribution is d*(1 - log₂3). -/
theorem equal_winding_of_v2_run (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1) :
    nu2 n (t + 2 * d) - nu2 n t = nu3 n (t + 2 * d) - nu3 n t := by
  rw [nu3_of_v2_run n t d hn hodd hrun, nu2_of_v2_run n t d hn hodd hrun]
  omega

/-! ## Walk effect of v₂=1 runs -/

open Real in
/-- **Walk deficit**: During d consecutive v₂=1 steps (2d uncompressed steps),
    the walk changes by exactly d * (1 - log₂3).
    Since log₂3 ≈ 1.585, each v₂=1 pair contributes ≈ -0.585 to the walk. -/
theorem walk_of_v2_run (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1) :
    walk n (t + 2 * d) = walk n t + ↑d * (1 - logb 2 3) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hrun' : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1 :=
      fun i hi => hrun i (by omega)
    -- IH: walk n (t + 2*d) = walk n t + d * (1 - logb 2 3)
    have ih_val := ih hrun'
    -- Step t+2d is odd, step t+2d+1 is even
    have hodd_d := isOddStep_during_v2_run n t (d + 1) hn hodd hrun d (by omega)
    have heven_d := isEvenStep_during_v2_run n t (d + 1) hn hodd hrun d (by omega)
    -- walk(t+2d+1) = walk(t+2d) - logb 2 3  (odd step)
    have step1 : walk n (t + 2 * d + 1) = walk n (t + 2 * d) - logb 2 3 :=
      walk_step_odd n (t + 2 * d) hodd_d
    -- walk(t+2d+2) = walk(t+2d+1) + 1  (even step)
    have step2 : walk n (t + 2 * d + 2) = walk n (t + 2 * d + 1) + 1 :=
      walk_step_even n (t + 2 * d + 1) heven_d
    -- Combine
    have : t + 2 * (d + 1) = t + 2 * d + 2 := by ring
    rw [this, step2, step1, ih_val]
    push_cast
    ring

open Real in
/-- **Walk deficit (difference form)**: The walk drops by d*(log₂3 - 1)
    during a v₂=1 run of length d. -/
theorem walk_deficit_of_v2_run (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1) :
    walk n (t + 2 * d) - walk n t = ↑d * (1 - logb 2 3) := by
  linarith [walk_of_v2_run n t d hn hodd hrun]

/-! ## Exit recovery: walk gain at the end of a v₂=1 run -/

-- After a maximal v₂=1 run, the exit odd step plus at least 2 even steps
-- contribute (2 - log₂3) ≈ +0.415 to the walk.
-- Requires: the value at time t+2d is odd (end of run), the exit has v₂ ≥ 2
-- (from dangerous_exit_forced), i.e., the step after 3a+1 is still even.

/-- The exit odd step at position t+2d (the value is odd but T gives an even result)
    decreases the walk by log₂3. -/
theorem walk_exit_odd_step (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1) :
    isOddStep n (t + 2 * d) = true := by
  -- The value at t+2d is oddCollatzIter(collatzSeq n t) d, which is odd
  have htrack := collatzSeq_tracks_oddCollatzIter n t d hn hodd hrun d le_rfl
  simp only [isOddStep, decide_eq_true_eq]
  rw [htrack]
  exact hrun d le_rfl

/-- After the exit odd step, the next step is always even (3a+1 is even). -/
theorem walk_exit_first_even (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1) :
    isEvenStep n (t + 2 * d + 1) = true := by
  have hodd_step := walk_exit_odd_step n t d hn hodd hrun
  have hpos := collatzSeq_ne_zero n hn (t + 2 * d)
  have := no_consecutive_odd_steps n (t + 2 * d) hpos hodd_step
  simp only [isEvenStep, isOddStep, decide_eq_true_eq, decide_eq_false_iff_not] at this ⊢
  omega

/-- If the v₂=1 run is maximal (T^d(x) gives an even result), the second
    halving step is also even: 4 | (3a+1) means (3a+1)/2 is still even. -/
theorem walk_exit_second_even (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1)
    (hexit : oddCollatzStep (oddCollatzIter (collatzSeq n t) d) % 2 = 0) :
    isEvenStep n (t + 2 * d + 2) = true := by
  -- The value at t+2d is a = oddCollatzIter(collatzSeq n t) d, odd
  -- collatzSeq n (t+2d+1) = 3a+1 (from odd step)
  -- collatzSeq n (t+2d+2) = (3a+1)/2 = oddCollatzStep a (from even step)
  -- We need (3a+1)/2 to be even, which is the hexit hypothesis
  have htrack := collatzSeq_tracks_oddCollatzIter n t d hn hodd hrun d le_rfl
  have ha_odd : collatzSeq n (t + 2 * d) % 2 = 1 := by
    rw [htrack]; exact hrun d le_rfl
  have ha_pos := collatzSeq_ne_zero n hn (t + 2 * d)
  -- collatzSeq n (t+2d+2) = oddCollatzStep(collatzSeq n (t+2d))
  have hval : collatzSeq n (t + 2 * d + 2) = oddCollatzStep (collatzSeq n (t + 2 * d)) := by
    exact collatzSeq_two_steps n (t + 2 * d) ha_odd ha_pos
  simp only [isEvenStep, decide_eq_true_eq]
  rw [hval, htrack]
  omega

open Real in
/-- **Exit recovery**: After a maximal v₂=1 run of length d, the 3 steps
    (1 odd + 2 even) immediately following the run contribute
    (2 - log₂3) ≈ +0.415 to the walk. -/
theorem walk_exit_recovery (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1)
    (hexit : oddCollatzStep (oddCollatzIter (collatzSeq n t) d) % 2 = 0) :
    walk n (t + 2 * d + 3) = walk n (t + 2 * d) + (2 - logb 2 3) := by
  have h_odd := walk_exit_odd_step n t d hn hodd hrun
  have h_ev1 := walk_exit_first_even n t d hn hodd hrun
  have h_ev2 := walk_exit_second_even n t d hn hodd hrun hexit
  -- walk(t+2d+1) = walk(t+2d) - logb 2 3
  have s1 : walk n (t + 2 * d + 1) = walk n (t + 2 * d) - logb 2 3 :=
    walk_step_odd n (t + 2 * d) h_odd
  -- walk(t+2d+2) = walk(t+2d+1) + 1
  have s2 : walk n (t + 2 * d + 2) = walk n (t + 2 * d + 1) + 1 :=
    walk_step_even n (t + 2 * d + 1) h_ev1
  -- walk(t+2d+3) = walk(t+2d+2) + 1
  have s3 : walk n (t + 2 * d + 3) = walk n (t + 2 * d + 2) + 1 :=
    walk_step_even n (t + 2 * d + 2) h_ev2
  linarith

open Real in
/-- **Net walk for run + exit**: A maximal v₂=1 run of length d followed by
    its 3-step exit changes the walk by d*(1 - log₂3) + (2 - log₂3)
    = (d+1)*(1 - log₂3) + 1 over 2d + 3 uncompressed steps. -/
theorem walk_run_plus_exit (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1)
    (hexit : oddCollatzStep (oddCollatzIter (collatzSeq n t) d) % 2 = 0) :
    walk n (t + 2 * d + 3) = walk n t + ↑(d + 1) * (1 - logb 2 3) + 1 := by
  have h1 := walk_of_v2_run n t d hn hodd hrun
  have h2 := walk_exit_recovery n t d hn hodd hrun hexit
  push_cast at *
  linarith

/-! ## Attrition counting: exact 2^{-d} rate -/

-- We prove that in {0, ..., 2^(d+1) - 1}, there are 2^d odd numbers
-- and exactly 1 of them satisfies 2^(d+1) | (x+1). Hence the attrition
-- rate for d consecutive v₂=1 steps is exactly 1/2^d.

/-- The odd numbers in {0, ..., 2n-1} are exactly {2k+1 | k ∈ {0, ..., n-1}}. -/
theorem odd_range_eq_image (n : ℕ) :
    (Finset.range (2 * n)).filter (fun x => x % 2 = 1) =
    (Finset.range n).image (fun k => 2 * k + 1) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · intro ⟨hlt, hodd⟩
    exact ⟨x / 2, by omega, by omega⟩
  · intro ⟨k, hk, hx⟩
    subst hx
    exact ⟨by omega, by omega⟩

/-- There are exactly 2^d odd numbers in {0, ..., 2^(d+1) - 1}. -/
theorem card_odd_in_period (d : ℕ) :
    ((Finset.range (2 ^ (d + 1))).filter (fun x => x % 2 = 1)).card = 2 ^ d := by
  have h : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
  rw [h, odd_range_eq_image]
  rw [Finset.card_image_of_injective _ (fun a b (hab : 2 * a + 1 = 2 * b + 1) => by omega)]
  exact Finset.card_range _

/-- The survivors (those with 2^(d+1) | (x+1)) among odd numbers in one period
    form the singleton {2^(d+1) - 1}. -/
theorem survivors_eq_singleton (d : ℕ) :
    ((Finset.range (2 ^ (d + 1))).filter (fun x => x % 2 = 1 ∧ (x + 1) % 2 ^ (d + 1) = 0)) =
    {2 ^ (d + 1) - 1} := by
  set p := 2 ^ (d + 1) with hp_def
  have hp_pos : p ≥ 1 := Nat.one_le_pow _ _ (by omega)
  have hp_even : 2 ∣ p := by
    rw [hp_def]; exact dvd_pow_self 2 (by omega : d + 1 ≠ 0)
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · intro ⟨hlt, hodd, hdvd⟩
    -- x + 1 ≡ 0 mod p and x < p, so x + 1 = p
    have hdvd' : p ∣ x + 1 := Nat.dvd_of_mod_eq_zero hdvd
    obtain ⟨k, hk⟩ := hdvd'
    have hk_pos : k ≥ 1 := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hk  -- x + 1 = 0, impossible for ℕ
      · exact h
    -- k = 1 since x + 1 = p * k ≤ p (because x < p)
    have : x + 1 = p := by nlinarith
    omega
  · intro hx; subst hx
    obtain ⟨m, hm⟩ := hp_even
    refine ⟨by omega, by omega, ?_⟩
    -- (p - 1 + 1) % p = p % p = 0
    have : p - 1 + 1 = p := by omega
    rw [this]; exact Nat.mod_self p

/-- There is exactly 1 survivor per period. -/
theorem card_survivors_in_period (d : ℕ) :
    ((Finset.range (2 ^ (d + 1))).filter
      (fun x => x % 2 = 1 ∧ (x + 1) % 2 ^ (d + 1) = 0)).card = 1 := by
  rw [survivors_eq_singleton]
  exact Finset.card_singleton _

/-- **Attrition rate**: Among odd numbers in one period of 2^(d+1),
    exactly 1 out of 2^d satisfies the divisibility condition for
    d consecutive v₂=1 steps. The survival fraction is 2^{-d}. -/
theorem attrition_rate (d : ℕ) :
    ((Finset.range (2 ^ (d + 1))).filter
      (fun x => x % 2 = 1 ∧ (x + 1) % 2 ^ (d + 1) = 0)).card * 2 ^ d =
    ((Finset.range (2 ^ (d + 1))).filter (fun x => x % 2 = 1)).card := by
  rw [card_survivors_in_period, card_odd_in_period]
  ring

/-- Equivalent formulation: survivors = odd_count / 2^d. -/
theorem attrition_rate_div (d : ℕ) :
    ((Finset.range (2 ^ (d + 1))).filter
      (fun x => x % 2 = 1 ∧ (x + 1) % 2 ^ (d + 1) = 0)).card =
    ((Finset.range (2 ^ (d + 1))).filter (fun x => x % 2 = 1)).card / 2 ^ d := by
  rw [card_survivors_in_period, card_odd_in_period]
  exact (Nat.div_self (Nat.one_le_pow _ _ (by omega))).symm

/-- The survivor condition connects back to hensel_attrition via divisibility.
    For odd x in the period, (x+1) % 2^(d+1) = 0 iff 2^(d+1) ∣ (x+1). -/
theorem survivor_iff_dvd (x d : ℕ) :
    (x + 1) % 2 ^ (d + 1) = 0 ↔ 2 ^ (d + 1) ∣ x + 1 := by
  constructor
  · exact Nat.dvd_of_mod_eq_zero
  · intro ⟨k, hk⟩; simp [hk, Nat.mul_mod_right]

/-- **Combined attrition theorem**: Among odd numbers in {0, ..., 2^(d+1)-1},
    the number capable of d consecutive v₂=1 steps is exactly 1.
    By hensel_attrition, these are exactly those with 2^(d+1) | (x+1),
    i.e., only x = 2^(d+1) - 1 in each period. -/
theorem attrition_count (d : ℕ) :
    ((Finset.range (2 ^ (d + 1))).filter
      (fun x => x % 2 = 1 ∧ 2 ^ (d + 1) ∣ x + 1)).card = 1 := by
  -- Convert divisibility to modular form
  have : (Finset.range (2 ^ (d + 1))).filter
      (fun x => x % 2 = 1 ∧ 2 ^ (d + 1) ∣ x + 1) =
    (Finset.range (2 ^ (d + 1))).filter
      (fun x => x % 2 = 1 ∧ (x + 1) % 2 ^ (d + 1) = 0) := by
    congr 1; ext x; simp [survivor_iff_dvd]
  rw [this, card_survivors_in_period]

-- Concrete examples
example : ((Finset.range 4).filter (fun x => x % 2 = 1 ∧ 4 ∣ x + 1)).card = 1 := by
  native_decide

-- d=1: period 4, odd = {1,3}, survivor = {3} (3+1=4, so 4|4). Rate = 1/2.
example : ((Finset.range 4).filter (fun x => x % 2 = 1)).card = 2 := by native_decide

-- d=2: period 8, odd = {1,3,5,7}, survivor = {7} (7+1=8, so 8|8). Rate = 1/4.
example : ((Finset.range 8).filter (fun x => x % 2 = 1 ∧ 8 ∣ x + 1)).card = 1 := by
  native_decide
example : ((Finset.range 8).filter (fun x => x % 2 = 1)).card = 4 := by native_decide

-- d=3: period 16, odd = {1,3,...,15}, survivor = {15}. Rate = 1/8.
example : ((Finset.range 16).filter (fun x => x % 2 = 1 ∧ 16 ∣ x + 1)).card = 1 := by
  native_decide
example : ((Finset.range 16).filter (fun x => x % 2 = 1)).card = 8 := by native_decide

/-! ## Deficit: integer-valued K-bound tracking -/

/-- The deficit: deficit(n,t) = 3·ν₃(n,t) - t.
    K-bound (3·ν₃ ≤ t + K) is equivalent to deficit bounded above. -/
def deficit (n t : ℕ) : ℤ := 3 * (nu3 n t : ℤ) - ↑t

@[simp] theorem deficit_zero (n : ℕ) : deficit n 0 = 0 := by
  simp [deficit]

/-- At an odd step, deficit increases by 2 (ν₃ +1, t +1: net 3·1 - 1 = 2). -/
theorem deficit_step_odd (n t : ℕ) (ho : isOddStep n t = true) :
    deficit n (t + 1) = deficit n t + 2 := by
  simp only [deficit, nu3_step_odd n t ho]; push_cast; ring

/-- At an even step, deficit decreases by 1 (ν₃ unchanged, t +1: net -1). -/
theorem deficit_step_even (n t : ℕ) (he : isEvenStep n t = true) :
    deficit n (t + 1) = deficit n t - 1 := by
  simp only [deficit, nu3_step_even n t he]; push_cast; ring

/-- Deficit is at most 2t (since ν₃ ≤ t). -/
theorem deficit_le_two_mul_t (n t : ℕ) : deficit n t ≤ 2 * (↑t : ℤ) := by
  unfold deficit
  have : nu3 n t ≤ t := by have := nu_partition n t; omega
  omega

/-- During a v₂=1 run of d compressed steps (2d uncompressed), deficit increases by d. -/
theorem deficit_of_v2_run (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1) :
    deficit n (t + 2 * d) = deficit n t + ↑d := by
  simp only [deficit, nu3_of_v2_run n t d hn hodd hrun]; push_cast; ring

/-- A maximal v₂=1 run of d steps plus 3-step exit: deficit increases by d.
    The exit (1 odd + 2 even) has net deficit change +2 - 1 - 1 = 0. -/
theorem deficit_of_run_plus_exit (n t d : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1)
    (hrun : ∀ i, i ≤ d → oddCollatzIter (collatzSeq n t) i % 2 = 1)
    (hexit : oddCollatzStep (oddCollatzIter (collatzSeq n t) d) % 2 = 0) :
    deficit n (t + 2 * d + 3) = deficit n t + ↑d := by
  have h_odd := walk_exit_odd_step n t d hn hodd hrun
  have h_ev1 := walk_exit_first_even n t d hn hodd hrun
  have h_ev2 := walk_exit_second_even n t d hn hodd hrun hexit
  have hnu_run := nu3_of_v2_run n t d hn hodd hrun
  have s1 := nu3_step_odd n (t + 2 * d) h_odd
  have s2 : nu3 n (t + 2 * d + 2) = nu3 n (t + 2 * d + 1) := by
    rw [show t + 2 * d + 2 = (t + 2 * d + 1) + 1 from by omega]
    exact nu3_step_even n (t + 2 * d + 1) h_ev1
  have s3 : nu3 n (t + 2 * d + 3) = nu3 n (t + 2 * d + 2) := by
    rw [show t + 2 * d + 3 = (t + 2 * d + 2) + 1 from by omega]
    exact nu3_step_even n (t + 2 * d + 2) h_ev2
  simp only [deficit, s3, s2, s1, hnu_run]; push_cast; ring

/-- Safe compressed step (1 odd + ≥2 even): deficit non-increasing. -/
theorem deficit_nonincreasing_at_safe_step (n t : ℕ)
    (ho : isOddStep n t = true) (he1 : isEvenStep n (t + 1) = true)
    (he2 : isEvenStep n (t + 2) = true) :
    deficit n (t + 3) ≤ deficit n t := by
  have s1 := deficit_step_odd n t ho
  have s2 : deficit n (t + 2) = deficit n (t + 1) - 1 := by
    rw [show t + 2 = (t + 1) + 1 from by omega]
    exact deficit_step_even n (t + 1) he1
  have s3 : deficit n (t + 3) = deficit n (t + 2) - 1 := by
    rw [show t + 3 = (t + 2) + 1 from by omega]
    exact deficit_step_even n (t + 2) he2
  omega

open Real in
/-- The walk expressed via deficit:
    walk = ((2 - logb 2 3) * t - (1 + logb 2 3) * deficit) / 3. -/
theorem walk_eq_deficit_form (n t : ℕ) :
    walk n t = ((2 - logb 2 3) * ↑t - (1 + logb 2 3) * (deficit n t : ℝ)) / 3 := by
  have hpart : (nu2 n t : ℝ) = ↑t - ↑(nu3 n t) := by
    have h := nu_partition n t
    have h' : (↑(nu2 n t) : ℝ) + ↑(nu3 n t) = ↑t := by exact_mod_cast h
    linarith
  have hdef : (deficit n t : ℝ) = 3 * ↑(nu3 n t) - ↑t := by
    simp only [deficit]; push_cast; ring
  simp only [walk]; rw [hpart, hdef]; ring

-- Concrete verification
example : deficit 7 0 = 0 := by native_decide
example : deficit 7 16 = -1 := by native_decide

end Collatz
