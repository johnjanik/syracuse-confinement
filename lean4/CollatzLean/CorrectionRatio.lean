/-
  CollatzLean/CorrectionRatio.lean
  The correction ratio r(t) = correction(n,t) / 2^ν₂(n,t) and its properties.

  Key result: if the walk has eventually linear drift, then the Collatz
  sequence is eventually bounded.  This replaces the false `correction_bound`
  (which claimed correction/3^ν₃ is bounded — it isn't) with the correct
  ratio correction/2^ν₂, which IS bounded when the walk has positive drift.

  See docs/correction_ratio_bound.tex for the full mathematical argument.
-/
import CollatzLean.Identity
import CollatzLean.Drift
import CollatzLean.CollatzSFT
import CollatzLean.Baker
import CollatzLean.SteinerCycle
import Mathlib.Data.Fintype.Pigeonhole

namespace Collatz

open Real

/-! ## Correction ratio recurrence

The correction ratio r(t) = C(t)/2^ν₂ satisfies:
  - Even step: r → r/2
  - Odd step: r → 3r + 1
This is the same arithmetic as the Collatz map, but driven by the parity
of collatzSeq(n,t), not by r(t) itself.

We work with the cleared-denominator form to stay in ℕ:
  correction(n,t) and 2^(nu2 n t)
and derive the key inequality on collatzSeq from these. -/

/-- At an even step, correction is unchanged and 2^ν₂ doubles.
    So correction / 2^ν₂ halves (cleared form: same numerator, larger denominator). -/
theorem correction_ratio_even (n t : ℕ) (he : isEvenStep n t = true) :
    correction n (t + 1) = correction n t ∧
    2 ^ nu2 n (t + 1) = 2 ^ nu2 n t * 2 := by
  exact ⟨correction_succ_even n t he, by rw [nu2_step_even n t he, pow_succ]⟩

/-- At an odd step, correction triples plus 2^ν₂, and 2^ν₂ stays.
    So correction / 2^ν₂ → 3 * (correction / 2^ν₂) + 1. -/
theorem correction_ratio_odd (n t : ℕ) (ho : isOddStep n t = true) :
    correction n (t + 1) = 3 * correction n t + 2 ^ nu2 n t ∧
    nu2 n (t + 1) = nu2 n t := by
  exact ⟨correction_succ_odd n t ho, nu2_step_odd n t ho⟩

/-! ## Trajectory bound from linear drift

The core result: if walk(n,t) ≥ ε·t for t ≥ T₀, then collatzSeq(n,t)
is eventually bounded.

Strategy: from the identity  a(t) · 2^ν₂ = n · 3^ν₃ + C(t),
we get  a(t) = n · 3^ν₃/2^ν₂ + C(t)/2^ν₂.

Walk divergence gives 3^ν₃/2^ν₂ → 0.  The geometric series argument
(see correction_ratio_bound.tex §3) shows C(t)/2^ν₂ is bounded.
Therefore a(t) is bounded.

For the Lean formalization, we work directly with the ℕ inequality:
  collatzSeq n t ≤ B  ↔  n · 3^ν₃ + C(t) ≤ B · 2^ν₂
and prove the RHS for large t. -/

/-- From the multiplicative identity: collatzSeq n t ≤ (n * 3^ν₃ + correction) / 2^ν₂.
    Since collatzSeq * 2^ν₂ = n * 3^ν₃ + correction exactly, this is an equality,
    but the ≤ form is what we need for bounding. -/
theorem collatzSeq_le_of_identity (n t : ℕ) (_hn : n ≥ 1) :
    collatzSeq n t * 2 ^ nu2 n t = n * 3 ^ nu3 n t + correction n t :=
  collatz_identity n t

/-- Universal bound: the identity's RHS never exceeds n * 4^ν₃.
    By induction: base is trivial; even step preserves; odd step uses
    2^ν₂ ≤ a(t)·2^ν₂ = n·3^ν₃ + C ≤ n·4^ν₃ (IH). -/
theorem identity_le_four_pow_nu3 (n : ℕ) (hn : n ≥ 1) (t : ℕ) :
    n * 3 ^ nu3 n t + correction n t ≤ n * 4 ^ nu3 n t := by
  induction t with
  | zero => simp [nu3, correction]
  | succ t ih =>
    rcases even_or_odd_step n t with he | ho
    · -- Even: correction and nu3 unchanged
      rw [correction_succ_even n t he, nu3_step_even n t he]; exact ih
    · -- Odd: correction → 3C + 2^ν₂, nu3 → ν₃ + 1
      rw [correction_succ_odd n t ho, nu3_step_odd n t ho]
      -- 2^ν₂ ≤ n*4^ν₃ (from a(t) ≥ 1 + identity + IH)
      have h2 : 2 ^ nu2 n t ≤ n * 4 ^ nu3 n t :=
        calc 2 ^ nu2 n t
            ≤ collatzSeq n t * 2 ^ nu2 n t :=
              Nat.le_mul_of_pos_left _ (collatzSeq_pos n hn t)
          _ = n * 3 ^ nu3 n t + correction n t := collatz_identity n t
          _ ≤ n * 4 ^ nu3 n t := ih
      -- 3*(n*3^ν + C) + 2^ν₂ ≤ 3*(n*4^ν) + n*4^ν = n*4^(ν+1)
      calc n * 3 ^ (nu3 n t + 1) + (3 * correction n t + 2 ^ nu2 n t)
          = 3 * (n * 3 ^ nu3 n t + correction n t) + 2 ^ nu2 n t := by
            rw [pow_succ]; ring
        _ ≤ 3 * (n * 4 ^ nu3 n t) + n * 4 ^ nu3 n t := by linarith
        _ = n * 4 ^ (nu3 n t + 1) := by rw [pow_succ]; ring

/-- If 3·ν₃ ≤ t + K for large t, then collatzSeq(n,t) ≤ n·2^K.

    From the universal bound: a(t)·2^ν₂ ≤ n·4^ν₃ = n·2^{2ν₃}.
    From 3ν₃ ≤ t+K and ν₂ = t−ν₃: 2ν₃ ≤ ν₂+K.
    So a(t)·2^ν₂ ≤ n·2^{ν₂+K}, giving a(t) ≤ n·2^K. -/
theorem collatzSeq_eventually_bounded_of_linear_drift (n : ℕ) (hn : n ≥ 1)
    (K T₀ : ℕ) (hbound : ∀ t, t ≥ T₀ → 3 * nu3 n t ≤ t + K) :
    ∃ B : ℕ, ∃ T₁ : ℕ, T₁ ≥ T₀ ∧ ∀ t, t ≥ T₁ → collatzSeq n t ≤ B := by
  refine ⟨n * 2 ^ K, T₀, le_refl _, fun t ht => ?_⟩
  -- From universal bound + identity: a(t) * 2^ν₂ ≤ n * 4^ν₃
  have h1 : collatzSeq n t * 2 ^ nu2 n t ≤ n * 4 ^ nu3 n t :=
    calc collatzSeq n t * 2 ^ nu2 n t
        = n * 3 ^ nu3 n t + correction n t := collatz_identity n t
      _ ≤ n * 4 ^ nu3 n t := identity_le_four_pow_nu3 n hn t
  -- From hypothesis: 2*ν₃ ≤ ν₂ + K  (since 3ν₃ ≤ t+K and ν₂ = t-ν₃)
  have hpart := nu_partition n t
  have h3 := hbound t ht
  have h2nu3 : 2 * nu3 n t ≤ nu2 n t + K := by omega
  -- So 4^ν₃ = 2^{2ν₃} ≤ 2^{ν₂+K}, giving a(t)*2^ν₂ ≤ n*2^{ν₂+K}
  have h4 : (4 : ℕ) ^ nu3 n t ≤ 2 ^ K * 2 ^ nu2 n t :=
    calc (4 : ℕ) ^ nu3 n t = (2 ^ 2) ^ nu3 n t := by norm_num
      _ = 2 ^ (2 * nu3 n t) := by rw [← pow_mul]
      _ ≤ 2 ^ (nu2 n t + K) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ nu2 n t * 2 ^ K := by rw [pow_add]
      _ = 2 ^ K * 2 ^ nu2 n t := by ring
  -- Cancel 2^ν₂
  have h5 : collatzSeq n t * 2 ^ nu2 n t ≤ n * 2 ^ K * 2 ^ nu2 n t :=
    calc collatzSeq n t * 2 ^ nu2 n t
        ≤ n * 4 ^ nu3 n t := h1
      _ ≤ n * (2 ^ K * 2 ^ nu2 n t) := Nat.mul_le_mul_left n h4
      _ = n * 2 ^ K * 2 ^ nu2 n t := by ring
  exact Nat.le_of_mul_le_mul_right h5 (Nat.pos_of_ne_zero (by positivity))

/-! ## Eventual periodicity

From the trajectory bound, the Collatz sequence takes finitely many values
for large t, hence is eventually periodic by pigeonhole. -/

/-- Equal Collatz values propagate forward: if the sequence agrees at two
    times, it agrees at all later offsets (since collatzSeq is just iteration). -/
private theorem collatzSeq_shift_eq (n t₁ t₂ : ℕ)
    (h : collatzSeq n t₁ = collatzSeq n t₂) (k : ℕ) :
    collatzSeq n (t₁ + k) = collatzSeq n (t₂ + k) := by
  induction k with
  | zero => simpa
  | succ k ih =>
    change collatz (collatzSeq n (t₁ + k)) = collatz (collatzSeq n (t₂ + k))
    rw [ih]

/-- A bounded Collatz trajectory is eventually periodic. -/
theorem collatzSeq_eventually_periodic_of_bounded (n : ℕ) (_hn : n ≥ 1)
    (B T₁ : ℕ) (hB : ∀ t, t ≥ T₁ → collatzSeq n t ≤ B) :
    ∃ T₂ : ℕ, ∃ p : ℕ, p ≥ 1 ∧ T₂ ≥ T₁ ∧ ∀ t, t ≥ T₂ → collatzSeq n (t + p) = collatzSeq n t := by
  -- Pigeonhole: B+2 consecutive values map to B+1 possible outputs
  let f : Fin (B + 2) → Fin (B + 1) := fun i =>
    ⟨collatzSeq n (T₁ + i.val), by have := hB (T₁ + i.val) (by omega); omega⟩
  obtain ⟨i, j, hij, hfij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f (by simp [Fintype.card_fin])
  -- Extract that the trajectory values are equal
  have heq : collatzSeq n (T₁ + i.val) = collatzSeq n (T₁ + j.val) :=
    congrArg Fin.val hfij
  have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
  -- Take the smaller index as start, difference as period
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- i.val < j.val
    refine ⟨T₁ + i.val, j.val - i.val, by omega, by omega, ?_⟩
    intro t ht
    have hk := collatzSeq_shift_eq n (T₁ + i.val) (T₁ + j.val) heq (t - (T₁ + i.val))
    rw [Nat.add_sub_cancel' (show T₁ + i.val ≤ t by omega)] at hk
    rw [show T₁ + j.val + (t - (T₁ + i.val)) = t + (j.val - i.val) from by omega] at hk
    exact hk.symm
  · -- j.val < i.val
    refine ⟨T₁ + j.val, i.val - j.val, by omega, by omega, ?_⟩
    intro t ht
    have hk := collatzSeq_shift_eq n (T₁ + j.val) (T₁ + i.val) heq.symm (t - (T₁ + j.val))
    rw [Nat.add_sub_cancel' (show T₁ + j.val ≤ t by omega)] at hk
    rw [show T₁ + i.val + (t - (T₁ + j.val)) = t + (i.val - j.val) from by omega] at hk
    exact hk.symm

/-! ## Cycle elimination (Δ₃ = 1)

The only Collatz cycle with exactly one odd step per period is {1, 2, 4}.
This follows from the cycle equation: c₀ = 2^e₁ / (2^Δ₂ - 3).
For c₀ to be a positive integer, 2^Δ₂ - 3 must divide a power of 2,
forcing 2^Δ₂ - 3 = 1, hence Δ₂ = 2, c₀ ∈ {1, 2, 4}. -/

set_option linter.unusedVariables false in
/-- In the trivial cycle 1 → 4 → 2 → 1, the sequence reaches 1. -/
theorem reaches_one_of_cycle_142 (n : ℕ) (hn : n ≥ 1)
    (T₂ p : ℕ) (hp : p ≥ 1)
    (hperiodic : ∀ t, t ≥ T₂ → collatzSeq n (t + p) = collatzSeq n t)
    (hone : ∃ t, t ≥ T₂ ∧ collatzSeq n t = 1) :
    collatzReaches n := by
  obtain ⟨t, _, ht1⟩ := hone
  exact ⟨t, ht1⟩

/-! ## Odd-step counting infrastructure -/

/-- Number of odd steps in the window [T₂, T₂ + p). -/
def oddStepsInPeriod (n T₂ p : ℕ) : ℕ :=
  ((Finset.range p).filter (fun i => isOddStep n (T₂ + i))).card

/-! ## Periodicity infrastructure for nu3/nu2 over cycles -/

/-- isOddStep is periodic when the trajectory is periodic. -/
private theorem isOddStep_periodic (n T₂ p : ℕ)
    (hperiodic : ∀ t, t ≥ T₂ → collatzSeq n (t + p) = collatzSeq n t)
    (t : ℕ) (ht : t ≥ T₂) : isOddStep n (t + p) = isOddStep n t := by
  simp only [isOddStep, hperiodic t ht]

/-- oddStepsInPeriod satisfies the expected recurrence at the successor. -/
private theorem oddStepsInPeriod_succ (n T₂ p : ℕ) :
    oddStepsInPeriod n T₂ (p + 1) = oddStepsInPeriod n T₂ p +
      if isOddStep n (T₂ + p) then 1 else 0 := by
  simp only [oddStepsInPeriod, Finset.range_add_one, Finset.filter_insert]
  have hmem : p ∉ (Finset.range p).filter (fun i => isOddStep n (T₂ + i)) := by
    simp [Finset.mem_filter, Finset.mem_range]
  by_cases ho : (isOddStep n (T₂ + p) : Prop)
  · simp only [if_pos ho, Finset.card_insert_of_notMem hmem, ite_true]
  · simp only [if_neg ho, ite_false, Nat.add_zero]

/-- ν₃ increases by oddStepsInPeriod over a window of length p. -/
private theorem nu3_add_period (n T₂ p : ℕ) :
    nu3 n (T₂ + p) = nu3 n T₂ + oddStepsInPeriod n T₂ p := by
  induction p with
  | zero => simp [oddStepsInPeriod, Finset.filter_empty]
  | succ p ih =>
    rw [show T₂ + (p + 1) = (T₂ + p) + 1 from by omega]
    have hsucc := oddStepsInPeriod_succ n T₂ p
    rcases even_or_odd_step n (T₂ + p) with he | ho
    · rw [nu3_step_even n (T₂ + p) he, ih]
      have : ¬(isOddStep n (T₂ + p) : Prop) := by
        simp only [isEvenStep, isOddStep, decide_eq_true_eq] at he ⊢; omega
      simp [this] at hsucc; omega
    · rw [nu3_step_odd n (T₂ + p) ho, ih]
      have : (isOddStep n (T₂ + p) : Prop) := by
        simp only [isOddStep, decide_eq_true_eq] at ho ⊢; exact ho
      simp [this] at hsucc; omega

/-- oddStepsInPeriod is invariant under shifting T₂ by p (periodicity). -/
private theorem oddStepsInPeriod_shift (n T₂ p : ℕ)
    (hperiodic : ∀ t, t ≥ T₂ → collatzSeq n (t + p) = collatzSeq n t) :
    oddStepsInPeriod n (T₂ + p) p = oddStepsInPeriod n T₂ p := by
  simp only [oddStepsInPeriod]
  congr 1; ext i
  simp only [Finset.mem_filter]
  constructor
  · intro ⟨hi, hodd⟩
    refine ⟨hi, ?_⟩
    rwa [show T₂ + p + i = (T₂ + i) + p from by omega,
         isOddStep_periodic n T₂ p hperiodic (T₂ + i) (by omega)] at hodd
  · intro ⟨hi, hodd⟩
    refine ⟨hi, ?_⟩
    rwa [show T₂ + p + i = (T₂ + i) + p from by omega,
         isOddStep_periodic n T₂ p hperiodic (T₂ + i) (by omega)]

/-- ν₃ after k full periods: ν₃(T₂ + k·p) = ν₃(T₂) + k · Δ₃. -/
private theorem nu3_add_kperiods (n T₂ p k : ℕ)
    (hperiodic : ∀ t, t ≥ T₂ → collatzSeq n (t + p) = collatzSeq n t) :
    nu3 n (T₂ + k * p) = nu3 n T₂ + k * oddStepsInPeriod n T₂ p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * p = k * p + p from by ring,
        show T₂ + (k * p + p) = (T₂ + k * p) + p from by omega,
        nu3_add_period n (T₂ + k * p) p]
    -- oddStepsInPeriod at T₂+k*p equals oddStepsInPeriod at T₂
    suffices oddStepsInPeriod n (T₂ + k * p) p = oddStepsInPeriod n T₂ p by
      rw [ih, this]; ring
    -- By induction: shift by p, k times
    clear ih
    induction k with
    | zero => simp
    | succ k ihk =>
      rw [show (k + 1) * p = k * p + p from by ring,
          show T₂ + (k * p + p) = (T₂ + k * p) + p from by omega,
          oddStepsInPeriod_shift n (T₂ + k * p) p
            (fun t ht => hperiodic t (by omega)),
          ihk]

/-- ν₂ after k full periods (additive form): ν₂(T₂+k·p) + k·Δ₃ = ν₂(T₂) + k·p. -/
private theorem nu2_add_kperiods (n T₂ p k : ℕ)
    (hperiodic : ∀ t, t ≥ T₂ → collatzSeq n (t + p) = collatzSeq n t) :
    nu2 n (T₂ + k * p) + k * oddStepsInPeriod n T₂ p = nu2 n T₂ + k * p := by
  have h3 := nu3_add_kperiods n T₂ p k hperiodic
  have hpart1 := nu_partition n (T₂ + k * p)
  have hpart2 := nu_partition n T₂
  omega

/-- If there are no odd steps in a period, every step is even. -/
private theorem all_even_of_delta3_zero (n T₂ p : ℕ)
    (h : oddStepsInPeriod n T₂ p = 0) :
    ∀ i, i < p → isEvenStep n (T₂ + i) = true := by
  intro i hip
  rcases even_or_odd_step n (T₂ + i) with he | ho
  · exact he
  · exfalso
    have hmem : i ∈ (Finset.range p).filter (fun j => isOddStep n (T₂ + j)) := by
      simp [Finset.mem_filter, Finset.mem_range]; exact ⟨hip, ho⟩
    have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
    rw [oddStepsInPeriod] at h; omega

/-- Correction is unchanged over an all-even stretch. -/
private theorem correction_unchanged_of_all_even (n T₂ k : ℕ)
    (h : ∀ i, i < k → isEvenStep n (T₂ + i) = true) :
    correction n (T₂ + k) = correction n T₂ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show T₂ + (k + 1) = (T₂ + k) + 1 from by omega,
        correction_succ_even n (T₂ + k) (h k (by omega)),
        ih (fun i hi => h i (by omega))]

/-- ν₃ is unchanged over an all-even stretch. -/
private theorem nu3_unchanged_of_all_even (n T₂ k : ℕ)
    (h : ∀ i, i < k → isEvenStep n (T₂ + i) = true) :
    nu3 n (T₂ + k) = nu3 n T₂ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show T₂ + (k + 1) = (T₂ + k) + 1 from by omega,
        nu3_step_even n (T₂ + k) (h k (by omega)),
        ih (fun i hi => h i (by omega))]

/-- ν₂ increases by the stretch length over an all-even stretch. -/
private theorem nu2_increases_of_all_even (n T₂ k : ℕ)
    (h : ∀ i, i < k → isEvenStep n (T₂ + i) = true) :
    nu2 n (T₂ + k) = nu2 n T₂ + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show T₂ + (k + 1) = (T₂ + k) + 1 from by omega,
        nu2_step_even n (T₂ + k) (h k (by omega)),
        ih (fun i hi => h i (by omega))]
    omega

/-! ## Δ₃ = 0 case: impossible -/

/-- A cycle with no odd steps is impossible: the identity forces 2^p = 1. -/
private theorem no_cycle_delta3_zero (n : ℕ) (hn : n ≥ 1)
    (T₂ p : ℕ) (hp : p ≥ 1)
    (hperiodic : collatzSeq n (T₂ + p) = collatzSeq n T₂)
    (hdelta : oddStepsInPeriod n T₂ p = 0) : False := by
  have hall := all_even_of_delta3_zero n T₂ p hdelta
  have hcorr := correction_unchanged_of_all_even n T₂ p hall
  have hnu3 := nu3_unchanged_of_all_even n T₂ p hall
  have hnu2 := nu2_increases_of_all_even n T₂ p hall
  have id1 := collatz_identity n T₂
  have id2 := collatz_identity n (T₂ + p)
  rw [hperiodic, hcorr, hnu3, hnu2, pow_add] at id2
  -- id2: c * (2^ν * 2^p) = n * 3^ν₃ + C = c * 2^ν  [by id1]
  have h_eq : collatzSeq n T₂ * 2 ^ nu2 n T₂ * 2 ^ p =
              collatzSeq n T₂ * 2 ^ nu2 n T₂ := by linarith [mul_assoc (collatzSeq n T₂) (2 ^ nu2 n T₂) (2 ^ p)]
  have hM_pos : 0 < collatzSeq n T₂ * 2 ^ nu2 n T₂ := by
    have := collatzSeq_pos n hn T₂; positivity
  have hM_ne : collatzSeq n T₂ * 2 ^ nu2 n T₂ ≠ 0 := by omega
  have h2p : 2 ^ p = 1 := mul_left_cancel₀ hM_ne (by linarith [mul_one (collatzSeq n T₂ * 2 ^ nu2 n T₂)])
  have : 2 ^ p ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hp
  omega

/-! ## Δ₃ = 1 case: only {1,2,4} -/

/-- When there is exactly one odd step in a period, extract its position. -/
private theorem exists_unique_odd_step (n T₂ p : ℕ)
    (h : oddStepsInPeriod n T₂ p = 1) :
    ∃ s, s < p ∧ isOddStep n (T₂ + s) = true ∧
      ∀ i, i < p → i ≠ s → isEvenStep n (T₂ + i) = true := by
  rw [oddStepsInPeriod, Finset.card_eq_one] at h
  obtain ⟨a, ha⟩ := h
  have ha_mem : a ∈ (Finset.range p).filter (fun i => isOddStep n (T₂ + i)) :=
    ha ▸ Finset.mem_singleton_self a
  simp [Finset.mem_filter, Finset.mem_range] at ha_mem
  refine ⟨a, ha_mem.1, ha_mem.2, ?_⟩
  intro i hip hia
  rcases even_or_odd_step n (T₂ + i) with he | ho
  · exact he
  · exfalso
    have : i ∈ (Finset.range p).filter (fun j => isOddStep n (T₂ + j)) := by
      simp [Finset.mem_filter, Finset.mem_range]; exact ⟨hip, ho⟩
    rw [ha] at this; simp at this; exact hia this

/-- Helper: even-step condition for the second stretch after the odd step. -/
private theorem even_stretch_after_odd (n T₂ p s : ℕ) (hs : s < p)
    (heven : ∀ i, i < p → i ≠ s → isEvenStep n (T₂ + i) = true) :
    ∀ i, i < (p - s - 1) → isEvenStep n ((T₂ + s + 1) + i) = true := by
  intro i hi
  have h1 : s + 1 + i < p := by omega
  have h2 : s + 1 + i ≠ s := by omega
  have := heven (s + 1 + i) h1 h2
  convert this using 2; omega

/-- Correction over one period with exactly one odd step at position s. -/
private theorem correction_one_odd_step (n T₂ p s : ℕ) (hs : s < p)
    (hodd_s : isOddStep n (T₂ + s) = true)
    (heven : ∀ i, i < p → i ≠ s → isEvenStep n (T₂ + i) = true) :
    correction n (T₂ + p) = 3 * correction n T₂ + 2 ^ (nu2 n T₂ + s) := by
  have heven1 : ∀ i, i < s → isEvenStep n (T₂ + i) = true :=
    fun i hi => heven i (by omega) (by omega)
  have heven2 := even_stretch_after_odd n T₂ p s hs heven
  have hc1 := correction_unchanged_of_all_even n T₂ s heven1
  have hnu2_1 := nu2_increases_of_all_even n T₂ s heven1
  have hc2 := correction_succ_odd n (T₂ + s) hodd_s
  have hc3 := correction_unchanged_of_all_even n (T₂ + s + 1) (p - s - 1) heven2
  rw [show T₂ + s + 1 + (p - s - 1) = T₂ + p from by omega] at hc3
  rw [hc3, hc2, hc1, hnu2_1]

/-- ν₂ over one period with exactly one odd step: increases by p - 1. -/
private theorem nu2_one_odd_step (n T₂ p s : ℕ) (hs : s < p)
    (hodd_s : isOddStep n (T₂ + s) = true)
    (heven : ∀ i, i < p → i ≠ s → isEvenStep n (T₂ + i) = true) :
    nu2 n (T₂ + p) = nu2 n T₂ + (p - 1) := by
  have heven1 : ∀ i, i < s → isEvenStep n (T₂ + i) = true :=
    fun i hi => heven i (by omega) (by omega)
  have heven2 := even_stretch_after_odd n T₂ p s hs heven
  have h1 := nu2_increases_of_all_even n T₂ s heven1
  have h2 := nu2_step_odd n (T₂ + s) hodd_s
  have h3 := nu2_increases_of_all_even n (T₂ + s + 1) (p - s - 1) heven2
  rw [show T₂ + s + 1 + (p - s - 1) = T₂ + p from by omega] at h3
  rw [h3, h2, h1]; omega

/-- ν₃ over one period with exactly one odd step: increases by 1. -/
private theorem nu3_one_odd_step (n T₂ p s : ℕ) (hs : s < p)
    (hodd_s : isOddStep n (T₂ + s) = true)
    (heven : ∀ i, i < p → i ≠ s → isEvenStep n (T₂ + i) = true) :
    nu3 n (T₂ + p) = nu3 n T₂ + 1 := by
  have heven1 : ∀ i, i < s → isEvenStep n (T₂ + i) = true :=
    fun i hi => heven i (by omega) (by omega)
  have heven2 := even_stretch_after_odd n T₂ p s hs heven
  have h1 := nu3_unchanged_of_all_even n T₂ s heven1
  have h2 := nu3_step_odd n (T₂ + s) hodd_s
  have h3 := nu3_unchanged_of_all_even n (T₂ + s + 1) (p - s - 1) heven2
  rw [show T₂ + s + 1 + (p - s - 1) = T₂ + p from by omega] at h3
  rw [h3, h2, h1]

/-- The cycle equation for Δ₃ = 1: c₀ · 2^(p-1) = 3·c₀ + 2^s. -/
private theorem cycle_equation_delta3_one (n T₂ p s : ℕ)
    (hperiodic : collatzSeq n (T₂ + p) = collatzSeq n T₂)
    (hs : s < p)
    (hodd_s : isOddStep n (T₂ + s) = true)
    (heven : ∀ i, i < p → i ≠ s → isEvenStep n (T₂ + i) = true) :
    collatzSeq n T₂ * 2 ^ (p - 1) = 3 * collatzSeq n T₂ + 2 ^ s := by
  have id1 := collatz_identity n T₂
  have id2 := collatz_identity n (T₂ + p)
  have hnu2 := nu2_one_odd_step n T₂ p s hs hodd_s heven
  have hnu3 := nu3_one_odd_step n T₂ p s hs hodd_s heven
  have hcorr := correction_one_odd_step n T₂ p s hs hodd_s heven
  rw [hperiodic, hnu2, hnu3, hcorr] at id2
  -- id2: c * 2^(ν+q) = n * 3^(ν₃+1) + (3*C + 2^(ν+s))  where q = p-1
  -- Suffices to cancel 2^ν from both sides of:
  --   2^ν * (c * 2^q) = 2^ν * (3*c + 2^s)
  suffices h : 2 ^ nu2 n T₂ * (collatzSeq n T₂ * 2 ^ (p - 1)) =
               2 ^ nu2 n T₂ * (3 * collatzSeq n T₂ + 2 ^ s) from
    mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℕ) ≠ 0)) h
  -- LHS: c * 2^(ν+q) = 2^ν * (c * 2^q)
  have lhs : collatzSeq n T₂ * 2 ^ (nu2 n T₂ + (p - 1)) =
             2 ^ nu2 n T₂ * (collatzSeq n T₂ * 2 ^ (p - 1)) := by
    rw [pow_add]; ring
  -- RHS from id1 and id2
  have rhs : n * 3 ^ (nu3 n T₂ + 1) + (3 * correction n T₂ + 2 ^ (nu2 n T₂ + s)) =
             3 * (n * 3 ^ nu3 n T₂ + correction n T₂) + 2 ^ nu2 n T₂ * 2 ^ s := by
    rw [pow_succ, pow_add]; ring
  -- Goal: 2^ν * (c * 2^q) = 2^ν * (3c + 2^s)
  -- By lhs: LHS = c * 2^(ν+q) = id2.LHS
  -- By rhs and id1: RHS = 3*(c * 2^ν) + 2^ν * 2^s
  rw [← lhs]
  -- Goal: c * 2^(ν+q) = 2^ν * (3c + 2^s)
  rw [id2]
  -- Goal: n * 3^(ν₃+1) + (3*C + 2^(ν+s)) = 2^ν * (3c + 2^s)
  rw [rhs, ← id1]
  -- Goal: 3*(c*2^ν) + 2^ν*2^s = 2^ν * (3c + 2^s)
  ring

/-- If d is odd and d ∣ 2^k, then d = 1. -/
private theorem odd_dvd_pow_two_eq_one {d k : ℕ}
    (hd_odd : d % 2 = 1) (hdvd : d ∣ 2 ^ k) : d = 1 := by
  have hcop : Nat.Coprime d (2 ^ k) :=
    Nat.Coprime.pow_right k
      (by rw [Nat.coprime_comm, Nat.coprime_two_left]; exact ⟨d / 2, by omega⟩)
  have h1 : d ∣ Nat.gcd d (2 ^ k) := Nat.dvd_gcd dvd_rfl hdvd
  rw [hcop] at h1
  exact Nat.eq_one_of_dvd_one h1

/-- The main Δ₃ = 1 result: the cycle contains 1. -/
private theorem cycle_contains_one_of_delta3_one (n : ℕ) (hn : n ≥ 1)
    (T₂ p : ℕ) (hp : p ≥ 1)
    (hperiodic : ∀ t, t ≥ T₂ → collatzSeq n (t + p) = collatzSeq n t)
    (hdelta : oddStepsInPeriod n T₂ p = 1) :
    ∃ t, t ≥ T₂ ∧ collatzSeq n t = 1 := by
  obtain ⟨s, hs, hodd_s, heven⟩ := exists_unique_odd_step n T₂ p hdelta
  have hceq := cycle_equation_delta3_one n T₂ p s
    (hperiodic T₂ (le_refl _)) hs hodd_s heven
  -- hceq: c₀ * 2^(p-1) = 3*c₀ + 2^s  where c₀ = collatzSeq n T₂
  set c₀ := collatzSeq n T₂ with hc₀_def
  have hc_pos := collatzSeq_pos n hn T₂
  have h2s_pos : 2 ^ s ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
  -- p = 1: c₀ = 3c₀ + 2^s, impossible
  -- p = 2: 2c₀ = 3c₀ + 2^s, impossible
  -- p ≥ 3: c₀ * (2^(p-1) - 3) = 2^s, with 2^(p-1) - 3 odd and ≥ 1, so = 1, giving p = 3
  by_cases hp1 : p = 1
  · subst hp1; simp at hceq; omega
  by_cases hp2 : p = 2
  · subst hp2; simp at hceq; omega
  -- p ≥ 3
  have hp3 : p ≥ 3 := by omega
  -- 2^(p-1) ≥ 4 since p-1 ≥ 2
  have h2pm1_ge : 2 ^ (p - 1) ≥ 4 :=
    le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- Rearrange cycle equation: c₀ * (2^(p-1) - 3) = 2^s
  have hfactor : c₀ * (2 ^ (p - 1) - 3) = 2 ^ s := by
    have h1 : c₀ * (2 ^ (p - 1) - 3) + c₀ * 3 = c₀ * 2 ^ (p - 1) := by
      rw [← Nat.left_distrib, Nat.sub_add_cancel (by omega)]
    omega
  -- 2^(p-1) - 3 is odd (2^(p-1) = 2k with k ≥ 2, so 2k - 3 is odd)
  have hd_odd : (2 ^ (p - 1) - 3) % 2 = 1 := by
    obtain ⟨k, hk, hk2⟩ : ∃ k, 2 ^ (p - 1) = 2 * k ∧ k ≥ 2 := by
      refine ⟨2 ^ (p - 2), ?_, ?_⟩
      · rw [← pow_succ']; congr 1; omega
      · calc 2 ^ (p - 2) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := by norm_num
    rw [hk]; omega
  -- 2^(p-1) - 3 divides 2^s
  have hdvd : (2 ^ (p - 1) - 3) ∣ 2 ^ s := ⟨c₀, by linarith⟩
  -- So 2^(p-1) - 3 = 1
  have hd1 := odd_dvd_pow_two_eq_one hd_odd hdvd
  -- 2^(p-1) = 4 and p = 3
  have h2pm1_4 : 2 ^ (p - 1) = 4 := by omega
  -- 2^(p-1) = 4 forces p = 3 (since 2^k is injective for base ≥ 2)
  have hp_eq : p = 3 := by
    have h_pm1 : p - 1 = 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2pm1_4
    omega
  subst hp_eq
  -- hceq: c₀ * 4 = 3 * c₀ + 2^s, so c₀ = 2^s
  have hc_eq : c₀ = 2 ^ s := by simp at hceq; omega
  -- s < 3, so s ∈ {0, 1, 2}; in each case the cycle contains 1
  have hs3 : s < 3 := hs
  -- Since c₀ = collatzSeq n T₂ and c₀ = 2^s, rewrite in terms of collatzSeq
  have hval : collatzSeq n T₂ = 2 ^ s := by rw [← hc₀_def]; exact hc_eq
  interval_cases s
  · -- s = 0: collatzSeq n T₂ = 1
    exact ⟨T₂, le_refl _, by simpa using hval⟩
  · -- s = 1: collatzSeq n T₂ = 2, collatz 2 = 1
    refine ⟨T₂ + 1, by omega, ?_⟩
    change collatz (collatzSeq n T₂) = 1
    rw [hval]; decide
  · -- s = 2: collatzSeq n T₂ = 4, collatz(collatz 4) = 1
    refine ⟨T₂ + 2, by omega, ?_⟩
    change collatz (collatz (collatzSeq n T₂)) = 1
    rw [hval]; decide

/-! ## Δ₃ ≥ 2 case: decomposition into strict and equality sub-cases -/

/-- Trajectory value is periodic: collatzSeq n (T₂ + k*p) = collatzSeq n T₂. -/
private theorem collatzSeq_kperiods (n T₂ p : ℕ) (k : ℕ)
    (hperiodic : ∀ t, t ≥ T₂ → collatzSeq n (t + p) = collatzSeq n t) :
    collatzSeq n (T₂ + k * p) = collatzSeq n T₂ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * p = k * p + p from by ring,
        show T₂ + (k * p + p) = (T₂ + k * p) + p from by omega,
        hperiodic (T₂ + k * p) (by omega), ih]

/-- From the drift bound 3·ν₃ ≤ t + K and periodicity, derive 3·Δ₃ ≤ p.
    At t = T₂ + k·p: 3·(ν₃(T₂) + k·Δ₃) ≤ T₂ + k·p + K for all k.
    If 3·Δ₃ > p then LHS grows faster than RHS, contradiction for large k. -/
private theorem three_delta3_le_p (n T₂ p : ℕ) (K T₀ : ℕ) (hT₂ : T₂ ≥ T₀)
    (hperiodic : ∀ t, t ≥ T₂ → collatzSeq n (t + p) = collatzSeq n t)
    (hbound3 : ∀ t, t ≥ T₀ → 3 * nu3 n t ≤ t + K) :
    3 * oddStepsInPeriod n T₂ p ≤ p := by
  by_contra h
  push_neg at h
  -- 3*Δ₃ ≥ p + 1
  set Δ₃ := oddStepsInPeriod n T₂ p with hΔ₃_def
  -- Choose k so that k*(3Δ₃ - p) > T₂ + K. Since 3Δ₃ - p ≥ 1, k = T₂+K+1 works.
  set k := T₂ + K + 1
  have hnu3k := nu3_add_kperiods n T₂ p k hperiodic
  have hk_bound := hbound3 (T₂ + k * p) (by omega)
  rw [hnu3k] at hk_bound
  -- hk_bound: 3*(ν₃(T₂) + k*Δ₃) ≤ T₂ + k*p + K
  -- From 3*Δ₃ ≥ p+1: k*(p+1) ≤ k*(3*Δ₃), so k*p + k ≤ 3*(k*Δ₃)
  have hkp : k * p + k ≤ 3 * (k * Δ₃) := by
    have : k * (p + 1) ≤ k * (3 * Δ₃) := Nat.mul_le_mul_left k (by omega)
    have : k * p + k = k * (p + 1) := by ring
    have : 3 * (k * Δ₃) = k * (3 * Δ₃) := by ring
    omega
  -- Chain: cancel nonlinear terms by explicit calc
  have hchain : 3 * nu3 n T₂ + k * p + k ≤ T₂ + k * p + K :=
    calc 3 * nu3 n T₂ + k * p + k
        ≤ 3 * nu3 n T₂ + 3 * (k * Δ₃) := by linarith
      _ = 3 * (nu3 n T₂ + k * Δ₃) := by ring
      _ ≤ T₂ + k * p + K := hk_bound
  omega

/-- The strict inequality case (2Δ₃ < Δ₂, i.e. 3Δ₃ < p): the universal bound
    a(t)·2^ν₂ ≤ n·4^ν₃ at t = T₂+k·p forces a(T₂) < 1 for large k,
    contradicting a(T₂) ≥ 1. -/
private theorem no_cycle_strict_inequality (n : ℕ) (hn : n ≥ 1)
    (T₂ p : ℕ) (_hp : p ≥ 1)
    (hperiodic : ∀ t, t ≥ T₂ → collatzSeq n (t + p) = collatzSeq n t)
    (hstrict : 3 * oddStepsInPeriod n T₂ p + 1 ≤ p) : False := by
  set Δ₃ := oddStepsInPeriod n T₂ p with hΔ₃_def
  -- Choose k so that ν₂(T₂+k*p) > 2*ν₃(T₂+k*p) + n
  -- Sufficient: k ≥ 2*ν₃(T₂) + n + 1 (see calculation below)
  set k := 2 * nu3 n T₂ + n + 1
  set t := T₂ + k * p with ht_def
  -- Universal bound at t
  have hub : collatzSeq n t * 2 ^ nu2 n t ≤ n * 4 ^ nu3 n t :=
    calc collatzSeq n t * 2 ^ nu2 n t
        = n * 3 ^ nu3 n t + correction n t := collatz_identity n t
      _ ≤ n * 4 ^ nu3 n t := identity_le_four_pow_nu3 n hn t
  -- ν₃ at t
  have hnu3 := nu3_add_kperiods n T₂ p k hperiodic
  -- Trajectory value at t = collatzSeq n T₂ (periodicity)
  have hseq := collatzSeq_kperiods n T₂ p k hperiodic
  rw [hseq] at hub
  -- collatzSeq n T₂ ≥ 1
  have hc_pos := collatzSeq_pos n hn T₂
  -- Partition at t and at T₂
  have hpart_t := nu_partition n t
  have hpart_T₂ := nu_partition n T₂
  -- Key inequality: 2*ν₃(t) + (n+1) ≤ ν₂(t)
  -- ν₃(t) = ν₃(T₂) + k*Δ₃
  -- ν₂(t) = T₂ + k*p - ν₃(T₂) - k*Δ₃  (from partition)
  -- Need: 2*(ν₃(T₂) + k*Δ₃) + (n+1) ≤ T₂ + k*p - ν₃(T₂) - k*Δ₃
  -- i.e. 3*ν₃(T₂) + 3*k*Δ₃ + n + 1 ≤ T₂ + k*p
  -- Since p ≥ 3*Δ₃+1: k*p ≥ 3*k*Δ₃ + k
  -- So RHS ≥ T₂ + 3*k*Δ₃ + k, need: 3*ν₃(T₂) + n + 1 ≤ T₂ + k
  -- k = 2*ν₃(T₂) + n + 1, T₂ ≥ ν₃(T₂) (partition), so T₂ + k ≥ 3*ν₃(T₂) + n + 1 ✓
  have hexp : 2 * nu3 n t + (n + 1) ≤ nu2 n t := by
    -- Suffices: 3*nu3(t) + (n+1) ≤ t (then omega closes using partition)
    have hpart := nu_partition n t
    suffices h : 3 * nu3 n t + (n + 1) ≤ T₂ + k * p by omega
    -- nu3(t) = nu3(T₂) + k*Δ₃
    rw [hnu3]
    -- Goal: 3*(ν₃(T₂) + k*Δ₃) + (n+1) ≤ T₂ + k*p
    -- From hstrict: k*(3*Δ₃+1) ≤ k*p, so 3*(k*Δ₃) + k ≤ k*p
    have hkp : 3 * (k * Δ₃) + k ≤ k * p := by
      have h1 : k * (3 * Δ₃ + 1) ≤ k * p := Nat.mul_le_mul_left k hstrict
      have : 3 * (k * Δ₃) + k = k * (3 * Δ₃ + 1) := by ring
      omega
    -- From partition: ν₃(T₂) ≤ T₂
    have hnu3_le : nu3 n T₂ ≤ T₂ := by have := nu_partition n T₂; omega
    -- Chain: 3*(ν₃(T₂)+k*Δ₃) + (n+1) ≤ T₂ + k + 3*(k*Δ₃) ≤ T₂ + k*p
    calc 3 * (nu3 n T₂ + k * Δ₃) + (n + 1)
        = 3 * nu3 n T₂ + 3 * (k * Δ₃) + (n + 1) := by ring
      _ ≤ T₂ + k + 3 * (k * Δ₃) := by omega
      _ ≤ T₂ + k * p := by linarith
  -- From hexp: 2^(n+1) * 4^ν₃(t) ≤ 2^ν₂(t)
  have hpow : 2 ^ (n + 1) * 4 ^ nu3 n t ≤ 2 ^ nu2 n t :=
    calc 2 ^ (n + 1) * 4 ^ nu3 n t
        = 2 ^ (n + 1) * (2 ^ 2) ^ nu3 n t := by norm_num
      _ = 2 ^ (n + 1) * 2 ^ (2 * nu3 n t) := by rw [← pow_mul]
      _ = 2 ^ (n + 1 + 2 * nu3 n t) := by rw [← pow_add]
      _ ≤ 2 ^ nu2 n t :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
  -- From hub and hc_pos: 2^ν₂(t) ≤ n * 4^ν₃(t)
  have h2 : 2 ^ nu2 n t ≤ n * 4 ^ nu3 n t :=
    calc 2 ^ nu2 n t
        = 1 * 2 ^ nu2 n t := by ring
      _ ≤ collatzSeq n T₂ * 2 ^ nu2 n t :=
          Nat.mul_le_mul_right _ hc_pos
      _ ≤ n * 4 ^ nu3 n t := hub
  -- Combined: 2^(n+1) * 4^ν₃(t) ≤ n * 4^ν₃(t)
  -- Cancel 4^ν₃(t): 2^(n+1) ≤ n
  have h4pos : 0 < 4 ^ nu3 n t := by positivity
  have habsurd : 2 ^ (n + 1) ≤ n :=
    Nat.le_of_mul_le_mul_right (le_trans hpow h2) h4pos
  -- But n < 2^(n+1) for all n, contradiction
  have : n < 2 ^ (n + 1) :=
    lt_of_lt_of_le (Nat.lt_pow_self (by norm_num : 1 < 2))
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  omega

/-- collatzStep (from Baker.lean) equals collatz (from Basic.lean). -/
private theorem collatzStep_eq_collatz (x : ℕ) : collatzStep x = collatz x := by
  unfold collatzStep collatz; rfl

/-- collatzSeq as iteration of collatz from a starting point. -/
private theorem collatzSeq_as_iterate (n T₂ k : ℕ) :
    collatzSeq n (T₂ + k) = collatz^[k] (collatzSeq n T₂) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change collatz (collatzSeq n (T₂ + k)) = collatz^[k + 1] (collatzSeq n T₂)
    rw [Function.iterate_succ', Function.comp_apply, ih]

/-- The equality case (2Δ₃ = Δ₂, i.e. p = 3Δ₃): uses Baker-Steiner cycle theorem.
    When p = 3·Δ₃, the cycle equation gives c₀ = S/(4^Δ₃ - 3^Δ₃) where
    S ~ 3^Δ₃ grows, so c₀ doesn't shrink to zero. Baker's theorem on
    linear forms in logarithms rules out all non-trivial solutions. -/
private theorem no_cycle_equality_case (n : ℕ) (hn : n ≥ 1)
    (T₂ p : ℕ) (_hp : p ≥ 1)
    (hperiodic : ∀ t, t ≥ T₂ → collatzSeq n (t + p) = collatzSeq n t)
    (hpeq : p = 3 * oddStepsInPeriod n T₂ p)
    (hdelta : oddStepsInPeriod n T₂ p ≥ 2) :
    ∃ t, t ≥ T₂ ∧ collatzSeq n t = 1 := by
  set Δ₃ := oddStepsInPeriod n T₂ p with hΔ₃_def
  set c₀ := collatzSeq n T₂ with hc₀_def
  have hc₀_pos : c₀ ≥ 1 := collatzSeq_pos n hn T₂
  have hstep_eq : collatzStep = collatz := funext collatzStep_eq_collatz
  -- Establish the cycle condition for Baker's theorem
  have hcycle : collatzStep^[3 * Δ₃] c₀ = c₀ := by
    have h : collatzSeq n (T₂ + 3 * Δ₃) = c₀ := by
      rw [← hpeq]; exact hperiodic T₂ (le_refl _)
    calc collatzStep^[3 * Δ₃] c₀
        = collatz^[3 * Δ₃] c₀ := by rw [hstep_eq]
      _ = collatzSeq n (T₂ + 3 * Δ₃) := by rw [← collatzSeq_as_iterate]
      _ = c₀ := h
  -- Apply Baker-Steiner cycle theorem
  obtain ⟨t, ht_lt, ht_one⟩ := baker_no_balanced_cycle Δ₃ hdelta c₀ hc₀_pos hcycle
  -- Bridge back to collatzSeq
  refine ⟨T₂ + t, by omega, ?_⟩
  rw [collatzSeq_as_iterate, ← hstep_eq]
  exact ht_one

/-- Cycles with Δ₃ ≥ 2 are impossible.
    Case split: if 3Δ₃ < p (strict), the universal bound gives a contradiction.
    If 3Δ₃ = p (equality), needs Baker — left as a focused sorry. -/
theorem no_cycle_delta3_ge2 (n : ℕ) (hn : n ≥ 1)
    (B T₂ p : ℕ) (hp : p ≥ 1) (K T₀ : ℕ) (hT₂ : T₂ ≥ T₀)
    (_hB : ∀ t, t ≥ T₂ → collatzSeq n t ≤ B)
    (hperiodic : ∀ t, t ≥ T₂ → collatzSeq n (t + p) = collatzSeq n t)
    (hbound3 : ∀ t, t ≥ T₀ → 3 * nu3 n t ≤ t + K)
    (hdelta : oddStepsInPeriod n T₂ p ≥ 2) :
    ∃ t, t ≥ T₂ ∧ collatzSeq n t = 1 := by
  have h3d := three_delta3_le_p n T₂ p K T₀ hT₂ hperiodic hbound3
  -- Case split: 3*Δ₃ < p or 3*Δ₃ = p
  by_cases heq : p = 3 * oddStepsInPeriod n T₂ p
  · exact no_cycle_equality_case n hn T₂ p hp hperiodic heq hdelta
  · exact absurd
      (no_cycle_strict_inequality n hn T₂ p hp hperiodic (by omega))
      (not_false)

/-- Any eventually periodic Collatz trajectory with linear drift bound
    must contain 1 in its cycle.

    Proof by case analysis on Δ₃ (odd steps per period):
    - Δ₃ = 0: impossible (multiplicative identity forces 2^p = 1)
    - Δ₃ = 1: the only cycle is {1,2,4} (algebraic)
    - Δ₃ ≥ 2: impossible (strict case proved; equality case needs Baker) -/
theorem cycle_contains_one (n : ℕ) (hn : n ≥ 1)
    (B T₂ p : ℕ) (hp : p ≥ 1) (K T₀ : ℕ) (hT₂ : T₂ ≥ T₀)
    (hB : ∀ t, t ≥ T₂ → collatzSeq n t ≤ B)
    (hperiodic : ∀ t, t ≥ T₂ → collatzSeq n (t + p) = collatzSeq n t)
    (hbound3 : ∀ t, t ≥ T₀ → 3 * nu3 n t ≤ t + K) :
    ∃ t, t ≥ T₂ ∧ collatzSeq n t = 1 := by
  -- Case split on Δ₃ = oddStepsInPeriod n T₂ p
  by_cases h0 : oddStepsInPeriod n T₂ p = 0
  · exact absurd h0 (by
      intro h0; exact no_cycle_delta3_zero n hn T₂ p hp
        (hperiodic T₂ (le_refl _)) h0)
  by_cases h1 : oddStepsInPeriod n T₂ p = 1
  · exact cycle_contains_one_of_delta3_one n hn T₂ p hp hperiodic h1
  · exact no_cycle_delta3_ge2 n hn B T₂ p hp K T₀ hT₂ hB hperiodic
      hbound3 (by omega)

/-! ## Main composition -/

/-- Linear drift implies collatzReaches.
    From the K-bound 3·ν₃ ≤ t + K alone:
    trajectory bounded → eventually periodic → cycle is trivial → reaches 1.
    Walk divergence (hdiv) was previously a parameter but is unused. -/
theorem reaches_one_of_linear_drift (n : ℕ) (hn : n ≥ 1)
    (K T₀ : ℕ) (hbound3 : ∀ t, t ≥ T₀ → 3 * nu3 n t ≤ t + K) :
    collatzReaches n := by
  -- Step 1: trajectory is eventually bounded
  obtain ⟨B, T₁, hT₁ge, hBound⟩ :=
    collatzSeq_eventually_bounded_of_linear_drift n hn K T₀ hbound3
  -- Step 2: trajectory is eventually periodic
  obtain ⟨T₂, p, hp, hT₂ge, hPeriodic⟩ :=
    collatzSeq_eventually_periodic_of_bounded n hn B T₁ hBound
  -- Step 3: cycle contains 1 (pass K, T₀, hbound3 for Δ₃≥2 case)
  have hCycle := cycle_contains_one n hn B T₂ p hp K T₀ (by omega)
    (fun t ht => hBound t (by omega)) hPeriodic hbound3
  -- Step 4: extract collatzReaches
  obtain ⟨t, _, ht1⟩ := hCycle
  exact ⟨t, ht1⟩

end Collatz
