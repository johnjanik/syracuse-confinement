/-
  CollatzLean/SteinerCycle.lean
  Steiner/Hercher cycle elimination: no non-trivial Collatz cycle
  with at most 91 odd steps.

  Architecture:
  1. correction_upper_bound: 2·correction ≤ (3^K − 1)·2^L (proved by induction)
  2. steiner_K_bound_79: for Δ₃ ≤ 79, cycleNu3 ≤ 91 (proved via native_decide
     on 2^145 < 3^92)
  3. hercher_no_small_cycle: axiom citing Hercher 2024 — no m-cycle for m ≤ 91
  4. steiner_cycle_elimination: combines (2) and (3) for Δ₃ ≤ 79

  References:
  - Steiner (1977): Original cycle equation framework
  - Simons & de Weger (2005): Extended to m ≤ 68
  - Hercher (2024): "No Collatz m-Cycles with m ≤ 91", extended to m ≤ 91
    using elementary continued fraction + correction sum analysis.
-/
import CollatzLean.Baker

set_option linter.style.nativeDecide false

namespace Collatz

/-! ## Correction upper bound

The correction term cycleCorrection c₀ t satisfies:
  correction = ∑_{i=1}^{K} 3^{K-i} · 2^{L_i}
where K = cycleNu3, L_i = cycleNu2 at the i-th odd step, L_i ≤ L = cycleNu2.

Upper bound: correction ≤ 2^L · ∑_{i=0}^{K-1} 3^i = 2^L · (3^K - 1)/2.
Equivalently: 2·correction + 2^L ≤ 3^K · 2^L (avoids nat subtraction). -/

/-- The correction is bounded: 2·correction + 2^L ≤ 3^K · 2^L.
    Equivalent to correction ≤ 2^L·(3^K − 1)/2 but stated without subtraction.
    Proved by induction on t, tracking the recurrence at odd/even steps. -/
theorem correction_upper_bound (c₀ t : ℕ) :
    2 * cycleCorrection c₀ t + 2 ^ cycleNu2 c₀ t ≤
      3 ^ cycleNu3 c₀ t * 2 ^ cycleNu2 c₀ t := by
  induction t with
  | zero => simp [cycleCorrection, cycleNu3, cycleNu2]
  | succ t ih =>
    by_cases hodd : (collatzStep^[t] c₀) % 2 = 1
    · -- Odd step: correction(t+1) = 3·corr + 2^L, K→K+1, L unchanged
      -- Need: 2·(3·corr + 2^L) + 2^L ≤ 3^(K+1)·2^L
      -- = 6·corr + 3·2^L ≤ 3·3^K·2^L = 3·(2·corr + 2^L + (3^K·2^L - 2·corr - 2^L))
      -- Simply: 3·(2·corr + 2^L) ≤ 3·(3^K·2^L), which is 3 × IH.
      rw [cycleCorrection_succ_odd c₀ t hodd,
          cycleNu3_succ_odd c₀ t hodd,
          cycleNu2_succ_odd c₀ t hodd, pow_succ]
      nlinarith [ih]
    · -- Even step: correction unchanged, K unchanged, L→L+1
      -- Need: 2·corr + 2^(L+1) ≤ 3^K·2^(L+1)
      -- = 2·corr + 2·2^L ≤ 2·3^K·2^L. From IH (2·corr + 2^L ≤ 3^K·2^L):
      -- 2·corr ≤ 3^K·2^L - 2^L, so 2·corr + 2·2^L ≤ 3^K·2^L + 2^L ≤ 2·3^K·2^L.
      have heven : (collatzStep^[t] c₀) % 2 = 0 := by omega
      rw [cycleCorrection_succ_even c₀ t heven,
          cycleNu3_succ_even c₀ t heven,
          cycleNu2_succ_even c₀ t heven, pow_succ]
      nlinarith [ih, Nat.one_le_pow (cycleNu3 c₀ t) 3 (by omega)]

/-! ## Cycle minimum bound

From the cycle equation c₀·(2^L - 3^K) = correction and the correction
upper bound 2·correction ≤ (3^K - 1)·2^L, we get:
  2·c₀·(2^L - 3^K) ≤ (3^K - 1)·2^L

This bounds c₀ from above in terms of K and L. For large K/L, the bound
on c₀ becomes small, limiting cycle membership. -/

/-- For a cycle with c₀ ≥ 2: the correction upper bound constrains c₀.
    Specifically: 2·c₀·(2^L − 3^K) + 2^L ≤ 3^K · 2^L. -/
theorem cycle_c0_bound (c₀ p : ℕ)
    (hcycle : collatzStep^[p] c₀ = c₀)
    (hexp : 2 ^ cycleNu2 c₀ p > 3 ^ cycleNu3 c₀ p) :
    2 * c₀ * (2 ^ cycleNu2 c₀ p - 3 ^ cycleNu3 c₀ p) + 2 ^ cycleNu2 c₀ p ≤
      3 ^ cycleNu3 c₀ p * 2 ^ cycleNu2 c₀ p := by
  have hceq := cycle_equation c₀ p hcycle hexp
  have hcub := correction_upper_bound c₀ p
  -- hceq: c₀ * (2^L - 3^K) = correction
  -- hcub: 2 * correction + 2^L ≤ 3^K * 2^L
  nlinarith

/-! ## Correction lower bound

The correction term also has a lower bound independent of the trajectory:
  correction ≥ (3^K - 1)/2
since each odd step contributes at least 3^{K-i} · 2^0 = 3^{K-i}.
Equivalently: 2·correction + 1 ≥ 3^K (avoids nat division). -/

/-- The correction is bounded below: 2·correction + 1 ≥ 3^K.
    Equivalent to correction ≥ (3^K − 1)/2 but stated without division.
    Proved by induction on t, mirroring correction_upper_bound. -/
theorem correction_lower_bound (c₀ t : ℕ) :
    2 * cycleCorrection c₀ t + 1 ≥ 3 ^ cycleNu3 c₀ t := by
  induction t with
  | zero => simp [cycleCorrection, cycleNu3]
  | succ t ih =>
    by_cases hodd : (collatzStep^[t] c₀) % 2 = 1
    · -- Odd step: correction(t+1) = 3·corr + 2^L, K→K+1, L unchanged
      -- Need: 2·(3·corr + 2^L) + 1 ≥ 3^(K+1) = 3·3^K
      -- From IH: 2·corr + 1 ≥ 3^K, so 2·corr ≥ 3^K - 1
      -- LHS = 6·corr + 2·2^L + 1 ≥ 3·(3^K - 1) + 2 + 1 = 3^(K+1)
      rw [cycleCorrection_succ_odd c₀ t hodd,
          cycleNu3_succ_odd c₀ t hodd, pow_succ]
      nlinarith [ih, Nat.one_le_pow (cycleNu2 c₀ t) 2 (by omega)]
    · -- Even step: correction unchanged, K unchanged
      have heven : (collatzStep^[t] c₀) % 2 = 0 := by omega
      rw [cycleCorrection_succ_even c₀ t heven,
          cycleNu3_succ_even c₀ t heven]
      exact ih

/-! ## Cycle c₀ lower bound

From the cycle equation c₀·(2^L - 3^K) = correction and the correction
lower bound 2·correction + 1 ≥ 3^K, we get:
  2·c₀·(2^L - 3^K) + 1 ≥ 3^K

This bounds c₀ from below. Combined with the upper bound, c₀ is squeezed. -/

/-- For a cycle: the correction lower bound constrains c₀ from below.
    Specifically: 2·c₀·(2^L − 3^K) + 1 ≥ 3^K. -/
theorem cycle_c0_lower_bound (c₀ p : ℕ)
    (hcycle : collatzStep^[p] c₀ = c₀)
    (hexp : 2 ^ cycleNu2 c₀ p > 3 ^ cycleNu3 c₀ p) :
    2 * c₀ * (2 ^ cycleNu2 c₀ p - 3 ^ cycleNu3 c₀ p) + 1 ≥
      3 ^ cycleNu3 c₀ p := by
  have hceq := cycle_equation c₀ p hcycle hexp
  have hclb := correction_lower_bound c₀ p
  nlinarith

/-- c₀ lower bound in division-free form:
    c₀ · 2 · (2^L − 3^K) ≥ 3^K − 1. -/
theorem cycle_c0_explicit_lower (c₀ p : ℕ)
    (hcycle : collatzStep^[p] c₀ = c₀)
    (hexp : 2 ^ cycleNu2 c₀ p > 3 ^ cycleNu3 c₀ p)
    (_hK_pos : cycleNu3 c₀ p ≥ 1) :
    c₀ * (2 * (2 ^ cycleNu2 c₀ p - 3 ^ cycleNu3 c₀ p)) ≥
      3 ^ cycleNu3 c₀ p - 1 := by
  have h := cycle_c0_lower_bound c₀ p hcycle hexp
  -- h : 2 * c₀ * (2^L - 3^K) + 1 ≥ 3^K
  -- Rewrite: c₀ * (2 * x) = 2 * c₀ * x
  have hrw : c₀ * (2 * (2 ^ cycleNu2 c₀ p - 3 ^ cycleNu3 c₀ p)) =
    2 * c₀ * (2 ^ cycleNu2 c₀ p - 3 ^ cycleNu3 c₀ p) := by ring
  rw [hrw]
  omega

/-! ## Cycle c₀ squeeze: upper and lower bounds combined

For a cycle with K ≥ 1 odd steps, L even steps, 2^L > 3^K, c₀ ≥ 2:
  (3^K - 1) / (2·(2^L - 3^K)) ≤ c₀ ≤ (3^K - 1)·2^L / (2·(2^L - 3^K))

Stated in ℕ without division:
  Lower: c₀ · 2 · (2^L - 3^K) ≥ 3^K - 1
  Upper: 2·c₀·(2^L - 3^K) + 2^L ≤ 3^K · 2^L -/

/-- Cycle c₀ squeeze: both bounds together. -/
theorem cycle_c0_squeeze (c₀ p : ℕ)
    (hcycle : collatzStep^[p] c₀ = c₀)
    (hexp : 2 ^ cycleNu2 c₀ p > 3 ^ cycleNu3 c₀ p)
    (hK_pos : cycleNu3 c₀ p ≥ 1) :
    c₀ * (2 * (2 ^ cycleNu2 c₀ p - 3 ^ cycleNu3 c₀ p)) ≥
      3 ^ cycleNu3 c₀ p - 1 ∧
    2 * c₀ * (2 ^ cycleNu2 c₀ p - 3 ^ cycleNu3 c₀ p) + 2 ^ cycleNu2 c₀ p ≤
      3 ^ cycleNu3 c₀ p * 2 ^ cycleNu2 c₀ p :=
  ⟨cycle_c0_explicit_lower c₀ p hcycle hexp hK_pos,
   cycle_c0_bound c₀ p hcycle hexp⟩

/-! ## K-bound for small Δ₃

For Δ₃ ≤ 79 (period p = 3·Δ₃ ≤ 237):
If cycleNu3 ≥ 92 then cycleNu2 ≤ 3·79 - 92 = 145.
Since 2^145 < 3^92 (verified), this contradicts 2^L > 3^K.
Hence cycleNu3 ≤ 91 for any cycle with Δ₃ ≤ 79. -/

private theorem pow2_145_lt_pow3_92 : 2 ^ 145 < 3 ^ 92 := by native_decide

/-- For Δ₃ ≤ 79, any cycle with 2^ν₂ > 3^ν₃ has at most 91 odd steps. -/
theorem steiner_K_bound_79 (Δ₃ : ℕ) (hΔ_le : Δ₃ ≤ 79) (c₀ : ℕ)
    (hexp : 2 ^ cycleNu2 c₀ (3 * Δ₃) > 3 ^ cycleNu3 c₀ (3 * Δ₃)) :
    cycleNu3 c₀ (3 * Δ₃) ≤ 91 := by
  by_contra h
  push_neg at h
  have hK : cycleNu3 c₀ (3 * Δ₃) ≥ 92 := by omega
  -- ν₂ = 3·Δ₃ - ν₃ ≤ 237 - 92 = 145
  have hL : cycleNu2 c₀ (3 * Δ₃) ≤ 145 := by
    unfold cycleNu2
    have := cycleNu3_le c₀ (3 * Δ₃)
    omega
  -- 2^ν₂ ≤ 2^145
  have h2L : 2 ^ cycleNu2 c₀ (3 * Δ₃) ≤ 2 ^ 145 :=
    Nat.pow_le_pow_right (by omega) hL
  -- 3^92 ≤ 3^ν₃
  have h3K : 3 ^ 92 ≤ 3 ^ cycleNu3 c₀ (3 * Δ₃) :=
    Nat.pow_le_pow_right (by omega) hK
  -- 2^ν₂ ≤ 2^145 < 3^92 ≤ 3^ν₃, contradicting hexp
  omega

/-! ## Generalized K-bound

The proof of steiner_K_bound_79 generalizes: for ANY Hercher threshold M
and period bound D satisfying 2^{3D-(M+1)} < 3^{M+1}, cycles with
Δ₃ ≤ D have at most M odd steps.

The maximum D for given M is approximately (M+1) · log₂3 / 3 ≈ 0.528·(M+1).
See ContinuedFraction.lean for verified boundary values. -/

/-- Generalized K-bound: if 2^{3D-(M+1)} < 3^{M+1}, then for any cycle
    with Δ₃ ≤ D, the number of odd steps is at most M.
    Specializes to steiner_K_bound_79 when M=91, D=79. -/
theorem steiner_K_bound_general (M D : ℕ)
    (hpow : 2 ^ (3 * D - (M + 1)) < 3 ^ (M + 1))
    (c₀ Δ₃ : ℕ) (hΔ : Δ₃ ≤ D)
    (hexp : 2 ^ cycleNu2 c₀ (3 * Δ₃) > 3 ^ cycleNu3 c₀ (3 * Δ₃)) :
    cycleNu3 c₀ (3 * Δ₃) ≤ M := by
  by_contra h
  push_neg at h
  have hK : cycleNu3 c₀ (3 * Δ₃) ≥ M + 1 := by omega
  -- ν₂ = 3Δ₃ - ν₃ ≤ 3D - (M+1)
  have hL : cycleNu2 c₀ (3 * Δ₃) ≤ 3 * D - (M + 1) := by
    unfold cycleNu2
    have := cycleNu3_le c₀ (3 * Δ₃)
    omega
  -- 2^ν₂ ≤ 2^(3D-(M+1))
  have h2L : 2 ^ cycleNu2 c₀ (3 * Δ₃) ≤ 2 ^ (3 * D - (M + 1)) :=
    Nat.pow_le_pow_right (by omega) hL
  -- 3^(M+1) ≤ 3^ν₃
  have h3K : 3 ^ (M + 1) ≤ 3 ^ cycleNu3 c₀ (3 * Δ₃) :=
    Nat.pow_le_pow_right (by omega) hK
  -- Chain: 2^ν₂ ≤ 2^(3D-(M+1)) < 3^(M+1) ≤ 3^ν₃, contradicting hexp
  omega

/-! ## Hercher's theorem (axiom)

Hercher (2024) proved: there is no non-trivial Collatz cycle with
at most 91 odd steps. The proof uses:
1. Correction sum bounds (each local minimum n_i ≥ X₀ ≈ 10^20)
2. Continued fraction expansion of log₂3
3. Case analysis on candidate (K, L) pairs

This is the sole axiom in this file. All other results are proved. -/

/-- Hercher's theorem: no non-trivial cycle with ≤ 91 odd steps.
    For any c₀ ≥ 2 in a periodic orbit with at most 91 odd steps,
    the orbit must contain 1 (i.e., c₀ is in the trivial cycle {1,2,4}).

    Reference: Hercher, "No Collatz m-Cycles with m ≤ 91" (2024). -/
axiom hercher_no_small_cycle :
    ∀ (c₀ p : ℕ), c₀ ≥ 2 → p ≥ 1 →
      collatzStep^[p] c₀ = c₀ → cycleNu3 c₀ p ≤ 91 →
      ∃ t, t < p ∧ collatzStep^[t] c₀ = 1

/-! ## Combined cycle elimination for Δ₃ ≤ 79 -/

/-- For Δ₃ ≤ 79: any periodic orbit of period 3·Δ₃ with c₀ ≥ 2 contains 1.
    Proof: steiner_K_bound_79 gives cycleNu3 ≤ 91, then hercher_no_small_cycle
    eliminates the cycle. -/
theorem steiner_cycle_elimination (Δ₃ : ℕ) (hΔ : Δ₃ ≥ 2) (hΔ_le : Δ₃ ≤ 79)
    (c₀ : ℕ) (hc : c₀ ≥ 2)
    (hcycle : collatzStep^[3 * Δ₃] c₀ = c₀)
    (hexp : 2 ^ cycleNu2 c₀ (3 * Δ₃) > 3 ^ cycleNu3 c₀ (3 * Δ₃)) :
    ∃ t, t < 3 * Δ₃ ∧ collatzStep^[t] c₀ = 1 := by
  have hK_le := steiner_K_bound_79 Δ₃ hΔ_le c₀ hexp
  exact hercher_no_small_cycle c₀ (3 * Δ₃) hc (by omega) hcycle hK_le

/-- Generalized cycle elimination: given a Hercher-type result for m ≤ M
    and a power comparison 2^{3D-(M+1)} < 3^{M+1}, all cycles with
    Δ₃ ≤ D are trivial. Takes the Hercher result as a hypothesis rather
    than relying on the axiom, making extensions modular.

    To extend cycle elimination to Δ₃ ≤ D for a new threshold M:
    1. Prove the power comparison `2^{3D-(M+1)} < 3^{M+1}` via native_decide
       (see ContinuedFraction.steinerWorks for verified boundaries)
    2. Extend the Hercher axiom to m ≤ M
    3. Apply this theorem -/
theorem steiner_cycle_elimination_general (M D : ℕ)
    (hpow : 2 ^ (3 * D - (M + 1)) < 3 ^ (M + 1))
    (hercher : ∀ c₀ p, c₀ ≥ 2 → p ≥ 1 → collatzStep^[p] c₀ = c₀ →
               cycleNu3 c₀ p ≤ M → ∃ t, t < p ∧ collatzStep^[t] c₀ = 1)
    (Δ₃ : ℕ) (_hΔ : Δ₃ ≥ 2) (hΔ_le : Δ₃ ≤ D)
    (c₀ : ℕ) (hc : c₀ ≥ 2)
    (hcycle : collatzStep^[3 * Δ₃] c₀ = c₀)
    (hexp : 2 ^ cycleNu2 c₀ (3 * Δ₃) > 3 ^ cycleNu3 c₀ (3 * Δ₃)) :
    ∃ t, t < 3 * Δ₃ ∧ collatzStep^[t] c₀ = 1 := by
  have hK_le := steiner_K_bound_general M D hpow c₀ Δ₃ hΔ_le hexp
  exact hercher c₀ (3 * Δ₃) hc (by omega) hcycle hK_le

/-! ## Large Δ₃ case: focused sorry

For Δ₃ ≥ 80, the number of odd steps K could exceed 91.
The c₀ squeeze (cycle_c0_squeeze) cannot close this gap: for
Δ₃ = 80 and ν₃ = 92, min c₀ ≈ 0.14 (far below 2), so the
squeeze alone cannot force a contradiction.

The limitation is structural: max D ≈ 0.528·(M+1) where M is
the Hercher threshold. With M = 91, max D = 79 is optimal.
Each unit increase in M gains ~0.86 units of Δ₃ coverage.
See ContinuedFraction.lean for the full boundary analysis.

Closing this sorry requires extending Hercher's computational
verification to m > 91, then applying steiner_cycle_elimination_general. -/

/-- For Δ₃ ≥ 80: cycle elimination. This remains open.
    The c₀ squeeze is too weak (ratio of 2^{ν₂} between upper and lower
    bounds). Closing requires extending Hercher beyond m = 91, then using
    steiner_cycle_elimination_general with the new threshold. -/
theorem steiner_cycle_large (Δ₃ : ℕ) (hΔ : Δ₃ ≥ 80)
    (c₀ : ℕ) (hc : c₀ ≥ 2)
    (hcycle : collatzStep^[3 * Δ₃] c₀ = c₀)
    (hexp : 2 ^ cycleNu2 c₀ (3 * Δ₃) > 3 ^ cycleNu3 c₀ (3 * Δ₃)) :
    ∃ t, t < 3 * Δ₃ ∧ collatzStep^[t] c₀ = 1 := by
  sorry

/-! ## Main cycle elimination (moved from Baker.lean)

Decomposed into:
- c₀ = 1: trivial
- c₀ ≥ 2, Δ₃ ≤ 79: proved via steiner_K_bound_79 + hercher_no_small_cycle
- c₀ ≥ 2, Δ₃ ≥ 80: sorry (open — requires extending Hercher beyond m = 91) -/

/-- No non-trivial cycle satisfies the Steiner equation.
    For Δ₃ ≤ 79: proved via Hercher's theorem (no m-cycle for m ≤ 91).
    For Δ₃ ≥ 80: sorry (open frontier).

    References: Steiner (1977), Simons & de Weger (2005), Hercher (2024). -/
private theorem cycle_no_nontrivial_solution (Δ₃ : ℕ) (hΔ : Δ₃ ≥ 2)
    (c₀ : ℕ) (hc : c₀ ≥ 1)
    (hcycle : collatzStep^[3 * Δ₃] c₀ = c₀)
    (hident : c₀ * 2 ^ cycleNu2 c₀ (3 * Δ₃) =
      c₀ * 3 ^ cycleNu3 c₀ (3 * Δ₃) + cycleCorrection c₀ (3 * Δ₃)) :
    ∃ t, t < 3 * Δ₃ ∧ collatzStep^[t] c₀ = 1 := by
  -- Trivial case: c₀ = 1
  by_cases hc1 : c₀ = 1
  · exact ⟨0, by omega, by simp [hc1]⟩
  -- Nontrivial case: c₀ ≥ 2
  have hc2 : c₀ ≥ 2 := by omega
  -- At least one odd step (all-even gives c₀·2^p = c₀, impossible)
  have hnu3_pos : cycleNu3 c₀ (3 * Δ₃) ≥ 1 := by
    by_contra hlt
    push_neg at hlt
    have hv3 : cycleNu3 c₀ (3 * Δ₃) = 0 := by omega
    have hcorr0 := correction_zero_of_nu3_zero c₀ (3 * Δ₃) hv3
    have hnu2 : cycleNu2 c₀ (3 * Δ₃) = 3 * Δ₃ := by unfold cycleNu2; omega
    rw [hv3, hcorr0, hnu2] at hident
    simp only [pow_zero, mul_one, add_zero] at hident
    have h2p : 2 ≤ 2 ^ (3 * Δ₃) := by
      calc 2 = 2 ^ 1 := by ring
        _ ≤ 2 ^ (3 * Δ₃) := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  -- Exponent ordering: 2^ν₂ > 3^ν₃
  have hexp : 2 ^ cycleNu2 c₀ (3 * Δ₃) > 3 ^ cycleNu3 c₀ (3 * Δ₃) := by
    by_contra hle
    push_neg at hle
    have := Nat.mul_le_mul_left c₀ hle
    have := cycleCorrection_pos c₀ (3 * Δ₃) hnu3_pos
    omega
  -- Case split: Δ₃ ≤ 79 (proved) vs Δ₃ ≥ 80 (sorry)
  by_cases hΔ_small : Δ₃ ≤ 79
  · exact steiner_cycle_elimination Δ₃ hΔ hΔ_small c₀ hc2 hcycle hexp
  · push_neg at hΔ_small
    exact steiner_cycle_large Δ₃ (by omega) c₀ hc2 hcycle hexp

/-- Baker-Steiner-Hercher cycle theorem: no non-trivial Collatz cycle has
    period p = 3·Δ₃ for any Δ₃ ≥ 2. Any such cycle must contain 1.

    For Δ₃ ≤ 79: proved via correction bound + Hercher's theorem.
    For Δ₃ ≥ 80: sorry (requires extending Hercher beyond m = 91). -/
theorem baker_no_balanced_cycle (Δ₃ : ℕ) (hΔ : Δ₃ ≥ 2)
    (c₀ : ℕ) (hc : c₀ ≥ 1)
    (hcycle : collatzStep^[3 * Δ₃] c₀ = c₀) :
    ∃ t, t < 3 * Δ₃ ∧ collatzStep^[t] c₀ = 1 := by
  have hident := cycle_identity c₀ (3 * Δ₃)
  rw [hcycle] at hident
  exact cycle_no_nontrivial_solution Δ₃ hΔ c₀ hc hcycle hident

end Collatz
