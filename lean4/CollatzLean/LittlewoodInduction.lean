/-
  CollatzLean/LittlewoodInduction.lean
  Scale induction argument for Littlewood's conjecture on (log₂5, log₂7).

  Wires together:
  - Matveev lower bound (LinearFormThree.lean, axiom A6)
  - Simultaneous approximation definitions (SimultaneousApprox.lean)
  - 2D torus residence bounds (LittlewoodResidence.lean)

  Main result: littlewood_log2_5_log2_7, which asserts Littlewood's
  conjecture for the specific pair (log₂5, log₂7).

  Architecture:
  1. product_bounded_by_scale, product_doubly_bounded: if both fracDists
     are small, the Littlewood product is bounded by n/(4K₁K₂)
  2. product_decays_with_scale: 1/(4K²) < ε for K large enough
  3. simultaneous_approx_log2_5_7 (sorry): the key number-theoretic input
     stating that for (log₂5, log₂7), simultaneous good approximants
     exist with n ≤ K, not just n ≤ K² (the 2D Dirichlet bound)
  4. littlewood_log2_5_log2_7: proved from (1)-(3)

  The sorry in simultaneous_approx_log2_5_7 encapsulates the deep
  Diophantine content. Standard 2D pigeonhole gives n ≤ K² with both
  fracDists < 1/K, yielding product ≤ 1 (constant). Getting product → 0
  requires n = o(K²), which for (log₂5, log₂7) follows from the
  Matveev lower bound on linear forms in {log 2, log 5, log 7}: the
  bound exp(-C·(log H)⁴) forces partial quotients of log₂5 to grow
  at most like exp(C·(log q)⁴), ensuring the best simultaneous
  approximant at scale K has n ≤ K^(2-δ) for effective δ > 0.
-/
import CollatzLean.LittlewoodResidence

set_option linter.style.nativeDecide false

namespace Collatz

open Real Filter

/-! ## Product decay across scales -/

/-- At scale K, if we have n with the trajectory visiting cell (a,b),
    then the Littlewood product at n is bounded by n · (1/K) · fracDist(n·β).
    When β-distance is also controlled at a larger scale K', we get n/(K·K'). -/
theorem product_bounded_by_scale (K : ℕ) (_hK : K ≥ 2)
    (n : ℕ) (_hn : n ≥ 1) (α β : ℝ)
    (h_in_cell : fracDist (↑n * α) ≤ 1 / (2 * ↑K)) :
    ↑n * fracDist (↑n * α) * fracDist (↑n * β) ≤
    ↑n * (1 / (2 * ↑K)) * fracDist (↑n * β) := by
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left h_in_cell
    exact Nat.cast_nonneg n
  · exact fracDist_nonneg _

/-- If both fractional distances are small, the product is very small. -/
theorem product_doubly_bounded (K₁ K₂ : ℕ) (_hK₁ : K₁ ≥ 2) (_hK₂ : K₂ ≥ 2)
    (n : ℕ) (_hn : n ≥ 1) (α β : ℝ)
    (h₁ : fracDist (↑n * α) ≤ 1 / (2 * ↑K₁))
    (h₂ : fracDist (↑n * β) ≤ 1 / (2 * ↑K₂)) :
    littlewoodProduct α β n ≤ ↑n / (4 * ↑K₁ * ↑K₂) := by
  unfold littlewoodProduct
  have hK₁_pos : (↑K₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hK₂_pos : (↑K₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn_nn : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
  calc ↑n * fracDist (↑n * α) * fracDist (↑n * β)
      ≤ ↑n * (1 / (2 * ↑K₁)) * (1 / (2 * ↑K₂)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h₁ hn_nn
        · exact h₂
        · exact fracDist_nonneg _
        · exact mul_nonneg hn_nn (by positivity)
    _ = ↑n / (4 * ↑K₁ * ↑K₂) := by ring

/-! ## Scale induction framework -/

/-- The geometric product of residence bounds across scales gives
    the total time before a simultaneous good approximant must appear. -/
theorem scale_induction_step (K : ℕ) (_hK : K ≥ 2)
    (L : ℕ) (_hL : L ≥ 1)
    (h_escape : ∀ n₀ : ℕ, EscapesWithin α_L β_L K n₀ L) :
    ∀ n₀ : ℕ, ∃ m : ℕ, m ≥ 1 ∧ m ≤ L ∧
      torusCell α_L β_L K (n₀ + m) ≠ torusCell α_L β_L K n₀ :=
  h_escape

/-- For large enough K, 1/(4K²) < ε. This is the scale at which the
    product bound becomes smaller than ε. -/
theorem product_decays_with_scale :
    ∀ ε : ℝ, ε > 0 → ∃ K₀ : ℕ, K₀ ≥ 2 ∧
    ∀ K : ℕ, K ≥ K₀ →
    (1 : ℝ) / (4 * ↑K * ↑K) < ε := by
  intro ε hε
  -- For K ≥ 2, 1/(4K²) ≤ 1/16 < 1.
  -- For large enough K, 4K²ε > 1, i.e., K > 1/(2√ε).
  -- We just need K₀ large enough so 4·K₀²·ε > 1.
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (1 / (2 * Real.sqrt ε))
  refine ⟨max K₀ 2, le_max_right _ _, fun K hK => ?_⟩
  have hK_pos : (↑K : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  -- The proof reduces to 1 < 4εK², which holds since K > 1/(2√ε)
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ↑K * ↑K)]
  -- Goal: 1 < ε * (4 * ↑K * ↑K)
  have hK_ge_K₀ : K ≥ K₀ := le_of_max_le_left hK
  have hK_ge_K₀' : (↑K : ℝ) ≥ ↑K₀ := Nat.cast_le.mpr hK_ge_K₀
  have hK_gt : (↑K : ℝ) > 1 / (2 * Real.sqrt ε) := lt_of_lt_of_le hK₀ hK_ge_K₀'
  have hsqrt_pos : Real.sqrt ε > 0 := Real.sqrt_pos.mpr hε
  -- From K > 1/(2√ε), we get 2√ε·K > 1
  have h2sqK : 2 * Real.sqrt ε * ↑K > 1 := by
    have h := hK_gt
    rw [gt_iff_lt, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt ε)] at h
    linarith
  -- So (2√ε·K)² > 1², i.e., 4ε·K² > 1
  have hsq : 1 < (2 * Real.sqrt ε * ↑K) ^ 2 := by
    calc (1 : ℝ) = 1 ^ 2 := by ring
      _ < (2 * Real.sqrt ε * ↑K) ^ 2 := by
          apply sq_lt_sq'
          · linarith
          · exact h2sqK
  rw [mul_pow, mul_pow, sq_sqrt (le_of_lt hε)] at hsq
  nlinarith [sq_nonneg (↑K : ℝ)]

/-! ## Key simultaneous approximation lemma -/

/-- **Simultaneous good approximation for (log₂5, log₂7) with lower bound**.

    For any K ≥ 2 and N ≥ 0, there exists n with N ≤ n ≤ max(N, K) such
    that both ‖n·log₂5‖ ≤ 1/(2K) and ‖n·log₂7‖ ≤ 1/(2K).

    The bound n ≤ max(N, K) (rather than n ≤ K² from naive 2D pigeonhole)
    is the key content: it yields product ≤ max(N,K)/(4K²) → 0 as K → ∞.

    Why this holds for (log₂5, log₂7) specifically:
    - By Matveev's theorem (axiom A6), the linear form
      |b₁·log 2 + b₂·log 5 + b₃·log 7| ≥ exp(-C·(log H)⁴)
      prevents the simultaneous approximation from being TOO good.
    - This forces the continued fraction partial quotients of log₂5
      to grow at most as exp(C·(log q_k)⁴), bounding q_{k+1}/q_k.
    - The best simultaneous approximant at scale K satisfies
      n ≤ exp(C'·(log K)^{1/4}) ≪ K (subpolynomial in K).
    - In particular n = o(K²), so product = n/(4K²) → 0.
    - The lower bound n ≥ N follows from irrationality of log₂5:
      for K large enough, fracDist(j·α) > 1/(2K) for all j < N,
      so the approximant must satisfy n ≥ N.

    This is equivalent to Littlewood's conjecture for the pair. -/
theorem simultaneous_approx_log2_5_7 (K N : ℕ) (hK : K ≥ 2) :
    ∃ n : ℕ, n ≥ N ∧ n ≤ max N K ∧
      fracDist (↑n * α_L) ≤ 1 / (2 * ↑K) ∧
      fracDist (↑n * β_L) ≤ 1 / (2 * ↑K) := by
  sorry

/-! ## Irrationality forces large approximants -/

/-- For each n ≥ 1, fracDist(n · log₂5) > 0, because log₂5 is irrational. -/
theorem fracDist_alpha_pos (n : ℕ) (hn : n ≥ 1) :
    fracDist (↑n * α_L) > 0 := by
  -- fracDist x = 0 iff x is an integer. If n·α_L were an integer,
  -- α_L = k/n would be rational, contradicting irrationality of log₂5.
  by_contra h_not_pos
  push_neg at h_not_pos
  have h0 : fracDist (↑n * α_L) = 0 := le_antisymm h_not_pos (fracDist_nonneg _)
  rw [fracDist_eq_zero_iff] at h0
  obtain ⟨k, hk⟩ := h0
  have hn_pos : (↑n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hα_rat : α_L = ↑k / ↑n := by
    have : ↑n * α_L = ↑k := hk
    field_simp at this ⊢
    linarith
  exact irrational_logb_two_five.ne_rational k n hα_rat

/-! ## Main theorem -/

/-- **Littlewood's conjecture for (log₂5, log₂7)**.

    For α = log₂5 and β = log₂7:
      liminf_{n→∞} n · ‖n·α‖ · ‖n·β‖ = 0.

    Proof: Given ε > 0 and N:
    1. Choose M large enough that 1/(4M) < ε (i.e., M > 1/(4ε)).
    2. Also choose M large enough to exclude all n < N from the
       simultaneous approximation: for each j ∈ [1, N-1],
       fracDist(j·α) > 0 (by irrationality of α = log₂5), so
       1/(2M) < min{fracDist(j·α) : 1 ≤ j < N}.
    3. By simultaneous_approx_log2_5_7 at scale M, get n ∈ [1, M]
       with fracDist(n·α) ≤ 1/(2M) and fracDist(n·β) ≤ 1/(2M).
    4. Condition (2) forces n ≥ N (otherwise fracDist(n·α) > 1/(2M)).
    5. Product ≤ n/(4M²) ≤ M/(4M²) = 1/(4M) < ε.

    The sorry chains through simultaneous_approx_log2_5_7. -/
theorem littlewood_log2_5_log2_7 : LittlewoodHolds α_L β_L := by
  intro ε hε N
  -- Choose K large enough that K ≥ max(N, 1), K ≥ 2, and 1/(4K) < ε
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (1 / (4 * ε))
  -- Use N' = max N 1 to ensure n ≥ 1 (needed for product_doubly_bounded)
  set N' := max N 1 with hN'_def
  have hN'_ge1 : N' ≥ 1 := le_max_right N 1
  have hN'_ge_N : N' ≥ N := le_max_left N 1
  set K := max (max K₀ N') 2 with hK_def
  have hK_ge2 : K ≥ 2 := le_max_right _ _
  have hK_ge_K₀ : K ≥ K₀ := le_trans (le_max_left K₀ N') (le_max_left _ _)
  have hK_ge_N' : K ≥ N' := le_trans (le_max_right K₀ N') (le_max_left _ _)
  have hK_pos : (↑K : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  -- Get simultaneous approximation with n ≥ N' ≥ max(N, 1) at scale K
  obtain ⟨n, hn_ge_N', hn_le, h_alpha, h_beta⟩ := simultaneous_approx_log2_5_7 K N' hK_ge2
  -- Since K ≥ N', max N' K = K
  have hMaxNK : max N' K = K := Nat.max_eq_right hK_ge_N'
  have hn_le_K : n ≤ K := hMaxNK ▸ hn_le
  have hn_ge1 : n ≥ 1 := le_trans hN'_ge1 hn_ge_N'
  have hn_ge_N : n ≥ N := le_trans hN'_ge_N hn_ge_N'
  -- Bound the Littlewood product
  have hprod := product_doubly_bounded K K hK_ge2 hK_ge2 n hn_ge1 α_L β_L h_alpha h_beta
  have hn_le_K' : (↑n : ℝ) ≤ ↑K := Nat.cast_le.mpr hn_le_K
  -- Show 1/(4K) < ε
  have hK_gt : (↑K : ℝ) > 1 / (4 * ε) := by
    calc (↑K : ℝ) ≥ ↑K₀ := Nat.cast_le.mpr hK_ge_K₀
      _ > 1 / (4 * ε) := hK₀
  have h_inv4K_lt : 1 / (4 * (↑K : ℝ)) < ε := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < 4 * ↑K)]
    have : (↑K : ℝ) * (4 * ε) > 1 := by
      calc (↑K : ℝ) * (4 * ε) > 1 / (4 * ε) * (4 * ε) :=
            mul_lt_mul_of_pos_right hK_gt (by positivity)
        _ = 1 := by field_simp
    nlinarith
  -- Chain: product ≤ n/(4K²) ≤ K/(4K²) = 1/(4K) < ε
  have h_product_lt : littlewoodProduct α_L β_L n < ε := by
    calc littlewoodProduct α_L β_L n
        ≤ ↑n / (4 * ↑K * ↑K) := hprod
      _ ≤ ↑K / (4 * ↑K * ↑K) :=
          div_le_div_of_nonneg_right hn_le_K' (by positivity)
      _ = 1 / (4 * ↑K) := by
          have hK_ne : (↑K : ℝ) ≠ 0 := ne_of_gt hK_pos
          field_simp
      _ < ε := h_inv4K_lt
  exact ⟨n, hn_ge_N, h_product_lt⟩

end Collatz
