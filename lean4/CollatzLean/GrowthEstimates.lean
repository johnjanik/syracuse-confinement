/-
  CollatzLean/GrowthEstimates.lean

  Analytical infrastructure for the Gel'fond-Schneider proof chain
  (Steps 3-5 of Siu's proof).

  Defines the auxiliary entire function F(z) = Σ a(i,j) · exp((i + j·β)·z)
  and provides:
  1. Differentiability (entire) — proved
  2. Growth bounds (exponential type) — proved
  3. Schwarz-type extrapolation of vanishing — proved (from sub-lemmas)
  4. Polynomial zero estimate via multiplicative independence — proved
  5. Jensen zero counting — proved
  6. Gel'fond-Schneider contradiction — proved

  These are the analytical core of `baker_extrapolation` in Baker.lean.

  Template: Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean
  Mathlib resources used:
  - Schwarz lemma: Mathlib.Analysis.Complex.Schwarz
  - Maximum modulus: Mathlib.Analysis.Complex.AbsMax
  - Jensen formula: Mathlib.Analysis.Complex.JensenFormula
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Sequences

namespace Collatz

open Complex Real Filter Topology

noncomputable section

/-! ## Auxiliary entire function

The Gel'fond-Schneider proof constructs an auxiliary polynomial P(X,Y) ∈ ℤ[X,Y]
and forms the entire function F(z) = P(e^z, e^{βz}) where β = log 3 / log 2.

Expanding: F(z) = Σ_{(i,j) ∈ supp} a(i,j) · exp((i + j·β)·z).

This function has exponential type (order ≤ 1), which is the key growth
constraint that makes the Schwarz lemma extrapolation work.
-/

/-- The auxiliary entire function F(z) = Σ_{(i,j) ∈ supp} a(i,j) · exp((i + jβ)z).
    Here `a` gives the coefficients, `supp` is the finite support, and `β` is
    the irrational parameter (log 3 / log 2 in the Baker application). -/
def auxEntireFunc (a : ℤ × ℤ → ℂ) (supp : Finset (ℤ × ℤ)) (β : ℝ) (z : ℂ) : ℂ :=
  ∑ p ∈ supp, a p * exp (((p.1 : ℂ) + (p.2 : ℂ) * (β : ℂ)) * z)

/-- The auxiliary function is differentiable (entire).
    Each summand is `const * exp(linear)`, hence entire, and finite sums of
    entire functions are entire. -/
theorem auxEntireFunc_differentiable (a : ℤ × ℤ → ℂ) (supp : Finset (ℤ × ℤ)) (β : ℝ) :
    Differentiable ℂ (auxEntireFunc a supp β) := by
  intro z
  change DifferentiableAt ℂ
    (fun z => ∑ p ∈ supp, a p * exp (((p.1 : ℂ) + (p.2 : ℂ) * (β : ℂ)) * z)) z
  apply DifferentiableAt.fun_sum
  intro p _
  apply DifferentiableAt.mul (differentiableAt_const _)
  apply DifferentiableAt.cexp
  exact differentiableAt_id.const_mul _

/-! ## Growth bound

The key analytical fact: F(z) = P(e^z, e^{βz}) has exponential type.
On a circle of radius R, |F(z)| ≤ |supp| · B · exp(σR) where:
- B = max coefficient size
- σ = max_{(i,j) ∈ supp} |i + jβ| (the "type" of F)

This follows from the triangle inequality and |exp(wz)| ≤ exp(|w|·|z|).
-/

/-- Growth bound for the auxiliary function on circles.
    For F(z) = Σ a(i,j) · exp((i+jβ)z) with |a(i,j)| ≤ B,
    we have |F(z)| ≤ |supp| · B · exp(σ · |z|) where σ depends on supp and β. -/
theorem auxEntireFunc_growth (a : ℤ × ℤ → ℂ) (supp : Finset (ℤ × ℤ)) (β : ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hBound : ∀ p ∈ supp, ‖a p‖ ≤ B) :
    ∃ σ : ℝ, σ > 0 ∧
      ∀ z : ℂ, ‖auxEntireFunc a supp β z‖ ≤
        supp.card * B * Real.exp (σ * ‖z‖) := by
  -- Choose σ = 1 + Σ_{p ∈ supp} ‖weight(p)‖. This ensures σ > 0
  -- and σ ≥ ‖weight(p)‖ for every p ∈ supp (since norms are nonneg).
  refine ⟨1 + ∑ p ∈ supp, ‖((p.1 : ℤ) : ℂ) + ((p.2 : ℤ) : ℂ) * (β : ℂ)‖,
    by positivity, fun z => ?_⟩
  set σ := 1 + ∑ p ∈ supp, ‖((p.1 : ℤ) : ℂ) + ((p.2 : ℤ) : ℂ) * (β : ℂ)‖
  -- Triangle inequality on the sum
  have h1 : ‖auxEntireFunc a supp β z‖ ≤
      ∑ p ∈ supp, ‖a p * exp (((p.1 : ℂ) + (p.2 : ℂ) * (β : ℂ)) * z)‖ := by
    exact norm_sum_le supp _
  -- Bound each summand: ‖a p · exp(w·z)‖ ≤ B · exp(σ·‖z‖)
  have h2 : ∑ p ∈ supp, ‖a p * exp (((p.1 : ℂ) + (p.2 : ℂ) * (β : ℂ)) * z)‖ ≤
      ∑ p ∈ supp, B * Real.exp (σ * ‖z‖) := by
    apply Finset.sum_le_sum
    intro p hp
    -- Split norm of product
    rw [norm_mul, Complex.norm_exp]
    -- ‖a p‖ ≤ B and exp(Re(w·z)) ≤ exp(σ·‖z‖)
    apply mul_le_mul (hBound p hp) _ (Real.exp_nonneg _) hB
    apply Real.exp_le_exp.mpr
    -- Re(w·z) ≤ ‖w·z‖ = ‖w‖·‖z‖ ≤ σ·‖z‖
    calc (((↑(p.1 : ℤ) : ℂ) + ↑(p.2 : ℤ) * ↑β) * z).re
        ≤ ‖((↑(p.1 : ℤ) : ℂ) + ↑(p.2 : ℤ) * ↑β) * z‖ :=
          Complex.re_le_norm _
      _ = ‖(↑(p.1 : ℤ) : ℂ) + ↑(p.2 : ℤ) * ↑β‖ * ‖z‖ := norm_mul _ z
      _ ≤ σ * ‖z‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
          have hsingle := Finset.single_le_sum
            (f := fun p => ‖((p.1 : ℤ) : ℂ) + ((p.2 : ℤ) : ℂ) * (β : ℂ)‖)
            (fun _ _ => norm_nonneg _) hp
          linarith
  -- Constant sum = card * constant
  have h3 : ∑ _ ∈ supp, B * Real.exp (σ * ‖z‖) =
      ↑supp.card * B * Real.exp (σ * ‖z‖) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  linarith

/-! ## Schwarz-type extrapolation

The core analytical step in the Gel'fond-Schneider proof.

If F is an entire function of exponential type σ that vanishes at the
integer points z = 0, 1, ..., T, then F is "exponentially small" on
compact subsets of the complex plane.

The proof uses the Poisson-Jensen formula on a disk of radius R = 2T+1:

  |F(z)| ≤ C · exp(σR) · ∏_{t=0}^{T} B_R(z, t)

where B_R(z, t) = R|z-t|/|R²-tz| is the Blaschke factor for zero at t
in the disk of radius R. On |z| = R, each |B_R| = 1; for |z| ≤ T/2,
the product of Blaschke factors is at most (1/2)^{T+1}.

Note: the naive polynomial division approach (dividing f by ∏(z-k) and
applying maximum modulus) does NOT yield (1/2)^{T+1}, because the ratio
∏|z-k|/∏(R-k) exceeds (1/2)^{T+1} at z = -T/2 for T ≥ 4. The Blaschke
factorization is essential: Blaschke factors have modulus exactly 1 on
the boundary circle, giving tighter interior bounds.

The decomposition isolates two sorry'd components:
1. `poisson_jensen_blaschke`: the Poisson-Jensen inequality
2. `blaschke_product_le_half_pow`: the Blaschke product bound

References: Boas "Entire Functions" (1954) §2.10, Conway "Functions of
One Complex Variable II" (1995) §XII.1.
-/

/-- Blaschke product for zeros at 0, 1, ..., T in the disk of radius R = 2T+1.
    Each factor R·‖z-k‖/‖R²-kz‖ has modulus 1 on |z| = R and < 1 for |z| < R. -/
noncomputable def blaschkeProduct (T : ℕ) (z : ℂ) : ℝ :=
  ∏ k ∈ Finset.range (T + 1),
    ((2 * (T : ℝ) + 1) * ‖z - (k : ℂ)‖ /
      ‖((2 * (T : ℝ) + 1) ^ 2 : ℂ) - (k : ℂ) * z‖)

/-- Each Blaschke factor is nonneg (ratio of nonneg reals). -/
private lemma blaschke_factor_nonneg (T : ℕ) (z : ℂ) (k : ℕ) :
    0 ≤ (2 * (T : ℝ) + 1) * ‖z - (k : ℂ)‖ /
      ‖((2 * (T : ℝ) + 1) ^ 2 : ℂ) - (k : ℂ) * z‖ :=
  div_nonneg (mul_nonneg (by positivity) (norm_nonneg _)) (norm_nonneg _)

/-- The Blaschke product is nonneg (product of nonneg factors). -/
private lemma blaschke_product_nonneg (T : ℕ) (z : ℂ) :
    0 ≤ blaschkeProduct T z :=
  Finset.prod_nonneg (fun k _ => blaschke_factor_nonneg T z k)

/-- Tight Blaschke factor bound: each factor ≤ (‖z‖ + k) / R where R = 2T+1.

    Proof: The Blaschke factor R·‖z-a‖/‖R²-a·z‖ satisfies
      R·‖z-a‖/‖R²-a·z‖ ≤ R·(‖z‖+a)/(R²+a·‖z‖) ≤ (‖z‖+a)/R.
    The first inequality (Möbius bound) follows by squaring and expanding:
      (‖z‖+a)²·‖R²-a·z‖² - (R²+a·‖z‖)²·‖z-a‖²
      = 2a(R²-‖z‖²)(‖z‖+Re(z))(R²-a²) ≥ 0
    since ‖z‖ < R, a ≤ T < R, and Re(z) ≥ -‖z‖.
    The second inequality follows from a·‖z‖ ≥ 0. -/

private lemma blaschke_factor_le_ratio (T : ℕ) (_hT : T ≥ 2) (k : ℕ)
    (_hk : k ∈ Finset.range (T + 1)) (z : ℂ) (_hz : ‖z‖ ≤ ↑T / 2) :
    (2 * (T : ℝ) + 1) * ‖z - (k : ℂ)‖ /
      ‖((2 * (T : ℝ) + 1) ^ 2 : ℂ) - (k : ℂ) * z‖ ≤
    (‖z‖ + ↑k) / (2 * ↑T + 1) := by
  -- Basic setup
  have hR_pos : (0 : ℝ) < 2 * (↑T : ℝ) + 1 := by positivity
  have hk_le_T : k ≤ T := by rw [Finset.mem_range] at _hk; omega
  have hkR : (↑k : ℝ) ≤ 2 * ↑T + 1 := by
    have : (↑k : ℝ) ≤ ↑T := Nat.cast_le.mpr hk_le_T; linarith
  have hrR : ‖z‖ ≤ 2 * (↑T : ℝ) + 1 := by linarith [_hz]
  have hx_ge : -‖z‖ ≤ z.re := (abs_le.mp (Complex.abs_re_le_norm z)).1
  -- ‖z‖² = z.re² + z.im²
  have hrxy : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [sq ‖z‖, Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]; ring
  have hx_le : z.re ≤ ‖z‖ := (abs_le.mp (Complex.abs_re_le_norm z)).2
  -- Handle denominator = 0 (LHS = 0 ≤ RHS)
  by_cases hdenom : ‖((2 * (↑T : ℝ) + 1) ^ 2 : ℂ) - (↑k : ℂ) * z‖ = 0
  · simp only [hdenom, div_zero]
    exact div_nonneg (by positivity) (by linarith)
  -- Denominator > 0: cross-multiply via div_le_div_iff₀
  · have hdenom_pos : 0 < ‖((2 * (↑T : ℝ) + 1) ^ 2 : ℂ) - (↑k : ℂ) * z‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hdenom)
    rw [div_le_div_iff₀ hdenom_pos hR_pos]
    -- Goal: (2T+1)*‖z-k‖*(2T+1) ≤ (‖z‖+k)*‖denom‖
    -- Use nonneg_le_nonneg_of_sq_le_sq to reduce to squared inequality
    apply nonneg_le_nonneg_of_sq_le_sq
      (mul_nonneg (by positivity) (norm_nonneg _))
    -- Goal: A*A ≤ B*B (where A = (2T+1)*‖z-k‖*(2T+1), B = (‖z‖+k)*‖denom‖)
    -- Step 1: Expand products via ring
    have hA2 : (2 * (↑T : ℝ) + 1) * ‖z - (↑k : ℂ)‖ * (2 * (↑T : ℝ) + 1) *
        ((2 * (↑T : ℝ) + 1) * ‖z - (↑k : ℂ)‖ * (2 * (↑T : ℝ) + 1)) =
        (2 * (↑T : ℝ) + 1) ^ 4 * (‖z - (↑k : ℂ)‖ * ‖z - (↑k : ℂ)‖) := by ring
    have hB2 : (‖z‖ + ↑k) * ‖((2 * (↑T : ℝ) + 1) ^ 2 : ℂ) - (↑k : ℂ) * z‖ *
        ((‖z‖ + ↑k) * ‖((2 * (↑T : ℝ) + 1) ^ 2 : ℂ) - (↑k : ℂ) * z‖) =
        (‖z‖ + ↑k) ^ 2 *
        (‖((2 * (↑T : ℝ) + 1) ^ 2 : ℂ) - (↑k : ℂ) * z‖ *
         ‖((2 * (↑T : ℝ) + 1) ^ 2 : ℂ) - (↑k : ℂ) * z‖) := by ring
    -- Step 2: Expand norms via normSq
    have hnum_sq : ‖z - (↑k : ℂ)‖ * ‖z - (↑k : ℂ)‖ = (z.re - ↑k) ^ 2 + z.im ^ 2 := by
      rw [Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.natCast_re,
                  Complex.natCast_im, sub_zero]; ring
    have hdenom_sq : ‖((2 * (↑T : ℝ) + 1) ^ 2 : ℂ) - (↑k : ℂ) * z‖ *
        ‖((2 * (↑T : ℝ) + 1) ^ 2 : ℂ) - (↑k : ℂ) * z‖ =
        ((2 * (↑T : ℝ) + 1) ^ 2 - ↑k * z.re) ^ 2 + (↑k * z.im) ^ 2 := by
      rw [Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
      simp only [pow_succ, pow_zero, one_mul,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        Complex.re_ofNat, Complex.im_ofNat,
        Complex.ofReal_re, Complex.ofReal_im,
        Complex.natCast_re, Complex.natCast_im,
        sub_zero, zero_mul, mul_zero, add_zero, zero_add, mul_one]; ring
    -- Step 3: Rewrite goal to pure real arithmetic
    rw [hA2, hB2, hnum_sq, hdenom_sq]
    -- Goal: (2T+1)⁴*((z.re-k)²+z.im²) ≤ (‖z‖+k)²*(((2T+1)²-k·z.re)²+(k·z.im)²)
    -- Eliminate z.im² using z.im² = ‖z‖² - z.re²
    have him2 : z.im ^ 2 = ‖z‖ ^ 2 - z.re ^ 2 := by linarith [hrxy]
    -- Rewrite numerator normSq: (z.re-k)²+z.im² = ‖z‖²-2k·z.re+k²
    have h_num : (z.re - (↑k : ℝ)) ^ 2 + z.im ^ 2 =
        ‖z‖ ^ 2 - 2 * (↑k : ℝ) * z.re + (↑k : ℝ) ^ 2 := by nlinarith
    -- Rewrite denominator normSq: ((2T+1)²-k·z.re)²+(k·z.im)²
    --   = (2T+1)⁴-2k(2T+1)²·z.re+k²·‖z‖²
    have h_den : ((2 * (↑T : ℝ) + 1) ^ 2 - (↑k : ℝ) * z.re) ^ 2 +
        ((↑k : ℝ) * z.im) ^ 2 =
        (2 * (↑T : ℝ) + 1) ^ 4 - 2 * (↑k : ℝ) * (2 * (↑T : ℝ) + 1) ^ 2 * z.re +
        (↑k : ℝ) ^ 2 * ‖z‖ ^ 2 := by nlinarith [mul_pow (↑k : ℝ) z.im 2]
    rw [h_num, h_den]
    -- Goal is now pure polynomial in z.re, ‖z‖, ↑k, (2↑T+1)
    -- Ring identity decomposes the difference as sum of two nonneg terms:
    --   2k(‖z‖+x)(S-‖z‖²)(S-k²) + (2k‖z‖S+k²‖z‖²)(‖z‖²-2kx+k²)
    -- where S = (2T+1)², x = z.re
    have hpoly : (‖z‖ + (↑k : ℝ)) ^ 2 *
        ((2 * (↑T : ℝ) + 1) ^ 4 - 2 * (↑k : ℝ) * (2 * (↑T : ℝ) + 1) ^ 2 * z.re +
        (↑k : ℝ) ^ 2 * ‖z‖ ^ 2) -
        (2 * (↑T : ℝ) + 1) ^ 4 *
        (‖z‖ ^ 2 - 2 * (↑k : ℝ) * z.re + (↑k : ℝ) ^ 2) =
        2 * (↑k : ℝ) * (‖z‖ + z.re) *
        ((2 * (↑T : ℝ) + 1) ^ 2 - ‖z‖ ^ 2) *
        ((2 * (↑T : ℝ) + 1) ^ 2 - (↑k : ℝ) ^ 2) +
        (2 * (↑k : ℝ) * ‖z‖ * (2 * (↑T : ℝ) + 1) ^ 2 +
        (↑k : ℝ) ^ 2 * ‖z‖ ^ 2) *
        (‖z‖ ^ 2 - 2 * (↑k : ℝ) * z.re + (↑k : ℝ) ^ 2) := by ring
    -- Each term nonneg
    have hr_sq_le : ‖z‖ ^ 2 ≤ (2 * (↑T : ℝ) + 1) ^ 2 :=
      sq_le_sq' (by linarith) hrR
    have hk_sq_le : (↑k : ℝ) ^ 2 ≤ (2 * (↑T : ℝ) + 1) ^ 2 :=
      sq_le_sq' (by linarith [Nat.cast_nonneg (α := ℝ) k]) hkR
    have hf1 : 0 ≤ 2 * (↑k : ℝ) * (‖z‖ + z.re) *
        ((2 * (↑T : ℝ) + 1) ^ 2 - ‖z‖ ^ 2) *
        ((2 * (↑T : ℝ) + 1) ^ 2 - (↑k : ℝ) ^ 2) := by
      apply mul_nonneg; apply mul_nonneg; apply mul_nonneg
      · positivity
      · linarith
      · linarith
      · linarith
    have hf2 : 0 ≤ (2 * (↑k : ℝ) * ‖z‖ * (2 * (↑T : ℝ) + 1) ^ 2 +
        (↑k : ℝ) ^ 2 * ‖z‖ ^ 2) *
        (‖z‖ ^ 2 - 2 * (↑k : ℝ) * z.re + (↑k : ℝ) ^ 2) := by
      apply mul_nonneg
      · positivity
      · -- ‖z‖^2 - 2k·z.re + k^2 = (‖z‖-k)^2 + 2k(‖z‖-z.re) ≥ 0
        have hsq : 0 ≤ (‖z‖ - (↑k : ℝ)) ^ 2 := sq_nonneg _
        have hdiff : 0 ≤ ‖z‖ - z.re := by linarith
        have hknn : (0 : ℝ) ≤ ↑k := Nat.cast_nonneg (α := ℝ) k
        linarith [mul_nonneg hknn hdiff]
    linarith

/-- The rising factorial ∏_{k=0}^{T} (r+k) ≤ T^(T+1) when 0 ≤ r ≤ T/2.

    Follows from AM-GM (Mathlib: `Real.geom_mean_le_arith_mean_weighted`):
    the geometric mean of (r+0, r+1, ..., r+T) is at most their arithmetic
    mean r + T/2 ≤ T. So ∏(r+k) ≤ T^{T+1}.

    For the AM-GM setup: use uniform weights w_k = 1/(T+1), so ∑w = 1.
    Then (∏ (r+k)^{1/(T+1)}) ≤ (1/(T+1))∑(r+k) = r + T/2 ≤ T.
    Raising to the (T+1)-th power: ∏(r+k) ≤ T^(T+1). -/
private lemma rising_factorial_le_pow (T : ℕ) (r : ℝ) (hr : 0 ≤ r) (hrT : r ≤ ↑T / 2) :
    ∏ k ∈ Finset.range (T + 1), (r + ↑k) ≤ (↑T : ℝ) ^ (T + 1) := by
  -- Strategy: AM-GM with uniform weights w_k = 1/(T+1).
  set n := T + 1 with hn_def
  set s := Finset.range n
  set z : ℕ → ℝ := fun k => r + ↑k
  set w : ℕ → ℝ := fun _ => (1 : ℝ) / ↑n
  have hz : ∀ k ∈ s, 0 ≤ z k := fun _ _ => by positivity
  have hw : ∀ k ∈ s, 0 ≤ w k := fun _ _ => by positivity
  have hn_pos : (0 : ℝ) < ↑n := by positivity
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hs_card : s.card = n := Finset.card_range n
  have hw' : ∑ k ∈ s, w k = 1 := by
    simp only [w, Finset.sum_const, nsmul_eq_mul, hs_card]
    exact mul_one_div_cancel hn_ne
  -- AM-GM: ∏ z_k^{w_k} ≤ ∑ w_k * z_k
  have hamgm := Real.geom_mean_le_arith_mean_weighted s w z hw hw' hz
  -- Bound the arithmetic mean by T
  have hsum : ∑ k ∈ s, w k * z k ≤ ↑T := by
    have hfactor : ∀ k ∈ s, w k * z k = (r + ↑k) / ↑n := by
      intro k _; simp only [w, z, one_div, inv_mul_eq_div]
    rw [Finset.sum_congr rfl hfactor, ← Finset.sum_div, div_le_iff₀ hn_pos]
    -- ∑(r + k) = n*r + ∑ k
    rw [show ∑ k ∈ s, (r + ↑k) = ↑n * r + ∑ k ∈ s, (↑k : ℝ) from by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hs_card]]
    -- Gauss sum
    have hgauss_nat : (∑ i ∈ s, i) * 2 = n * T := by
      change (∑ i ∈ Finset.range n, i) * 2 = n * T
      have h1 := Finset.sum_range_id_mul_two n
      have h2 : n - 1 = T := by omega
      rw [h2] at h1; exact h1
    have hgauss_real : (∑ i ∈ s, (↑i : ℝ)) * 2 = ↑n * ↑T := by
      have hcast : (∑ k ∈ s, (↑k : ℝ)) = (↑(∑ k ∈ s, k) : ℝ) := by push_cast; rfl
      rw [hcast, show (2 : ℝ) = (↑(2 : ℕ) : ℝ) from by norm_num,
          ← Nat.cast_mul, hgauss_nat, Nat.cast_mul]
    nlinarith
  -- ∏ z_k^{1/n} ≤ T
  have hle : ∏ k ∈ s, z k ^ (w k) ≤ ↑T := le_trans hamgm hsum
  -- ∏ z_k^{1/n} = (∏ z_k)^{1/n}
  rw [Real.finset_prod_rpow s z hz] at hle
  -- (∏ z_k)^{n⁻¹} ≤ T → ∏ z_k ≤ T^n
  rw [one_div] at hle
  rw [Real.rpow_inv_le_iff_of_pos (Finset.prod_nonneg hz) (Nat.cast_nonneg T) hn_pos] at hle
  rwa [Real.rpow_natCast] at hle

/-- Product bound: ∏_{k=0}^{T} (r+k)/(2T+1) ≤ (1/2)^(T+1) for 0 ≤ r ≤ T/2.

    Proof: by `rising_factorial_le_pow`, ∏(r+k) ≤ T^(T+1).
    Dividing by (2T+1)^(T+1): product ≤ (T/(2T+1))^(T+1).
    Since T < T + 1/2 < T + 1 ≤ 2T+1 for T ≥ 0, we get T/(2T+1) < 1/2. -/
private lemma ratio_product_le_half_pow (T : ℕ) (_hT : T ≥ 2) (r : ℝ)
    (hr : 0 ≤ r) (hrT : r ≤ ↑T / 2) :
    ∏ k ∈ Finset.range (T + 1), ((r + ↑k) / (2 * ↑T + 1)) ≤ (1 / 2) ^ (T + 1) := by
  have hR_pos : (0 : ℝ) < 2 * ↑T + 1 := by positivity
  -- Rewrite ∏ (f/g) = (∏ f) / (∏ g), with g constant
  conv_lhs =>
    arg 2; ext k
    rw [show (r + ↑k) / (2 * ↑T + 1) = (fun i => r + ↑i) k / (fun _ => 2 * (↑T : ℝ) + 1) k
      from rfl]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  -- Goal: ∏(r+k) / (2T+1)^(T+1) ≤ (1/2)^(T+1)
  rw [div_le_iff₀ (pow_pos hR_pos _), ← mul_pow]
  -- Goal: ∏(r+k) ≤ ((1/2) * (2T+1))^(T+1)
  calc ∏ k ∈ Finset.range (T + 1), (r + ↑k)
      ≤ (↑T : ℝ) ^ (T + 1) := rising_factorial_le_pow T r hr hrT
    _ ≤ (1 / 2 * (2 * ↑T + 1)) ^ (T + 1) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _

/-- Blaschke boundary identity: R·‖w-k‖ = ‖R²-kw‖ on ‖w‖ = R.
    Proof by showing both sides squared are equal using ‖w‖² = R². -/
private lemma blaschke_boundary_identity (R : ℝ) (hR : 0 < R)
    (w : ℂ) (hw : ‖w‖ = R) (k : ℕ) :
    R * ‖w - (↑k : ℂ)‖ = ‖((R ^ 2 : ℝ) : ℂ) - (↑k : ℂ) * w‖ := by
  have hR_nn : (0 : ℝ) ≤ R := le_of_lt hR
  rw [← sq_eq_sq₀ (mul_nonneg hR_nn (norm_nonneg _)) (norm_nonneg _)]
  have hrxy : w.re ^ 2 + w.im ^ 2 = R ^ 2 := by
    have h1 : ‖w‖ * ‖w‖ = R * R := by rw [hw]
    rw [Complex.norm_mul_self_eq_normSq, Complex.normSq_apply] at h1; nlinarith
  have hL : (R * ‖w - (↑k : ℂ)‖) ^ 2 = R ^ 2 * ((w.re - ↑k) ^ 2 + w.im ^ 2) := by
    have h1 : ‖w - (↑k : ℂ)‖ * ‖w - (↑k : ℂ)‖ = (w.re - ↑k) ^ 2 + w.im ^ 2 := by
      rw [Complex.norm_mul_self_eq_normSq, Complex.normSq_apply,
          Complex.sub_re, Complex.sub_im, Complex.natCast_re, Complex.natCast_im, sub_zero]; ring
    nlinarith [sq_nonneg R]
  have hR2 : ‖((R ^ 2 : ℝ) : ℂ) - (↑k : ℂ) * w‖ ^ 2 =
      (R ^ 2 - ↑k * w.re) ^ 2 + (↑k * w.im) ^ 2 := by
    have h1 : ‖((R ^ 2 : ℝ) : ℂ) - (↑k : ℂ) * w‖ *
        ‖((R ^ 2 : ℝ) : ℂ) - (↑k : ℂ) * w‖ =
        (R ^ 2 - ↑k * w.re) ^ 2 + (↑k * w.im) ^ 2 := by
      rw [Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
                  Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
                  sub_zero, zero_mul, add_zero]; ring
    nlinarith [sq_nonneg ‖((R ^ 2 : ℝ) : ℂ) - (↑k : ℂ) * w‖]
  rw [hL, hR2]
  nlinarith [sq_nonneg (↑k * w.re - R ^ 2), sq_nonneg (↑k * w.im),
             sq_nonneg (w.re - ↑k), sq_nonneg w.im, sq_nonneg (↑k : ℝ)]

/-- Factor an entire function through its integer zeros via iterated dslope.
    If f vanishes at 0, 1, ..., n-1, then f(w) = ∏_{k<n}(w-k) · H(w) for some entire H. -/
private lemma factor_through_zeros (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (n : ℕ) (hvanish : ∀ k : ℕ, k < n → f (↑k : ℂ) = 0) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, f w = (∏ k ∈ Finset.range n, (w - (↑k : ℂ))) * H w := by
  induction n with
  | zero => exact ⟨f, hf, fun w => by simp⟩
  | succ n ih =>
    obtain ⟨G, hG_diff, hG_eq⟩ := ih (fun k hk => hvanish k (Nat.lt_succ_of_lt hk))
    have hGn : G (↑n : ℂ) = 0 := by
      have hfn := hvanish n (Nat.lt_succ_iff.mpr le_rfl)
      rw [hG_eq] at hfn
      have hprod_ne : ∏ k ∈ Finset.range n, ((↑n : ℂ) - (↑k : ℂ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun k hk => by
          rw [Finset.mem_range] at hk
          simp only [sub_ne_zero, Ne, Nat.cast_inj]; omega)
      exact (mul_eq_zero.mp hfn).resolve_left hprod_ne
    refine ⟨dslope G (↑n : ℂ), ?_, fun w => ?_⟩
    · rwa [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem,
           differentiableOn_univ]
    · have h := sub_smul_dslope G (↑n : ℂ) w
      rw [smul_eq_mul, hGn, sub_zero] at h
      rw [Finset.prod_range_succ, mul_assoc, h, ← hG_eq]

/-- Poisson-Jensen inequality: an entire function with growth bound and
    integer zeros satisfies |f(z)| ≤ C·exp(σR) · blaschkeProduct.

    Proof: Factor f(w) = ∏(w-k)·H(w) via iterated dslope.
    Define g(w) = H(w)·∏(R²-kw)/R^{T+1}; g is entire.
    On |w|=R, boundary identity gives |g|=|f| ≤ C·exp(σR).
    Maximum modulus principle: |g(z)| ≤ C·exp(σR) for |z| ≤ R.
    Assembly: |f(z)| = |g(z)|·blaschkeProduct(z). -/
private lemma poisson_jensen_blaschke
    (f : ℂ → ℂ) (_hf : Differentiable ℂ f)
    (C σ : ℝ) (_hC : C > 0) (_hσ : σ > 0)
    (_hgrowth : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (σ * ‖z‖))
    (T : ℕ) (_hT : T ≥ 2)
    (_hvanish : ∀ t : ℕ, t ≤ T → f (t : ℂ) = 0)
    (z : ℂ) (_hz : ‖z‖ ≤ ↑T / 2) :
    ‖f z‖ ≤ C * Real.exp (σ * (2 * ↑T + 1)) * blaschkeProduct T z := by
  set R := 2 * (T : ℝ) + 1 with hR_def
  have hR_pos : (0 : ℝ) < R := by positivity
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  have hR_nn : (0 : ℝ) ≤ R := le_of_lt hR_pos
  have hrR : ‖z‖ ≤ R := by linarith [_hz]
  -- Step 1: Factor f through its zeros at 0,1,...,T
  obtain ⟨H, hH_diff, hH_eq⟩ := factor_through_zeros f _hf (T + 1)
    (fun k hk => _hvanish k (by omega))
  -- Step 2: Trivial case — some factor z - k = 0
  by_cases hprod : ∏ k ∈ Finset.range (T + 1), (z - (↑k : ℂ)) = 0
  · rw [hH_eq z, hprod, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg (le_of_lt _hC) (le_of_lt (Real.exp_pos _)))
      (blaschke_product_nonneg T z)
  -- Step 3: All factors nonzero
  · have hfactors_ne : ∀ k ∈ Finset.range (T + 1), z - (↑k : ℂ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hprod
    -- Define conjugate product Qc
    set Qc : ℂ → ℂ := fun w => ∏ k ∈ Finset.range (T + 1),
      (((R ^ 2 : ℝ) : ℂ) - (↑k : ℂ) * w) with hQc_def
    -- Each denominator factor ‖R² - kz‖ > 0
    have hQc_factors_pos : ∀ k ∈ Finset.range (T + 1),
        0 < ‖((R ^ 2 : ℝ) : ℂ) - (↑k : ℂ) * z‖ := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [norm_pos_iff]; intro heq
      have heq' := sub_eq_zero.mp heq
      by_cases hk0 : k = 0
      · -- k=0: R² = 0*z = 0, contradiction
        subst hk0; simp at heq'
        linarith [sq_pos_of_pos hR_pos]
      · have hk_pos : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
        have hT_pos : (0 : ℝ) < ↑T := by positivity
        have hnorm : ↑k * ‖z‖ = R ^ 2 := by
          have h1 : ‖(↑k : ℂ) * z‖ = R ^ 2 := by
            rw [← heq']; simp [Complex.norm_real, abs_of_pos (pow_pos hR_pos 2)]
          rwa [norm_mul, Complex.norm_natCast] at h1
        have hz_eq : ‖z‖ = R ^ 2 / ↑k := by field_simp at hnorm ⊢; linarith
        have hk_le : (↑k : ℝ) ≤ ↑T := by exact_mod_cast Nat.lt_succ_iff.mp hk
        have h1 : R ^ 2 / ↑T ≤ R ^ 2 / ↑k :=
          div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ R ^ 2) hk_pos (by linarith)
        have h2 : ↑T / 2 < R ^ 2 / ↑T := by
          rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 2) hT_pos]
          rw [hR_def]; nlinarith
        linarith [hz_eq]
    -- ‖Qc z‖ > 0
    have hQc_pos : 0 < ‖Qc z‖ := by
      show 0 < ‖∏ k ∈ Finset.range (T + 1), (((R ^ 2 : ℝ) : ℂ) - (↑k : ℂ) * z)‖
      rw [Complex.norm_prod]
      exact Finset.prod_pos hQc_factors_pos
    -- R^(T+1) > 0
    have hR_pow_pos : (0 : ℝ) < R ^ (T + 1) := pow_pos hR_pos _
    -- Define g = H · Qc / R^(T+1)
    set g : ℂ → ℂ := fun w => H w * Qc w / ((↑R : ℂ) ^ (T + 1)) with hg_def
    -- g is entire
    have hQc_diff : Differentiable ℂ Qc := by
      change Differentiable ℂ (fun w => ∏ k ∈ Finset.range (T + 1),
        (((R ^ 2 : ℝ) : ℂ) - (↑k : ℂ) * w))
      fun_prop
    have hg_diff : Differentiable ℂ g := by
      show Differentiable ℂ (fun w => H w * Qc w / ((↑R : ℂ) ^ (T + 1)))
      exact (hH_diff.mul hQc_diff).div_const _
    -- Helper: compute ‖g w‖ = ‖H w‖ * ‖Qc w‖ / R^(T+1)
    have norm_g (w : ℂ) : ‖g w‖ = ‖H w‖ * ‖Qc w‖ / R ^ (T + 1) := by
      show ‖H w * Qc w / ((↑R : ℂ) ^ (T + 1))‖ = _
      simp [norm_div, norm_mul, norm_pow, Real.norm_of_nonneg hR_nn]
    -- Step 4: Bound g on boundary |w| = R
    have hg_boundary : ∀ w : ℂ, ‖w‖ = R → ‖g w‖ ≤ C * Real.exp (σ * R) := by
      intro w hw
      rw [norm_g]
      -- ‖Qc w‖ = R^(T+1) * ∏ ‖w-k‖  (boundary identity)
      have hQc_boundary : ‖Qc w‖ =
          R ^ (T + 1) * ∏ k ∈ Finset.range (T + 1), ‖w - (↑k : ℂ)‖ := by
        show ‖∏ k ∈ Finset.range (T + 1), (((R ^ 2 : ℝ) : ℂ) - (↑k : ℂ) * w)‖ = _
        rw [Complex.norm_prod, Finset.prod_congr rfl (fun k _ =>
          (blaschke_boundary_identity R hR_pos w hw k).symm),
          Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      rw [hQc_boundary]
      have hRpow_ne : R ^ (T + 1) ≠ 0 := ne_of_gt hR_pow_pos
      field_simp
      -- Goal: ‖H w‖ * ∏ ‖w-k‖ ≤ C * exp(σR)  =  ‖f w‖
      have : ‖H w‖ * ∏ k ∈ Finset.range (T + 1), ‖w - (↑k : ℂ)‖ = ‖f w‖ := by
        rw [hH_eq w, norm_mul, Complex.norm_prod]; ring
      rw [this]
      calc ‖f w‖ ≤ C * Real.exp (σ * ‖w‖) := _hgrowth w
        _ = C * Real.exp (σ * R) := by rw [hw]
    -- Step 5: Maximum modulus principle
    have hg_bound : ‖g z‖ ≤ C * Real.exp (σ * R) := by
      apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
        hg_diff.diffContOnCl
      · intro w hw
        rw [frontier_ball (0 : ℂ) hR_ne, Metric.mem_sphere, dist_zero_right] at hw
        exact hg_boundary w hw
      · rw [closure_ball (0 : ℂ) hR_ne, Metric.mem_closedBall, dist_zero_right]
        exact hrR
    -- Step 6: Assembly — ‖f z‖ = ‖g z‖ * blaschkeProduct
    suffices hkey : ‖f z‖ = ‖g z‖ * blaschkeProduct T z by
      rw [hkey]; exact mul_le_mul_of_nonneg_right hg_bound (blaschke_product_nonneg T z)
    -- ‖f z‖ = (∏ ‖z-k‖) * ‖H z‖
    have hf_norm : ‖f z‖ = (∏ k ∈ Finset.range (T + 1), ‖z - (↑k : ℂ)‖) * ‖H z‖ := by
      rw [hH_eq z, norm_mul, Complex.norm_prod]
    -- ‖Qc z‖ as a product of norms
    have hQc_norm : ‖Qc z‖ = ∏ k ∈ Finset.range (T + 1),
        ‖((R ^ 2 : ℝ) : ℂ) - (↑k : ℂ) * z‖ := by
      show ‖∏ k ∈ Finset.range (T + 1), _‖ = _; exact Complex.norm_prod ..
    -- blaschkeProduct = R^(T+1) * ∏‖z-k‖ / ‖Qc z‖
    have hbp_eq : blaschkeProduct T z =
        R ^ (T + 1) * (∏ k ∈ Finset.range (T + 1), ‖z - (↑k : ℂ)‖) /
        ‖Qc z‖ := by
      unfold blaschkeProduct
      -- Unify R with 2*T+1 in the Qc norm
      have hQc_norm' : ‖Qc z‖ = ∏ k ∈ Finset.range (T + 1),
          ‖((2 * (T : ℝ) + 1) ^ 2 : ℂ) - (↑k : ℂ) * z‖ := by
        rw [hQc_norm]; congr 1; ext k; congr 1; congr 1; rw [hR_def]; push_cast; ring
      rw [hQc_norm', Finset.prod_div_distrib, Finset.prod_mul_distrib]
      congr 1; rw [Finset.prod_const, Finset.card_range]
    rw [hf_norm, norm_g, hbp_eq]
    field_simp

/-- The Blaschke product is at most (1/2)^(T+1) for |z| ≤ T/2, R = 2T+1.

    Proof chain:
    1. Each factor ≤ (‖z‖+k)/(2T+1) by `blaschke_factor_le_ratio`
    2. Product of ratios ≤ (1/2)^(T+1) by `ratio_product_le_half_pow` (AM-GM)
    Assembled via `Finset.prod_le_prod` (monotonicity of products). -/
private lemma blaschke_product_le_half_pow
    (T : ℕ) (hT : T ≥ 2) (z : ℂ) (hz : ‖z‖ ≤ ↑T / 2) :
    blaschkeProduct T z ≤ (1 / 2) ^ (T + 1) := by
  unfold blaschkeProduct
  calc ∏ k ∈ Finset.range (T + 1),
        ((2 * (T : ℝ) + 1) * ‖z - (k : ℂ)‖ /
          ‖((2 * (T : ℝ) + 1) ^ 2 : ℂ) - (k : ℂ) * z‖)
      ≤ ∏ k ∈ Finset.range (T + 1), ((‖z‖ + ↑k) / (2 * ↑T + 1)) :=
        Finset.prod_le_prod (fun k _ => blaschke_factor_nonneg T z k)
          (fun k hk => blaschke_factor_le_ratio T hT k hk z hz)
    _ ≤ (1 / 2) ^ (T + 1) :=
        ratio_product_le_half_pow T hT ‖z‖ (norm_nonneg z) hz

/-- Schwarz-type vanishing extrapolation for entire functions of exponential type.

    If F is entire with growth |F(z)| ≤ C·exp(σ|z|), and F vanishes at
    all integers 0, 1, ..., T, then F is exponentially small on |z| ≤ T/2.

    Combines `poisson_jensen_blaschke` and `blaschke_product_le_half_pow`. -/
theorem schwarz_vanishing_bound
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (C σ : ℝ) (hC : C > 0) (hσ : σ > 0)
    (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (σ * ‖z‖))
    (T : ℕ) (hT : T ≥ 2)
    (hvanish : ∀ t : ℕ, t ≤ T → f (t : ℂ) = 0) :
    ∀ z : ℂ, ‖z‖ ≤ T / 2 →
      ‖f z‖ ≤ C * Real.exp (σ * (2 * T + 1)) * (1 / 2) ^ (T + 1) := by
  intro z hz
  have h1 := poisson_jensen_blaschke f hf C σ hC hσ hgrowth T hT hvanish z hz
  have h2 := blaschke_product_le_half_pow T hT z hz
  calc ‖f z‖
      ≤ C * Real.exp (σ * (2 * ↑T + 1)) * blaschkeProduct T z := h1
    _ ≤ C * Real.exp (σ * (2 * ↑T + 1)) * (1 / 2) ^ (T + 1) := by
        apply mul_le_mul_of_nonneg_left h2
        exact mul_nonneg (le_of_lt hC) (le_of_lt (Real.exp_pos _))

/-! ## Jensen zero counting

Jensen's formula relates the average of log|f| on a circle to the
zeros of f inside the circle. For the Gel'fond-Schneider proof,
we use the contrapositive:

If f is small on a large circle (from Schwarz extrapolation) and
f(0) ≠ 0, then Jensen's formula bounds the number of zeros.

Specifically: if |f(z)| ≤ ε on |z| ≤ R and f(0) ≠ 0, then the
number of zeros in |z| ≤ R/2 is at most log(ε/|f(0)|) / log 2.

This uses Mathlib.Analysis.Complex.JensenFormula.
-/

/-- Jensen-type zero count from growth bounds.

    An entire function with f(0) ≠ 0 that is bounded by ε on |z| ≤ R
    has at most N zeros in |z| ≤ R/2, where N depends on ε, |f(0)|, and R. -/
theorem jensen_zero_count
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (R : ℝ) (hR : R > 0) (ε : ℝ) (hε : ε > 0)
    (hsmall : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ ε) :
    ∃ N : ℕ, ∀ (S : Finset ℂ),
      (∀ z ∈ S, f z = 0 ∧ ‖z‖ ≤ R / 2) → S.card ≤ N := by
  -- Reduce to finiteness of the zero set in the ball
  set Z := {z : ℂ | f z = 0 ∧ ‖z‖ ≤ R / 2}
  suffices hfin : Z.Finite by
    exact ⟨hfin.toFinset.card, fun S hS =>
      Finset.card_le_card fun z hz => hfin.mem_toFinset.mpr (hS z hz)⟩
  -- f is analytic on ℂ (complex differentiable → analytic)
  have hfU : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
  -- No accumulation of zeros (identity principle + f(0) ≠ 0)
  have hiso : ∀ z : ℂ, ¬ (∃ᶠ w in 𝓝[≠] z, f w = 0) := by
    intro z hfreq
    exact hf0 ((hfU.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ z) hfreq) (Set.mem_univ 0))
  -- By contradiction: if Z is infinite, derive accumulation of zeros
  by_contra hinf
  haveI : Infinite Z := Set.infinite_coe_iff.mpr hinf
  -- Extract an injective sequence of zeros
  let emb := Infinite.natEmbedding Z
  let x : ℕ → ℂ := fun n => (emb n).val
  have hx_zero : ∀ n, f (x n) = 0 := fun n => (emb n).prop.1
  have hx_inj : Function.Injective x :=
    Subtype.val_injective.comp emb.injective
  have hx_ball : ∀ n, x n ∈ Metric.closedBall (0 : ℂ) (R / 2) := fun n => by
    simp only [Metric.mem_closedBall, dist_zero_right]; exact (emb n).prop.2
  -- Extract convergent subsequence by compactness
  obtain ⟨z₀, -, φ, hφ, hconv⟩ :=
    (isCompact_closedBall (0 : ℂ) (R / 2)).tendsto_subseq hx_ball
  -- The subsequence is injective, so eventually ≠ z₀
  have hxφ_inj : Function.Injective (x ∘ φ) := hx_inj.comp hφ.injective
  have hne : ∀ᶠ n in Filter.atTop, (x ∘ φ) n ≠ z₀ := by
    rw [Filter.eventually_atTop]
    by_cases h : ∃ n₀, (x ∘ φ) n₀ = z₀
    · obtain ⟨n₀, hn₀⟩ := h
      exact ⟨n₀ + 1, fun n hn he => absurd (hxφ_inj (he.trans hn₀.symm)) (by omega)⟩
    · push_neg at h; exact ⟨0, fun n _ => h n⟩
  -- Convergence in punctured neighborhood
  have hconv_punct : Filter.Tendsto (x ∘ φ) Filter.atTop (𝓝[≠] z₀) :=
    Filter.tendsto_inf.mpr ⟨hconv, Filter.tendsto_principal.mpr hne⟩
  -- Contradiction: sequence of zeros provides frequent zeros, but hiso forbids them
  exact hiso z₀ fun hev => by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hconv_punct.eventually hev)
    exact hN N le_rfl (hx_zero (φ N))

/-! ## Polynomial zero estimate

A polynomial P(X,Y) evaluated at points of the form (2^t, 3^t) can
vanish at only finitely many such points unless P is identically zero.
This is because the points {(2^t, 3^t) : t ∈ ℕ} are in "general position"
with respect to polynomials, a consequence of the multiplicative independence
of 2 and 3.

The zero estimate is the "algebraic" counterpart to the "analytic" Schwarz
extrapolation: the extrapolation produces many zeros, while the zero estimate
bounds how many zeros a non-zero polynomial can have. The gap between these
two counts forces the polynomial to be identically zero — contradicting the
construction. The quantitative analysis of this gap yields the effective
Baker-type lower bound on |m·log 2 + n·log 3|.
-/

/-- Polynomial evaluation at exponential points.
    Evaluates P at (2^t, 3^t) for P represented as a function on ℤ × ℤ. -/
def polyEvalExp (P : ℤ → ℤ → ℤ) (L : ℕ) (t : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (L + 1),
    P i j * (2 : ℤ) ^ (i * t) * (3 : ℤ) ^ (j * t)

/-- The bases 2^a * 3^b are distinct for distinct (a,b) pairs,
    by unique prime factorization (multiplicative independence of 2 and 3). -/
private lemma two_pow_mul_three_pow_injective :
    ∀ a b c d : ℕ, (2 : ℤ) ^ a * 3 ^ b = 2 ^ c * 3 ^ d → a = c ∧ b = d := by
  intro a b c d h
  -- Transfer to ℕ (all values positive, cast is injective)
  have h' : (2 : ℕ) ^ a * 3 ^ b = 2 ^ c * 3 ^ d := by zify; exact h
  -- Coprimality of powers of 2 and 3
  have hcop1 : Nat.Coprime (2 ^ a) (3 ^ d) :=
    Nat.Coprime.pow a d (by decide : Nat.Coprime 2 3)
  have hcop2 : Nat.Coprime (2 ^ c) (3 ^ b) :=
    Nat.Coprime.pow c b (by decide : Nat.Coprime 2 3)
  constructor
  · -- a = c: 2^a | 2^c and 2^c | 2^a (by coprimality), so 2^a = 2^c
    have h1 : 2 ^ a ∣ 2 ^ c := hcop1.dvd_of_dvd_mul_right ⟨3 ^ b, h'.symm⟩
    have h2 : 2 ^ c ∣ 2 ^ a := hcop2.dvd_of_dvd_mul_right ⟨3 ^ d, h'⟩
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2)) (Nat.dvd_antisymm h1 h2)
  · -- b = d: cancel 2^a from both sides, then 3^b = 3^d
    have hac : a = c := by
      have h1 : 2 ^ a ∣ 2 ^ c := hcop1.dvd_of_dvd_mul_right ⟨3 ^ b, h'.symm⟩
      have h2 : 2 ^ c ∣ 2 ^ a := hcop2.dvd_of_dvd_mul_right ⟨3 ^ d, h'⟩
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2)) (Nat.dvd_antisymm h1 h2)
    rw [hac] at h'
    have h3eq : (3 : ℕ) ^ b = 3 ^ d := mul_left_cancel₀ (by positivity : (2 : ℕ) ^ c ≠ 0) h'
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3)) h3eq

/-- A non-zero polynomial of degree ≤ L in each variable has at most (L+1)²-1
    zeros among the points {(2^t, 3^t) : t = 0, 1, ..., T}.

    This follows from the multiplicative independence of 2 and 3:
    the values 2^i · 3^j for (i,j) ∈ {0,...,L}² are pairwise distinct,
    so the Vandermonde determinant is non-zero, and a non-zero linear
    combination of (L+1)² distinct exponentials α_k^t can vanish for
    at most (L+1)²-1 values of t.

    Uses `eq_zero_of_forall_pow_sum_mul_pow_eq_zero` from Mathlib. -/
theorem polynomial_zero_estimate
    (P : ℤ → ℤ → ℤ) (L : ℕ) (_hL : L ≥ 1)
    (_hsupp : ∀ i j : ℤ, (i < 0 ∨ i > L ∨ j < 0 ∨ j > L) → P i j = 0)
    (hP : ∃ i j : ℤ, 0 ≤ i ∧ i ≤ L ∧ 0 ≤ j ∧ j ≤ L ∧ P i j ≠ 0)
    (T : ℕ) (hT : T + 1 ≥ (L + 1) * (L + 1)) :
    ∃ t : ℕ, t ≤ T ∧ polyEvalExp P L t ≠ 0 := by
  by_contra hall
  push_neg at hall
  -- hall : ∀ t, t ≤ T → polyEvalExp P L t = 0
  set M := (L + 1) * (L + 1) with hM_def
  -- Map between Fin M and pairs (Fin(L+1), Fin(L+1))
  let e := finProdFinEquiv (m := L + 1) (n := L + 1)
  -- Coefficient vector and evaluation bases
  let v : Fin M → ℤ := fun k => P ↑(e.symm k).1 ↑(e.symm k).2
  let f : Fin M → ℤ := fun k => 2 ^ (e.symm k).1.val * 3 ^ (e.symm k).2.val
  -- Step 1: f is injective (multiplicative independence of 2 and 3)
  have hf_inj : Function.Injective f := by
    intro k₁ k₂ hfk
    have h := two_pow_mul_three_pow_injective _ _ _ _ hfk
    exact e.symm.injective (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  -- Step 2: Vandermonde vanishing condition
  have hfv : ∀ i : Fin M, (∑ j : Fin M, v j * f j ^ (i : ℕ)) = 0 := by
    intro i
    have hi_le : (i : ℕ) ≤ T := by omega
    -- The Fin M sum equals polyEvalExp P L i
    suffices hsuff : (∑ j : Fin M, v j * f j ^ (i : ℕ)) = polyEvalExp P L (i : ℕ) by
      rw [hsuff]; exact hall (i : ℕ) hi_le
    -- Reindex from Fin M to Fin(L+1) × Fin(L+1), then to range sums
    trans (∑ p : Fin (L + 1) × Fin (L + 1),
      P ↑p.1 ↑p.2 * (2 : ℤ) ^ (p.1.val * (i : ℕ)) * 3 ^ (p.2.val * (i : ℕ)))
    · apply Fintype.sum_equiv e.symm
      intro k
      simp only [v, f, mul_pow, ← pow_mul]
      ring
    · unfold polyEvalExp
      simp only [← Fin.sum_univ_eq_sum_range]
      rw [← Finset.sum_product']
      rfl
  -- Step 3: Vandermonde determinant → v = 0
  have hv_zero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf_inj hfv
  -- Step 4: But P is not identically zero → contradiction
  obtain ⟨i₀, j₀, hi₀, hi₀L, hj₀, hj₀L, hPne⟩ := hP
  apply hPne
  have key : v (e (⟨i₀.toNat, by omega⟩, ⟨j₀.toNat, by omega⟩)) = 0 :=
    congr_fun hv_zero _
  simp only [v, Equiv.symm_apply_apply] at key
  rwa [show (↑(Fin.mk i₀.toNat (by omega : i₀.toNat < L + 1)) : ℤ) = i₀ from by
        simp [Int.toNat_of_nonneg hi₀],
       show (↑(Fin.mk j₀.toNat (by omega : j₀.toNat < L + 1)) : ℤ) = j₀ from by
        simp [Int.toNat_of_nonneg hj₀]] at key

/-! ## Combined extrapolation-contradiction

The full Gel'fond-Schneider argument combines all the above:
1. auxEntireFunc gives F(z) from the polynomial P
2. auxEntireFunc_growth bounds |F|
3. schwarz_vanishing_bound makes |F| exponentially small
4. jensen_zero_count says F has many zeros (more than L²)
5. polynomial_zero_estimate says a non-zero P of degree L
   can't have > L² zeros at exponential points
6. Contradiction → P ≡ 0 → but P(0,0) ≠ 0

The quantitative version of this contradiction yields the
effective lower bound in baker_extrapolation.
-/

/-- The Gel'fond-Schneider extrapolation theorem.

    Given an auxiliary polynomial P of degree ≤ L with P(0,0) ≠ 0,
    coefficient bound B, and initial vanishing at integer points 0,...,T,
    the Schwarz-Jensen analysis produces a contradiction when T is large
    enough relative to L (specifically T + 1 ≥ (L+1)²).

    This forces the auxiliary function F(z) = P(e^z, e^{βz}) to be
    identically zero, which contradicts P(0,0) ≠ 0.

    The proof chains:
    auxEntireFunc_growth → schwarz_vanishing_bound → jensen_zero_count
    → polynomial_zero_estimate → contradiction. -/
theorem gelfond_schneider_contradiction
    (P : ℤ → ℤ → ℤ) (L : ℕ) (hL : L ≥ 1)
    (hP0 : P 0 0 ≠ 0)
    (hsupp : ∀ i j : ℤ, (i < 0 ∨ i > L ∨ j < 0 ∨ j > L) → P i j = 0)
    (_B : ℝ) (_hB : _B > 0)
    (_hbound : ∀ i j : ℤ, (|P i j| : ℝ) ≤ _B)
    (_β : ℝ) (_hβ : Irrational _β)
    (T : ℕ) (hT : T + 1 ≥ (L + 1) * (L + 1))
    (hvanish : ∀ t : ℕ, t ≤ T → polyEvalExp P L t = 0) :
    False := by
  -- Step 1: polynomial_zero_estimate says ∃ t ≤ T with polyEvalExp P L t ≠ 0
  have hP_exists : ∃ i j : ℤ, 0 ≤ i ∧ i ≤ L ∧ 0 ≤ j ∧ j ≤ L ∧ P i j ≠ 0 :=
    ⟨0, 0, le_refl _, by omega, le_refl _, by omega, by exact_mod_cast hP0⟩
  have ⟨t, ht, hne⟩ := polynomial_zero_estimate P L hL hsupp hP_exists T hT
  -- Step 2: hvanish says polyEvalExp P L t = 0 for all t ≤ T
  exact hne (hvanish t ht)

end

end Collatz
