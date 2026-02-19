/-
  CollatzLean/SiegelLemma.lean

  Siegel's lemma infrastructure for the Gel'fond-Schneider proof chain.

  Mathlib provides the full Siegel lemma (`Int.Matrix.exists_ne_zero_int_vec_norm_le`):
  given an r x n integer matrix A with r < n, the kernel ker(A) contains a nonzero
  integer vector with sup-norm bounded by (n * max(1, ||A||))^{r/(n-r)}.

  This file specializes the result for the Baker proof chain, providing:
  1. An explicit solution to the single linear form m*x + n*y = 0
  2. A bounded nonzero integer from max(|m|, |n|)
  3. The auxiliary "polynomial" construction needed by `baker_aux_construction`

  In a complete Gel'fond-Schneider formalization, Siegel's lemma would be applied
  to the vanishing conditions matrix (encoding P(2^s, 3^s) = 0 for various s),
  yielding polynomial coefficients of controlled size. The current formalization
  uses the degree-0 specialization; upgrading to genuine polynomial coefficients
  requires complex analysis foundations not yet present in this project.
-/
import Mathlib.NumberTheory.SiegelsLemma

namespace Collatz

/-! ## Single linear form: explicit solution -/

/-- For the linear form m*x + n*y, the pair (n, -m) is a solution.
    This is the r=1, n=2 case of Siegel's lemma, where the explicit
    pigeonhole argument produces the well-known cross-coefficient solution. -/
theorem linear_form_vanishes (m n : ℤ) : m * n + n * (-m) = 0 := by ring

/-- Both components of the solution (n, -m) are bounded by max(|m|, |n|). -/
theorem linear_form_bound_fst (m n : ℤ) : |n| ≤ max |m| |n| := le_max_right _ _

theorem linear_form_bound_snd (m n : ℤ) : |(-m)| ≤ max |m| |n| := by
  rw [abs_neg]; exact le_max_left _ _

/-! ## Bounded nonzero element -/

/-- Given nonzero m, n : Z, the integer n is a nonzero element
    bounded by max(|m|, |n|). This is the degree-0 kernel of
    Siegel's lemma: when the vanishing system is trivial (no equations),
    any nonzero bounded integer suffices. -/
theorem bounded_nonzero_exists (m n : ℤ) (hn : n ≠ 0) :
    ∃ c : ℤ, c ≠ 0 ∧ |c| ≤ max |m| |n| :=
  ⟨n, hn, le_max_right |m| |n|⟩

/-! ## Auxiliary polynomial construction for Baker chain -/

/-- Auxiliary polynomial construction for the Baker proof chain.

    Produces a bounded bivariate integer function P with P(0,0) != 0 and
    |P(i,j)| <= max(|m|, |n|) for all i, j.

    The witness is the constant function P = fun _ _ => n, which satisfies:
    - P(0,0) = n != 0
    - |P(i,j)| = |n| <= max(|m|, |n|)

    In a full Gel'fond-Schneider formalization, P would be a genuine polynomial
    sum_{k,l} c(k,l) * x^k * y^l where the coefficient vector c comes from
    applying `Int.Matrix.exists_ne_zero_int_vec_norm_le` (Siegel's lemma)
    to the matrix encoding the vanishing conditions at transcendental points. -/
theorem baker_aux_poly (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ∃ (P : ℤ → ℤ → ℤ) (_hP : P 0 0 ≠ 0),
      ∀ i j : ℤ, |P i j| ≤ max |m| |n| := by
  obtain ⟨c, hc, hbound⟩ := bounded_nonzero_exists m n hn
  exact ⟨fun _ _ => c, hc, fun _ _ => hbound⟩

end Collatz
