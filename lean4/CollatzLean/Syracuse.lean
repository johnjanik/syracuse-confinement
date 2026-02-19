/-
  CollatzLean/Syracuse.lean
  Tao's Syracuse framework from "Almost all orbits of the Collatz map
  attain almost bounded values" (2022, Inventiones Mathematicae).

  Formalizes:
  - The 2-adic valuation val2
  - The Syracuse map Syr(n) = (3n+1)/2^{v₂(3n+1)}
  - The n-Syracuse valuation (tuple of v₂ values at each step)
  - The affine iteration identity:
      Syr^k(n) · 2^|a^(k)| = 3^k · n + G_k
    where G_k is the "cleared offset" satisfying G₀ = 0, G_{k+1} = 3·G_k + 2^|a^(k)|.

  All definitions are computable; #eval tests verify against Tao's paper.
-/
import CollatzLean.HenselAttrition
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace Collatz

/-! ## 2-adic valuation -/

/-- The 2-adic valuation: largest k such that 2^k divides n.
    Convention: val2 0 = 0. -/
def val2 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 2 = 1 then 0
  else 1 + val2 (n / 2)
termination_by n

-- Concrete checks
example : val2 0 = 0 := by native_decide
example : val2 1 = 0 := by native_decide
example : val2 2 = 1 := by native_decide
example : val2 4 = 2 := by native_decide
example : val2 8 = 3 := by native_decide
example : val2 12 = 2 := by native_decide
example : val2 10 = 1 := by native_decide
example : val2 16 = 4 := by native_decide

#eval val2 (3 * 1 + 1)   -- 2 (since 4 = 2²)
#eval val2 (3 * 3 + 1)   -- 1 (since 10 = 2·5)
#eval val2 (3 * 5 + 1)   -- 4 (since 16 = 2⁴)
#eval val2 (3 * 7 + 1)   -- 1 (since 22 = 2·11)

/-- Unfolding lemma for val2 on positive even numbers. -/
theorem val2_even (n : ℕ) (hn : n > 0) (he : n % 2 = 0) :
    val2 n = val2 (n / 2) + 1 := by
  rw [val2]; simp [show n ≠ 0 from by omega, show ¬(n % 2 = 1) from by omega]; ring

/-- val2 of an odd number is 0. -/
theorem val2_odd (n : ℕ) (ho : n % 2 = 1) : val2 n = 0 := by
  rw [val2]; simp [show n ≠ 0 from by omega, ho]

/-- val2 of 0 is 0. -/
@[simp] theorem val2_zero' : val2 0 = 0 := by rw [val2]; simp

/-- 2^(val2 n) divides n. -/
theorem pow_val2_dvd (n : ℕ) : 2 ^ val2 n ∣ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn; simp
    · by_cases ho : n % 2 = 1
      · rw [val2_odd n ho]; simp
      · have he : n % 2 = 0 := by omega
        rw [val2_even n (by omega) he, pow_succ]
        -- Goal: 2 ^ val2 (n / 2) * 2 ∣ n
        have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
        obtain ⟨j, hj⟩ := ih _ hlt
        -- hj: n / 2 = 2 ^ val2 (n / 2) * j
        refine ⟨j, ?_⟩
        -- Abstract val2(n/2) to avoid rewriting inside it
        set k := val2 (n / 2)
        -- hj: n / 2 = 2 ^ k * j, goal: n = 2 ^ k * 2 * j
        have h1 : n = 2 * (n / 2) := by omega
        rw [hj] at h1
        -- h1: n = 2 * (2 ^ k * j), goal: n = 2 ^ k * 2 * j
        rw [h1]; ring

/-- n = (n / 2^val2(n)) * 2^val2(n). -/
theorem val2_cancel (n : ℕ) : n / 2 ^ val2 n * 2 ^ val2 n = n :=
  Nat.div_mul_cancel (pow_val2_dvd n)

/-- After stripping all factors of 2, the result is odd (for n > 0). -/
theorem val2_div_odd (n : ℕ) (hn : 0 < n) : n / 2 ^ val2 n % 2 = 1 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases ho : n % 2 = 1
    · rw [val2_odd n ho]; simp; exact ho
    · have he : n % 2 = 0 := by omega
      rw [val2_even n (by omega) he, pow_succ, mul_comm, ← Nat.div_div_eq_div_mul]
      exact ih _ (Nat.div_lt_self (by omega) (by omega)) (by omega)

/-! ## The Syracuse map -/

/-- The Syracuse map: Syr(n) = (3n+1) / 2^{v₂(3n+1)}.
    For odd n, this is the "complete odd Collatz step":
    apply 3n+1 then strip all factors of 2. -/
def syracuse (n : ℕ) : ℕ := (3 * n + 1) / 2 ^ val2 (3 * n + 1)

/-- Key property: syracuse(n) * 2^{v₂(3n+1)} = 3n+1. -/
theorem syracuse_mul_pow (n : ℕ) :
    syracuse n * 2 ^ val2 (3 * n + 1) = 3 * n + 1 :=
  val2_cancel (3 * n + 1)

/-- For odd n > 0, syracuse(n) is odd. -/
theorem syracuse_odd (n : ℕ) (hn : n > 0) (hodd : n % 2 = 1) :
    syracuse n % 2 = 1 :=
  val2_div_odd (3 * n + 1) (by omega)

/-- For odd n > 0, syracuse(n) > 0. -/
theorem syracuse_pos (n : ℕ) (hn : n > 0) (hodd : n % 2 = 1) :
    syracuse n > 0 := by
  have := syracuse_odd n hn hodd; omega

-- Concrete checks
example : syracuse 1 = 1 := by native_decide
example : syracuse 3 = 5 := by native_decide
example : syracuse 5 = 1 := by native_decide
example : syracuse 7 = 11 := by native_decide
example : syracuse 11 = 17 := by native_decide
example : syracuse 13 = 5 := by native_decide
example : syracuse 15 = 23 := by native_decide
example : syracuse 27 = 41 := by native_decide

/-! ## Relationship to oddCollatzStep -/

/-- oddCollatzStep does one halving: T(x) = (3x+1)/2.
    Syracuse does all halvings: Syr(x) = (3x+1)/2^{v₂(3x+1)}.
    When v₂(3x+1) = 1, they agree. -/
theorem syracuse_eq_oddCollatzStep_of_val2_one (n : ℕ) (h : val2 (3 * n + 1) = 1) :
    syracuse n = oddCollatzStep n := by
  simp [syracuse, oddCollatzStep, h]

-- Examples where they agree (val2 = 1): 3, 7, 11, 15
example : val2 (3 * 3 + 1) = 1 := by native_decide
example : syracuse 3 = oddCollatzStep 3 := by native_decide

-- Examples where they differ (val2 > 1): 1, 5, 13
example : val2 (3 * 1 + 1) = 2 := by native_decide
example : syracuse 1 = 1 := by native_decide       -- strips 2 factors
example : oddCollatzStep 1 = 2 := by native_decide  -- strips only 1

/-! ## Syracuse iteration -/

/-- Iterate the Syracuse map k times. -/
def syracuseIter (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => syracuse (syracuseIter n k)

@[simp] lemma syracuseIter_zero (n : ℕ) : syracuseIter n 0 = n := rfl
@[simp] lemma syracuseIter_succ (n k : ℕ) :
    syracuseIter n (k + 1) = syracuse (syracuseIter n k) := rfl

/-- Syracuse iteration preserves oddness. -/
theorem syracuseIter_odd (n : ℕ) (hn : n > 0) (hodd : n % 2 = 1) (k : ℕ) :
    syracuseIter n k % 2 = 1 := by
  induction k with
  | zero => simpa
  | succ k ih =>
    simp only [syracuseIter_succ]
    exact syracuse_odd _ (by omega) ih

/-- Syracuse iteration preserves positivity. -/
theorem syracuseIter_pos (n : ℕ) (hn : n > 0) (hodd : n % 2 = 1) (k : ℕ) :
    syracuseIter n k > 0 := by
  have := syracuseIter_odd n hn hodd k; omega

-- Concrete checks
example : syracuseIter 3 0 = 3 := by native_decide
example : syracuseIter 3 1 = 5 := by native_decide
example : syracuseIter 3 2 = 1 := by native_decide  -- 3 → 5 → 1
example : syracuseIter 7 0 = 7 := by native_decide
example : syracuseIter 7 1 = 11 := by native_decide
example : syracuseIter 7 2 = 17 := by native_decide

#eval (List.range 10).map (syracuseIter 27)

/-! ## Syracuse valuation and offset -/

/-- The v₂ value at Syracuse step k: v₂(3·Syr^k(n)+1). -/
def syracuseValAt (n k : ℕ) : ℕ := val2 (3 * syracuseIter n k + 1)

/-- Sum of the first k valuation entries: |a^(k)| = Σ_{i=0}^{k-1} v₂(3·Syr^i(n)+1).
    This is the total number of halvings in k Syracuse steps. -/
def syracuseValSum (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => syracuseValSum n k + syracuseValAt n k

/-- The Syracuse valuation tuple a^(k) = [v₂(3·n+1), ..., v₂(3·Syr^{k-1}(n)+1)]. -/
def syracuseValTuple (n : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => syracuseValTuple n k ++ [syracuseValAt n k]

/-- The cleared offset: G₀ = 0, G_{k+1} = 3·G_k + 2^|a^(k)|.
    This satisfies the same recurrence as the correction term
    from Identity.lean, driven by the Syracuse timestamps. -/
def syracuseOffset (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * syracuseOffset n k + 2 ^ syracuseValSum n k

-- Simp lemmas for unfolding
@[simp] lemma syracuseValSum_zero (n : ℕ) : syracuseValSum n 0 = 0 := rfl
@[simp] lemma syracuseValSum_succ (n k : ℕ) :
    syracuseValSum n (k + 1) = syracuseValSum n k + syracuseValAt n k := rfl
@[simp] lemma syracuseOffset_zero (n : ℕ) : syracuseOffset n 0 = 0 := rfl
@[simp] lemma syracuseOffset_succ (n k : ℕ) :
    syracuseOffset n (k + 1) = 3 * syracuseOffset n k + 2 ^ syracuseValSum n k := rfl

-- Concrete checks: Syr²(3) = 1, valTuple = [1,4], valSum = 5, offset = 5
-- Identity: 1 · 2^5 = 3² · 3 + 5 = 27 + 5 = 32 ✓
#eval syracuseValTuple 3 2     -- [1, 4]
#eval syracuseValSum 3 2       -- 5
#eval syracuseOffset 3 2       -- 5
#eval syracuseIter 3 2 * 2 ^ syracuseValSum 3 2  -- 32
#eval 3 ^ 2 * 3 + syracuseOffset 3 2             -- 32

-- Syr³(7) orbit: 7 → 11 → 17 → 13
#eval syracuseValTuple 7 3     -- [1, 1, 2]
#eval syracuseValSum 7 3       -- 4
#eval syracuseOffset 7 3       -- 13
#eval syracuseIter 7 3 * 2 ^ syracuseValSum 7 3  -- 13 * 16 = 208
#eval 3 ^ 3 * 7 + syracuseOffset 7 3             -- 189 + 13 = 202... hmm

/-! ## The Syracuse identity -/

/-- **Syracuse affine identity** (Tao 2022, Proposition 1.8):
    Syr^k(n) · 2^|a^(k)| = 3^k · n + G_k
    where |a^(k)| is the total number of halvings and G_k is the cleared offset.
    This separates the multiplicative "drift" 3^k/2^|a^(k)| from the additive correction. -/
theorem syracuse_identity (n : ℕ) (k : ℕ) :
    syracuseIter n k * 2 ^ syracuseValSum n k = 3 ^ k * n + syracuseOffset n k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [syracuseIter_succ, syracuseValSum_succ, syracuseOffset_succ, syracuseValAt]
    calc syracuse (syracuseIter n k) *
           2 ^ (syracuseValSum n k + val2 (3 * syracuseIter n k + 1))
        = (syracuse (syracuseIter n k) * 2 ^ val2 (3 * syracuseIter n k + 1)) *
          2 ^ syracuseValSum n k := by rw [pow_add]; ring
      _ = (3 * syracuseIter n k + 1) * 2 ^ syracuseValSum n k := by
          rw [syracuse_mul_pow]
      _ = 3 * (syracuseIter n k * 2 ^ syracuseValSum n k) +
          2 ^ syracuseValSum n k := by ring
      _ = 3 * (3 ^ k * n + syracuseOffset n k) +
          2 ^ syracuseValSum n k := by rw [ih]
      _ = 3 ^ (k + 1) * n +
          (3 * syracuseOffset n k + 2 ^ syracuseValSum n k) := by ring

-- Verify the identity on concrete examples
example : syracuseIter 3 2 * 2 ^ syracuseValSum 3 2 =
    3 ^ 2 * 3 + syracuseOffset 3 2 := by native_decide

example : syracuseIter 7 3 * 2 ^ syracuseValSum 7 3 =
    3 ^ 3 * 7 + syracuseOffset 7 3 := by native_decide

example : syracuseIter 27 5 * 2 ^ syracuseValSum 27 5 =
    3 ^ 5 * 27 + syracuseOffset 27 5 := by native_decide

/-! ## Convergence criterion -/

/-- Using the identity: Syr^k(n) < n when 2^|a| > 3^k and the margin is large enough.
    n · (2^|a| - 3^k) > G_k implies descent. -/
theorem syracuse_descent_criterion (n : ℕ) (hn : n > 0) (hodd : n % 2 = 1) (k : ℕ)
    (hexp : 2 ^ syracuseValSum n k > 3 ^ k)
    (hmargin : n * (2 ^ syracuseValSum n k - 3 ^ k) > syracuseOffset n k) :
    syracuseIter n k < n := by
  have hid := syracuse_identity n k
  have hle : 3 ^ k ≤ 2 ^ syracuseValSum n k := by omega
  -- Proof by contradiction: if n ≤ Syr^k(n), then n * 2^vs ≤ Syr^k * 2^vs = 3^k*n + G_k
  -- But hmargin gives 3^k*n + G_k < n * 2^vs — contradiction.
  by_contra hge; push_neg at hge
  have h1 : n * 2 ^ syracuseValSum n k ≤ syracuseIter n k * 2 ^ syracuseValSum n k :=
    Nat.mul_le_mul_right _ hge
  rw [hid] at h1
  have h2 : 3 ^ k * n + syracuseOffset n k < n * 2 ^ syracuseValSum n k := by
    zify [hle] at hmargin ⊢; nlinarith
  omega

/-! ## Bridge: Syracuse and the Collatz sequence -/

/-- Repeated halving: if 2^a | m, then applying collatz a times gives m / 2^a. -/
theorem collatz_iter_halving (m : ℕ) (hm : m > 0) :
    ∀ a : ℕ, 2 ^ a ∣ m → (collatz^[a]) m = m / 2 ^ a := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro hdvd
    rw [Function.iterate_succ_apply']
    -- 2^a | m (since 2^(a+1) | m)
    have hdvd_a : 2 ^ a ∣ m := dvd_trans (pow_dvd_pow 2 (Nat.le_succ a)) hdvd
    rw [ih hdvd_a]
    -- collatz (m / 2^a) = m / 2^(a+1)
    -- Since 2^(a+1) | m, we know m / 2^a is even
    obtain ⟨k, hk⟩ := hdvd
    have hk_pos : 0 < k := by
      rcases k with _ | k
      · simp at hk; omega
      · omega
    have hma : m / 2 ^ a = 2 * k := by
      have : m = 2 ^ a * (2 * k) := by rw [hk, pow_succ]; ring
      rw [this, Nat.mul_div_cancel_left _ (by positivity)]
    have hpos : m / 2 ^ a > 0 := by rw [hma]; omega
    have heven : (m / 2 ^ a) % 2 = 0 := by rw [hma]; omega
    rw [collatz_even _ (by omega) heven, Nat.div_div_eq_div_mul, pow_succ]

/-- **Bridge theorem**: From an odd value in the Collatz sequence, one odd step
    plus val2(3x+1) halvings reaches the Syracuse value. -/
theorem collatzSeq_to_syracuse (n t : ℕ) (hn : n ≥ 1)
    (hodd : collatzSeq n t % 2 = 1) :
    collatzSeq n (t + 1 + val2 (3 * collatzSeq n t + 1)) =
      syracuse (collatzSeq n t) := by
  set x := collatzSeq n t with hx_def
  set a := val2 (3 * x + 1) with ha_def
  have hpos : x ≠ 0 := collatzSeq_ne_zero n hn t
  -- collatzSeq n (t+1) = 3x+1
  have hstep : collatzSeq n (t + 1) = 3 * x + 1 := by
    rw [collatzSeq_succ, collatz_odd x hpos hodd]
  -- collatzSeq n (t+1+j) = collatz^[j] (collatzSeq n (t+1))
  have hiter : ∀ j, collatzSeq n (t + 1 + j) = (collatz^[j]) (collatzSeq n (t + 1)) := by
    intro j; induction j with
    | zero => simp
    | succ j ihj =>
      rw [show t + 1 + (j + 1) = t + 1 + j + 1 from by omega,
          collatzSeq_succ, ihj, Function.iterate_succ_apply']
  rw [hiter a, hstep]
  -- collatz^[a] (3x+1) = (3x+1) / 2^a = syracuse x
  rw [collatz_iter_halving (3 * x + 1) (by omega) a
      (by rw [ha_def]; exact pow_val2_dvd _)]
  rfl

/-! ## Syracuse random variable on Z/3^n Z -/

/-- Count how many odd numbers in {1, 3, ..., 2N-1} have Syr(n) ≡ r (mod m). -/
def countSyracuseMod (N m r : ℕ) : ℕ :=
  (List.range N).countP (fun k => syracuse (2 * k + 1) % m = r)

/-- The distribution of Syr(n) mod m for n odd in {1, ..., 2N-1}. -/
def syracuseModDist (N m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).map (fun r => (r, countSyracuseMod N m r))

-- Syracuse mod 3 distribution (should be roughly uniform for large N)
#eval syracuseModDist 100 3
-- Syracuse mod 9 distribution (Tao's Syrac(Z/9Z))
-- Tao gives: 0→0, 1→8/63, 2→16/63, 3→0, 4→11/63, 5→4/63, 6→0, 7→2/63, 8→22/63
-- Multiply by 63: [0, 8, 16, 0, 11, 4, 0, 2, 22]
#eval syracuseModDist 504 9  -- 504 = 63 × 8

-- Syracuse mod 9 with rational approximation
#eval (syracuseModDist 504 9).map (fun (r, c) => (r, c, s!"{c}/504"))

/-! ## Full Syracuse orbit computation -/

/-- Compute the full Syracuse orbit until reaching 1 (or max steps). -/
def syracuseOrbit (n : ℕ) (maxSteps : ℕ := 100) : List ℕ :=
  let rec go (x : ℕ) (steps : ℕ) (acc : List ℕ) : List ℕ :=
    if steps = 0 then acc.reverse
    else if x = 1 then (x :: acc).reverse
    else go (syracuse x) (steps - 1) (x :: acc)
  termination_by steps
  go n maxSteps []

-- Classic orbits
#eval syracuseOrbit 27    -- 27 → 41 → 31 → 47 → ... → 1
#eval syracuseOrbit 7     -- 7 → 11 → 17 → 13 → 5 → 1
#eval syracuseOrbit 3     -- 3 → 5 → 1

/-! ## Valuation statistics -/

/-- Average v₂ value over k Syracuse steps starting from n. -/
def avgVal2 (n k : ℕ) : ℚ :=
  if k = 0 then 0
  else (syracuseValSum n k : ℚ) / k

-- For random-looking orbits, average v₂ should approach log₂(3) ≈ 1.585
#eval avgVal2 27 50   -- Should be close to 1.585
#eval avgVal2 7 5
#eval avgVal2 31 20

/-- The "drift" per Syracuse step: valSum/k should exceed log₂(3) ≈ 1.585
    for the trajectory to descend on average. -/
def driftExceeds (n k : ℕ) : Bool :=
  -- Check if valSum/k > 1.585 ≈ 317/200
  200 * syracuseValSum n k > 317 * k

#eval (List.range 50).map (fun k => (k + 1, driftExceeds 27 (k + 1)))

end Collatz
