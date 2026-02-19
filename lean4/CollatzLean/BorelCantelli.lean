/-
  CollatzLean/BorelCantelli.lean
  Borel-Cantelli consequence of Hensel attrition:
  the set of odd numbers capable of sustaining arbitrarily long v₂=1 runs
  has natural density zero.

  Key insight: the survivor sets E_d = {x odd : 2^(d+1) | (x+1)} are nested
  (E_{d+1} ⊆ E_d), so the union for d ≥ D collapses to E_D.
  Since |E_D ∩ [0,M)| = M / 2^(D+1), the density among odd numbers is ≤ 2^{-D} → 0.
-/
import CollatzLean.HenselAttrition
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace Collatz

/-! ## Survivor sets and automatic oddness -/

/-- Count of odd x < M with 2^(d+1) | (x+1): the "level-d survivors". -/
def OddSurvivorCount (M d : ℕ) : ℕ :=
  ((Finset.range M).filter (fun x => x % 2 = 1 ∧ (x + 1) % 2 ^ (d + 1) = 0)).card

/-- The survivor set (without redundant oddness filter). -/
def SurvivorSet (M d : ℕ) : Finset ℕ :=
  (Finset.range M).filter (fun x => (x + 1) % 2 ^ (d + 1) = 0)

/-- Any number with 2^(d+1) | (x+1) is automatically odd. -/
theorem survivor_auto_odd (x d : ℕ) (h : (x + 1) % 2 ^ (d + 1) = 0) : x % 2 = 1 := by
  have : 2 ∣ x + 1 :=
    dvd_trans (dvd_pow_self 2 (by omega : d + 1 ≠ 0)) ((survivor_iff_dvd x d).mp h)
  omega

/-- The oddness filter is redundant: OddSurvivorCount = SurvivorSet.card. -/
theorem oddSurvivorCount_eq_survivorSet_card (M d : ℕ) :
    OddSurvivorCount M d = (SurvivorSet M d).card := by
  simp only [OddSurvivorCount, SurvivorSet]; congr 1; ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, survivor_auto_odd x d h3, h3⟩⟩

/-! ## Exact counting of survivors -/

/-- The survivor set is the image of {0,...,M/p-1} under k ↦ (k+1)·p - 1. -/
theorem survivorSet_eq_image (M d : ℕ) :
    SurvivorSet M d =
      (Finset.range (M / 2 ^ (d + 1))).image (fun k => (k + 1) * 2 ^ (d + 1) - 1) := by
  have hp : 0 < 2 ^ (d + 1) := by positivity
  ext x
  simp only [SurvivorSet, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · intro ⟨hxM, hmod⟩
    obtain ⟨k, hk⟩ := (survivor_iff_dvd x d).mp hmod
    have hk_pos : 1 ≤ k := by
      rcases k with _ | k'
      · simp at hk
      · omega
    have hk_le : k ≤ M / 2 ^ (d + 1) := by
      have hkp : k * 2 ^ (d + 1) ≤ M := by linarith [mul_comm k (2 ^ (d + 1))]
      calc k = k * 2 ^ (d + 1) / 2 ^ (d + 1) := (Nat.mul_div_cancel k hp).symm
        _ ≤ M / 2 ^ (d + 1) := Nat.div_le_div_right hkp
    refine ⟨k - 1, by omega, ?_⟩
    · have hk1 : k - 1 + 1 = k := by omega
      rw [hk1, show k * 2 ^ (d + 1) = 2 ^ (d + 1) * k from mul_comm _ _]; omega
  · intro ⟨j, hj, hx⟩
    have h1 : (j + 1) * 2 ^ (d + 1) ≤ M / 2 ^ (d + 1) * 2 ^ (d + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : M / 2 ^ (d + 1) * 2 ^ (d + 1) ≤ M := Nat.div_mul_le_self M _
    have h3 : 0 < (j + 1) * 2 ^ (d + 1) := Nat.mul_pos (Nat.succ_pos j) hp
    constructor
    · omega
    · have heq : (j + 1) * 2 ^ (d + 1) - 1 + 1 = (j + 1) * 2 ^ (d + 1) := by omega
      subst hx
      rw [heq, show (j + 1) * 2 ^ (d + 1) = 2 ^ (d + 1) * (j + 1) from mul_comm _ _]
      exact Nat.mul_mod_right _ (j + 1)

/-- Exact count of survivors in {0,...,M-1}. -/
theorem survivor_count (M d : ℕ) :
    (SurvivorSet M d).card = M / 2 ^ (d + 1) := by
  set p := 2 ^ (d + 1) with hp_def
  have hp_pos : 0 < p := by positivity
  rw [survivorSet_eq_image]
  rw [Finset.card_image_of_injective _
    (fun a b (h : (a + 1) * p - 1 = (b + 1) * p - 1) => by
      -- Introduce fresh names so omega can handle the Nat subtraction
      set X := (a + 1) * p with hX_def
      set Y := (b + 1) * p with hY_def
      have hX : 0 < X := Nat.mul_pos (Nat.succ_pos a) hp_pos
      have hY : 0 < Y := Nat.mul_pos (Nat.succ_pos b) hp_pos
      have hXY : X = Y := by omega
      rw [hX_def, hY_def] at hXY
      have := mul_right_cancel₀ (show p ≠ 0 from by omega) hXY
      omega)]
  exact Finset.card_range _

/-- OddSurvivorCount equals M / 2^(d+1). -/
theorem oddSurvivorCount_eq (M d : ℕ) :
    OddSurvivorCount M d = M / 2 ^ (d + 1) := by
  rw [oddSurvivorCount_eq_survivorSet_card, survivor_count]

/-- Upper bound (requested form): OddSurvivorCount M d ≤ M / 2^(d+1) + 1. -/
theorem oddSurvivorCount_le (M d : ℕ) :
    OddSurvivorCount M d ≤ M / 2 ^ (d + 1) + 1 := by
  rw [oddSurvivorCount_eq]; omega

/-! ## Nesting of survivor sets -/

/-- Survivor sets are antitone in d: higher d → stricter condition → smaller set. -/
theorem survivorSet_antitone (M : ℕ) {d d' : ℕ} (hdd : d ≤ d') :
    SurvivorSet M d' ⊆ SurvivorSet M d := by
  intro x hx
  simp only [SurvivorSet, Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, (survivor_iff_dvd x d).mpr
    (dvd_trans (Nat.pow_dvd_pow 2 (by omega : d + 1 ≤ d' + 1))
      ((survivor_iff_dvd x d').mp hx.2))⟩

/-- The existential collapses: ∃ d ≥ D, 2^(d+1) | (x+1) ↔ 2^(D+1) | (x+1).
    This is because the survivor sets are nested. -/
theorem exists_survivor_iff_base (x D : ℕ) :
    (∃ d, D ≤ d ∧ 2 ^ (d + 1) ∣ x + 1) ↔ 2 ^ (D + 1) ∣ x + 1 := by
  constructor
  · intro ⟨d, hDd, hdvd⟩
    exact dvd_trans (Nat.pow_dvd_pow 2 (by omega : D + 1 ≤ d + 1)) hdvd
  · exact fun h => ⟨D, le_refl D, h⟩

/-! ## Integer density bound -/

/-- The survivor count times 2^(D+1) is at most M. -/
theorem survivor_count_mul_le (M D : ℕ) :
    (SurvivorSet M D).card * 2 ^ (D + 1) ≤ M := by
  rw [survivor_count]; exact Nat.div_mul_le_self M _

/-! ## Real-valued density estimates -/

/-- The survivor density among odd numbers is at most 1/2^D. -/
theorem survivor_density_le (M D : ℕ) (hM : 0 < M) :
    ((SurvivorSet M D).card : ℝ) / (↑M / 2) ≤ 1 / 2 ^ D := by
  rw [survivor_count]
  have hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr hM
  -- Clear denominators: suffices to show card * 2^D * 2 ≤ M (as ℝ)
  rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < ↑M / 2) (by positivity : (0 : ℝ) < 2 ^ D)]
  rw [one_mul, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  -- Goal: ↑(M / 2^(D+1)) * 2^D * 2 ≤ ↑M
  have key : ((M / 2 ^ (D + 1)) * 2 ^ (D + 1) : ℕ) ≤ M := Nat.div_mul_le_self M _
  have hkey : (↑((M / 2 ^ (D + 1)) * 2 ^ (D + 1)) : ℝ) ≤ ↑M := Nat.cast_le.mpr key
  have hmul : (↑((M / 2 ^ (D + 1)) * 2 ^ (D + 1)) : ℝ) =
      ↑(M / 2 ^ (D + 1)) * ↑(2 ^ (D + 1) : ℕ) := by push_cast; ring
  have hpow : (↑(2 ^ (D + 1) : ℕ) : ℝ) = 2 ^ D * 2 := by push_cast; ring
  nlinarith

/-! ## Borel-Cantelli: density converges to zero -/

/-- For any D, the survivor density is at most 1/2^D among odd numbers.
    By `exists_survivor_iff_base`, SurvivorSet M D captures exactly the set
    {x < M : x odd ∧ ∃ d ≥ D, 2^(d+1) | (x+1)}. -/
theorem borel_cantelli_finite (M D : ℕ) (hM : 0 < M) :
    ((SurvivorSet M D).card : ℝ) / (↑M / 2) ≤ 1 / 2 ^ D :=
  survivor_density_le M D hM

/-- **Borel-Cantelli danger density**: the density of odd numbers that can
    sustain v₂=1 runs of length ≥ D converges to zero as D → ∞.

    Concretely: ∀ ε > 0, ∃ D₀ M₀, ∀ D ≥ D₀, ∀ M ≥ M₀,
      card(SurvivorSet M D) / (M/2) < ε.

    By `exists_survivor_iff_base` and `survivor_auto_odd`, SurvivorSet M D equals
    {x < M : x odd ∧ ∃ d ≥ D, 2^(d+1) | (x+1)}. -/
theorem borel_cantelli_danger_density (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ M₀ : ℕ, ∀ D, D₀ ≤ D → ∀ M, M₀ ≤ M →
      ((SurvivorSet M D).card : ℝ) / (↑M / 2) < ε := by
  -- Find D₀ such that 1/2^D₀ < ε (Archimedean property)
  obtain ⟨D₀, hD₀⟩ : ∃ D₀ : ℕ, 1 / (2 : ℝ) ^ D₀ < ε := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 : ℝ) / 2 < 1)
    exact ⟨n, by rwa [div_pow, one_pow] at hn⟩
  -- M₀ = 1 suffices (we just need M > 0)
  exact ⟨D₀, 1, fun D hD M hM => by
    have hM_pos : 0 < M := by omega
    -- 2^D₀ ≤ 2^D (via ℕ cast)
    have h2D_le : (2 : ℝ) ^ D₀ ≤ 2 ^ D := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hD
    calc ((SurvivorSet M D).card : ℝ) / (↑M / 2)
        ≤ 1 / 2 ^ D := borel_cantelli_finite M D hM_pos
      _ ≤ 1 / 2 ^ D₀ := by
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ D)
            (by positivity : (0 : ℝ) < 2 ^ D₀)]
          linarith
      _ < ε := hD₀⟩

/-! ## Concrete verification -/

example : OddSurvivorCount 16 0 = 8 := by native_decide
example : OddSurvivorCount 16 1 = 4 := by native_decide
example : OddSurvivorCount 16 2 = 2 := by native_decide
example : OddSurvivorCount 16 3 = 1 := by native_decide
example : OddSurvivorCount 16 4 = 0 := by native_decide

example : SurvivorSet 100 3 ⊆ SurvivorSet 100 2 := survivorSet_antitone 100 (by omega)

end Collatz
