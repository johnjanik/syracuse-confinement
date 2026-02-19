import Mathlib.Data.Int.Basic

variable (z : ℤ) (n : ℕ)

-- Test application of Int.toNat_le (which states: m.toNat ≤ n ↔ m ≤ ↑n)
example (h : z ≤ ↑n) : z.toNat ≤ n := Int.toNat_le.mpr h

-- Alternative using Int.le_toNat (requires 0 ≤ z)
-- Int.le_toNat states: 0 ≤ z → (n ≤ z.toNat ↔ ↑n ≤ z)
example (h1 : 0 ≤ z) (h2 : z ≤ ↑n) : z.toNat ≤ n := by
  -- Can't use le_toNat for this direction, but can use toNat_le
  exact Int.toNat_le.mpr h2
