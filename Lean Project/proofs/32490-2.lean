import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (h : n ≠ 0) : n.log2 < k ↔ n < 2 ^ k := by
apply Iff.intro
. intro h1
  rw [← Nat.not_lt] at h1
  rw [← Nat.log2_le_iff_pow_le_self h] at h1
  rw [← Nat.not_lt]
  exact h1
. intro h1
  rw [← Nat.not_lt] at h1
  rw [← Nat.pow_lt_iff_lt_pow h] at h1
  rw [← Nat.log2_le_iff_pow_le_self h]
  rw [← Nat.not_lt]
  exact h1

/- ACTUAL PROOF OF Nat.log2_lt -/

example (h : n ≠ 0) : n.log2 < k ↔ n < 2 ^ k := by
  rw [← Nat.not_le, ← Nat.not_le, le_log2 h]