import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (h : n ≠ 0) : n.log2 < k ↔ n < 2 ^ k := by
apply Iff.intro
. intro h1
  apply Nat.lt_of_le_of_lt
  apply Nat.log2_le_iff_pow_le_self
  . exact h
  . exact h1
. intro h1
  contrapose! h1
  apply Nat.log2_le_iff_pow_le_self
  . exact h
  . exact h1

/- ACTUAL PROOF OF Nat.log2_lt -/

example (h : n ≠ 0) : n.log2 < k ↔ n < 2 ^ k := by
  rw [← Nat.not_le, ← Nat.not_le, le_log2 h]