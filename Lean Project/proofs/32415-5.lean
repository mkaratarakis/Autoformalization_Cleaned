import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {m n : Nat} : min n (min m n) = min n m := by
  by_cases h : n ≤ m
  · rw [min_eq_left h, min_eq_left h]
  · rw [min_eq_right (not_le.mp h), min_eq_right (not_le.mp h)]

/- ACTUAL PROOF OF Nat.min_self_assoc' -/

example {m n : Nat} : min n (min m n) = min n m := by
  rw [Nat.min_comm m n, ← Nat.min_assoc, Nat.min_self]