import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (h₁ : m + k ≤ n) (h₂ : 0 < k) : n - (m + k) < n - m := by
  rw [sub_sub, sub_self]
  apply Nat.sub_lt_self_iff
  linarith

/- ACTUAL PROOF OF Nat.sub_add_lt_sub -/

example (h₁ : m + k ≤ n) (h₂ : 0 < k) : n - (m + k) < n - m := by
  rw [← Nat.sub_sub]; exact Nat.sub_lt_of_pos_le h₂ (Nat.le_sub_of_add_le' h₁)