import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (n m : Nat) : n - m = max n m - m := by
  by_cases h: n ≤ m
  · simp [max]
    rw [Nat.sub_eq_zero_of_le h]
    rw [Nat.sub_self]
  · simp [max, -sub_eq_zero_of_le h]

/- ACTUAL PROOF OF Nat.sub_eq_max_sub -/

example (n m : Nat) : n - m = max n m - m := by
  cases Nat.le_total m n with
  | inl h => rw [Nat.max_eq_left h]
  | inr h => rw [Nat.max_eq_right h, Nat.sub_eq_zero_of_le h, Nat.sub_self]