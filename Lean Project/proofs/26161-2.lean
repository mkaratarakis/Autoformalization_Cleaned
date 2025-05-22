import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example (a b : Nat) : min a b = min b a := by
  by_cases h : a ≤ b
  · apply Nat.min_eq_left
    exact h
  · apply Nat.min_eq_right
    exact h

/- ACTUAL PROOF OF Nat.min_comm -/

example (a b : Nat) : min a b = min b a := by
  match Nat.lt_trichotomy a b with
  | .inl h => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]
  | .inr (.inl h) => simp [Nat.min_def, h]
  | .inr (.inr h) => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]