import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example (a b : Nat) : min a b = min b a := by
  by_cases h : a ≤ b
  · rw [if_pos h]
    rw [if_neg (not_le_of_gt h)]
  · rw [if_neg h]
    rw [if_pos (le_of_not_ge h)]

/- ACTUAL PROOF OF Nat.min_comm -/

example (a b : Nat) : min a b = min b a := by
  match Nat.lt_trichotomy a b with
  | .inl h => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]
  | .inr (.inl h) => simp [Nat.min_def, h]
  | .inr (.inr h) => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]