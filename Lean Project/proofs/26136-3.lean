import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example (a b : Nat) : min a b ≤ b := by
by_cases h : a ≤ b
· rw [min_def]
  rw [if_pos h]
  exact h
· rw [min_def]
  rw [if_neg h]
  exact le_rfl

/- ACTUAL PROOF OF Nat.min_le_right -/

example (a b : Nat) : min a b ≤ b := by
  by_cases (a <= b) <;> simp [Nat.min_def, *]