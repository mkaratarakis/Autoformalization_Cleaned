import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example (a b : Nat) : min a b ≤ b := by
  by_cases h : a ≤ b
  · exact le_of_eq (Nat.min_eq_left h)
  · exact Nat.le_rfl b

/- ACTUAL PROOF OF Nat.min_le_right -/

example (a b : Nat) : min a b ≤ b := by
  by_cases (a <= b) <;> simp [Nat.min_def, *]