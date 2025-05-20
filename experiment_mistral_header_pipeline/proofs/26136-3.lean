import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example (a b : Nat) : min a b ≤ b := by
  by_cases h : a ≤ b
  · apply Nat.le_trans (Nat.min_le_left _ _) h
  · exact Nat.min_eq_right h

/- ACTUAL PROOF OF Nat.min_le_right -/

example (a b : Nat) : min a b ≤ b := by
  by_cases (a <= b) <;> simp [Nat.min_def, *]