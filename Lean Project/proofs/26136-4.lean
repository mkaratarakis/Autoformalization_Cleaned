import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example (a b : Nat) : min a b ≤ b := by
by_cases h : a ≤ b
· exact h
· apply min_le_right

/- ACTUAL PROOF OF Nat.min_le_right -/

example (a b : Nat) : min a b ≤ b := by
  by_cases (a <= b) <;> simp [Nat.min_def, *]