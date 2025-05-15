import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example ( a b : Nat) : a ≤ max a b := by
  by_cases h : a ≤ b
  · exact le_max_of_le_left h
  · exact le_max_of_le_right h

/- ACTUAL PROOF OF Nat.le_max_left -/

example ( a b : Nat) : a ≤ max a b := by
  by_cases (a <= b) <;> simp [Nat.max_def, *]