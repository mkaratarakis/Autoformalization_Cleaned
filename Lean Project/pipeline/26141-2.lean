import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example ( a b : Nat) : a ≤ max a b := by
  by_cases h : a ≤ b
  · simp [Nat.max_def, h]
  · have h' : ¬ b ≤ a := fun h'' => h (le_of_not_le h'')
    simp [Nat.max_def, h']

/- ACTUAL PROOF OF Nat.le_max_left -/

example ( a b : Nat) : a ≤ max a b := by
  by_cases (a <= b) <;> simp [Nat.max_def, *]