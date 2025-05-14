import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example ( a b : Nat) : a ≤ max a b := by

  by_cases h : a ≤ b

  · have : max a b = b := by simp [max_def, h]
    rw [this]
    exact h

  · have : max a b = a := by simp [max_def, h]
    rw [this]
    exact le_rfl

/- ACTUAL PROOF OF Nat.le_max_left -/

example ( a b : Nat) : a ≤ max a b := by
  by_cases (a <= b) <;> simp [Nat.max_def, *]