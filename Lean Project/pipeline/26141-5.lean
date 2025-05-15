import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example ( a b : Nat) : a ≤ max a b := by
  by_cases h : a ≤ b
  · apply Nat.le_max_left
  · rw [Nat.max_eq_left_of_not_le (not_le.mp h)]
    apply Nat.le_refl

/- ACTUAL PROOF OF Nat.le_max_left -/

example ( a b : Nat) : a ≤ max a b := by
  by_cases (a <= b) <;> simp [Nat.max_def, *]