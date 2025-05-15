import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example ( a b : Nat) : a ≤ max a b := by
  by_cases h : a ≤ b
  · exact h
  · rw [max_eq_left (not_le.mp h)]
    exact le_refl a

/- ACTUAL PROOF OF Nat.le_max_left -/

example ( a b : Nat) : a ≤ max a b := by
  by_cases (a <= b) <;> simp [Nat.max_def, *]