import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a b : Int) : min a b ≤ b := by
  by_cases h : a ≤ b
  · rw [min_eq_left h]
    exact h
  · rw [min_eq_right]
    exact le_rfl

/- ACTUAL PROOF OF Int.min_le_right -/

example (a b : Int) : min a b ≤ b := by
  rw [Int.min_def]; split <;> simp [*]