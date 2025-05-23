import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a b : Int) : min a b ≤ b := by
  by_cases h : a ≤ b
  · apply min_le_right
  · apply min_le_right

/- ACTUAL PROOF OF Int.min_le_right -/

example (a b : Int) : min a b ≤ b := by
  rw [Int.min_def]; split <;> simp [*]