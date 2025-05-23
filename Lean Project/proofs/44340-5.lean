import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a b : Int) : a ≤ max a b := by
  by_cases
  -- Case 1: a ≤ b
  . case inl h =>
    rw [max_eq_right h]
    exact h
  -- Case 2: ¬ a ≤ b
  . case inr h =>
    rw [max_eq_left (not_le.mp h)]
    exact le_rfl

/- ACTUAL PROOF OF Int.le_max_left -/

example (a b : Int) : a ≤ max a b := by
  rw [Int.max_def]; split <;> simp [*]