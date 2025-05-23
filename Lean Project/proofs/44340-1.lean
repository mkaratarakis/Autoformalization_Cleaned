import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a b : Int) : a ≤ max a b := by
  by_cases
  -- Case 1: a ≤ b
  . case inl h =>
    -- In this case, max a b = b
    have h₁ : max a b = b := by simp [max]
    rw [h₁]
    exact h
  -- Case 2: ¬ a ≤ b
  . case inr h =>
    -- In this case, max a b = a
    have h₁ : max a b = a := by simp [max, h]
    rw [h₁]
    exact le_refl a

/- ACTUAL PROOF OF Int.le_max_left -/

example (a b : Int) : a ≤ max a b := by
  rw [Int.max_def]; split <;> simp [*]