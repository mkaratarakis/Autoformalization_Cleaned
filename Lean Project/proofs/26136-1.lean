import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example (a b : Nat) : min a b ≤ b := by
cases h : a ≤ b with
| inl h =>
  have h1 := min_eq_left h
  rw [h1]
  exact h
| inr h =>
  have h1 := min_eq_right h
  rw [h1]
  exact le_rfl

/- ACTUAL PROOF OF Nat.min_le_right -/

example (a b : Nat) : min a b ≤ b := by
  by_cases (a <= b) <;> simp [Nat.min_def, *]