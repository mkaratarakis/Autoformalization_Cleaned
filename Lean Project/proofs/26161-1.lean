import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example (a b : Nat) : min a b = min b a := by
  cases h₁ : le a b with
  | inl h =>
    cases h₂ : le b a with
    | inl h' =>
      rw [min_eq_left h]
      rw [min_eq_left h']
    | inr h' =>
      rw [min_eq_left h]
      rw [min_eq_right h']
  | inr h =>
    cases h₂ : le b a with
    | inl h' =>
      rw [min_eq_right h]
      rw [min_eq_left h']
    | inr h' =>
      rw [min_eq_right h]
      rw [min_eq_right h']

/- ACTUAL PROOF OF Nat.min_comm -/

example (a b : Nat) : min a b = min b a := by
  match Nat.lt_trichotomy a b with
  | .inl h => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]
  | .inr (.inl h) => simp [Nat.min_def, h]
  | .inr (.inr h) => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]