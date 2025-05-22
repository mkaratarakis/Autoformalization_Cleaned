import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example ( a b : Nat) : a ≤ max a b := by
  by_cases h : a ≤ b
  . calc
  a ≤ b := h
  _ ≤ max a b := le_max_right a b

. calc
  a ≤ a := le_refl a
  _ = max a b := (eq_max_of_not_le h).symm

/- ACTUAL PROOF OF Nat.le_max_left -/

example ( a b : Nat) : a ≤ max a b := by
  by_cases (a <= b) <;> simp [Nat.max_def, *]