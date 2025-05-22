import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example ( a b : Nat) : a ≤ max a b := by
  by_cases h : a ≤ b
  . calc
  a ≤ b := h
  _ ≤ max a b := by simp [max]

. calc
  a ≤ a := le_rfl
  _ = max a b := by simp [max, h]

/- ACTUAL PROOF OF Nat.le_max_left -/

example ( a b : Nat) : a ≤ max a b := by
  by_cases (a <= b) <;> simp [Nat.max_def, *]