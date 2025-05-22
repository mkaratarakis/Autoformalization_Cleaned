import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b = .lt ↔ a < b := by
  constructor
  · intro h
    unfold compare at h
    cases h
    case inl h => exact h
    case inr h => contradiction
  · intro h
    unfold compare
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt h)
    case inl h => exact Or.inl h
    case inr h => contradiction

/- ACTUAL PROOF OF Nat.compare_eq_lt -/

example {a b : Nat} : compare a b = .lt ↔ a < b := by
  rw [compare_def_lt]; (repeat' split) <;> simp [*]