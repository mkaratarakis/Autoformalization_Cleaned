import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b = .lt ↔ a < b := by
  constructor
  · intro h
    exact iff_of_eq (Nat.compare_eq_lt_iff_lt.2 h)
  · intro h
    exact iff_of_eq (Nat.compare_eq_lt_iff_lt.1 h)

/- ACTUAL PROOF OF Nat.compare_eq_lt -/

example {a b : Nat} : compare a b = .lt ↔ a < b := by
  rw [compare_def_lt]; (repeat' split) <;> simp [*]