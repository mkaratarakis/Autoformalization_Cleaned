import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b = .lt ↔ a < b := by
  constructor
  · intro h
    exact Nat.lt_of_compare_lt h
  · intro h
    exact Nat.compare_lt_of_lt h

/- ACTUAL PROOF OF Nat.compare_eq_lt -/

example {a b : Nat} : compare a b = .lt ↔ a < b := by
  rw [compare_def_lt]; (repeat' split) <;> simp [*]