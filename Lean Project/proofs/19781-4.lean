import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b ≠ .lt ↔ b ≤ a := by
  constructor
  · intro h
    by_cases h' : a < b
    · apply False.elim
      apply h
      exact compare_lt_of_lt h'
    · exact Nat.le_of_not_lt h'
  · intro h
    exact fun.

/- ACTUAL PROOF OF Nat.compare_ne_lt -/

example {a b : Nat} : compare a b ≠ .lt ↔ b ≤ a := by
  rw [compare_def_le]; (repeat' split) <;> simp [Nat.le_of_not_le, *]