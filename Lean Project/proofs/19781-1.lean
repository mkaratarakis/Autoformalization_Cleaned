import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b ≠ .lt ↔ b ≤ a := by
  constructor
  · intro h
    contrapose! h
    exact compare_lt_iff_lt.2 h
  · intro h
    exact mt compare_lt_iff_lt.1 (not_lt_of_ge h)

/- ACTUAL PROOF OF Nat.compare_ne_lt -/

example {a b : Nat} : compare a b ≠ .lt ↔ b ≤ a := by
  rw [compare_def_le]; (repeat' split) <;> simp [Nat.le_of_not_le, *]