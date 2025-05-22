import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b = .gt ↔ b < a := by
  constructor
  · intro h
    cases h' : compare a b with
    | eq => contradiction
    | lt => contradiction
    | gt => exact Nat.lt_of_sub_eq_zero h'
  · intro h
    rw [compare_eq_gt_iff_lt]
    exact h

/- ACTUAL PROOF OF Nat.compare_eq_gt -/

example {a b : Nat} : compare a b = .gt ↔ b < a := by
  rw [compare_def_lt]; (repeat' split) <;> simp [Nat.le_of_lt, *]