import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b = .gt ↔ b < a := by
  constructor
  · intro h
    cases compare_eq_gt_iff_lt.mp h
    exact compare_eq_gt_iff_lt.mpr h
  · intro h
    cases compare_eq_gt_iff_lt.mpr h
    exact compare_eq_gt_iff_lt.mp h

/- ACTUAL PROOF OF Nat.compare_eq_gt -/

example {a b : Nat} : compare a b = .gt ↔ b < a := by
  rw [compare_def_lt]; (repeat' split) <;> simp [Nat.le_of_lt, *]