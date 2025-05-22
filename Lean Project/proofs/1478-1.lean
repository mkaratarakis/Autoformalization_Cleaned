import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b ≠ .gt ↔ a ≤ b := by
  constructor
  · intro h
    by_cases h' : a < b
    · simp [h', compare_lt_of_lt h'] at h
    · simp [compare_of_not_lt h'] at h
      cases h'
      · simp [compare_eq_of_eq h'] at h
      · simp [compare_gt_of_gt h'] at h
  · intro h
    by_cases h' : a < b
    · simp [h', compare_lt_of_lt h']
    · simp [compare_of_not_lt h']
      cases h'
      · simp [compare_eq_of_eq h']
      · simp [compare_gt_of_gt h']
        contradiction

/- ACTUAL PROOF OF Nat.compare_ne_gt -/

example {a b : Nat} : compare a b ≠ .gt ↔ a ≤ b := by
  rw [compare_def_le]; (repeat' split) <;> simp [*]