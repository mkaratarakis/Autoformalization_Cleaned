import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b = .eq ↔ a = b := by
  constructor
  · intro h
    by_cases h1 : a < b
    · simp [compare, h1] at h
    · by_cases h2 : b < a
      · simp [compare, h2] at h
      · have : a ≤ b ∧ b ≤ a
        · constructor
          · exact le_of_not_gt h2
          · exact le_of_not_gt h1
        linarith
  · intro h
    simp [compare, h]

/- ACTUAL PROOF OF Nat.compare_eq_eq -/

example {a b : Nat} : compare a b = .eq ↔ a = b := by
  rw [compare_def_lt]; (repeat' split) <;> simp [Nat.ne_of_lt, Nat.ne_of_gt, *]
  next hlt hgt => exact Nat.le_antisymm (Nat.not_lt.1 hgt) (Nat.not_lt.1 hlt)