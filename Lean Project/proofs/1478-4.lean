import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b ≠ .gt ↔ a ≤ b := by
  constructor
  · intro h
    by_cases h' : a < b
    · exact le_of_lt h'
    · have : compare a b = .eq ∨ compare a b = .lt := by
        simp [compare, h']
        tauto
      simp [this, h]
  · intro h
    by_cases h' : a < b
    · have : compare a b = .lt := by simp [compare, h']
      intro contra
      simp [this] at contra
    · have : a = b := le_antisymm h (not_lt.mp h')
      have : compare a b = .eq := by simp [compare, this]
      intro contra
      simp [this] at contra

/- ACTUAL PROOF OF Nat.compare_ne_gt -/

example {a b : Nat} : compare a b ≠ .gt ↔ a ≤ b := by
  rw [compare_def_le]; (repeat' split) <;> simp [*]