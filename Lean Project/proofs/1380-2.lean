import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b = .lt ↔ a < b := by
  constructor
  · intro h
    unfold compare at h
    simp at h
    simp [Nat.lt_iff_add_one_le]
    exact h
  · intro h
    unfold compare
    rw [Nat.lt_iff_add_one_le] at h
    simp [h]
    simp

/- ACTUAL PROOF OF Nat.compare_eq_lt -/

example {a b : Nat} : compare a b = .lt ↔ a < b := by
  rw [compare_def_lt]; (repeat' split) <;> simp [*]