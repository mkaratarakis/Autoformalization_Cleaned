import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b = .gt ↔ b < a := by
  constructor
  · intro h
    unfold compare at h
    simp at h
    cases h
    case inl h =>
      exact Nat.lt_of_sub_eq_zero h
    case inr h =>
      contradiction
  · intro h
    unfold compare
    simp
    exact Or.inl (Nat.zero_eq_of_lt h)

/- ACTUAL PROOF OF Nat.compare_eq_gt -/

example {a b : Nat} : compare a b = .gt ↔ b < a := by
  rw [compare_def_lt]; (repeat' split) <;> simp [Nat.le_of_lt, *]