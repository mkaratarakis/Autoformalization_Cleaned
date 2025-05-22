import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b = .gt ↔ b < a := by
  constructor
  · intro h
    cases h' : compare a b with
    | eq =>
      apply False.elim
      apply h
      exact h'
    | lt =>
      apply False.elim
      apply h
      exact h'
    | gt =>
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ a b) (Ne.symm (Ne.of_lt h'))
  · intro h
    rw [compare]
    split
    · intro h₁
      exact False.elim (not_lt_of_ge (Nat.le_of_lt_succ a b) h)
    · intro h₁
      apply Nat.lt_of_le_of_ne (Nat.le_of_lt_succ a b)
      apply Ne.symm
      exact not_lt.mp h₁ h

/- ACTUAL PROOF OF Nat.compare_eq_gt -/

example {a b : Nat} : compare a b = .gt ↔ b < a := by
  rw [compare_def_lt]; (repeat' split) <;> simp [Nat.le_of_lt, *]