import Mathlib.Data.Fintype.List
import Mathlib.Data.List.Cycle

open List
variable {α : Type*} [DecidableEq α]

example (xs : List α) (y x d : α) (h : x ≠ y) :
    nextOr (y :: xs) x d = nextOr xs x d := by
  cases xs
  · rfl
  · case cons z zs =>
    simp only [nextOr, ite_eq_right_iff]
    intro h'
    contradiction

/- ACTUAL PROOF OF List.nextOr_cons_of_ne -/

example (xs : List α) (y x d : α) (h : x ≠ y) :
    nextOr (y :: xs) x d = nextOr xs x d := by
  cases' xs with z zs
  · rfl
  · exact if_neg h