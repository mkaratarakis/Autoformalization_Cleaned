import Mathlib.Data.Fintype.List
import Mathlib.Data.List.Cycle

open List
variable {α : Type*} [DecidableEq α]

example (xs : List α) (y x d : α) (h : x ≠ y) :
    nextOr (y :: xs) x d = nextOr xs x d := by
  cases xs
  · simp
  · simp only [nextOr, if_neg h]

/- ACTUAL PROOF OF List.nextOr_cons_of_ne -/

example (xs : List α) (y x d : α) (h : x ≠ y) :
    nextOr (y :: xs) x d = nextOr xs x d := by
  cases' xs with z zs
  · rfl
  · exact if_neg h