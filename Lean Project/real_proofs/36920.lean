import Mathlib.Data.Fintype.List
import Mathlib.Data.List.Cycle

open List
variable {α : Type*} [DecidableEq α]


example (xs : List α) (x d d' : α) (x_mem : x ∈ xs)
    (x_ne : x ≠ xs.getLast (ne_nil_of_mem x_mem)) : nextOr xs x d = nextOr xs x d' := by
  induction' xs with y ys IH
  · cases x_mem
  cases' ys with z zs
  · simp at x_mem x_ne
    contradiction
  by_cases h : x = y
  · rw [h, nextOr_self_cons_cons, nextOr_self_cons_cons]
  · rw [nextOr, nextOr, IH]
    · simpa [h] using x_mem
    · simpa using x_ne