import Mathlib.Data.Fintype.List
import Mathlib.Data.List.Cycle

open List
variable {α : Type*} [DecidableEq α]
variable (l : List α) (x : α)

example (h : x ∈ l) (y : α) (h : x ∈ y :: l) (hy : x ≠ y)
    (hx : x ≠ getLast (y :: l) (cons_ne_nil _ _)) :
    next (y :: l) x h = next l x (by simpa [hy] using h) := by
rw [next, next, nextOr_cons_of_ne _ _ _ _ hy, nextOr_eq_nextOr_of_mem_of_ne]
  · rwa [getLast_cons] at hx
    exact ne_nil_of_mem h
  · rwa [getLast_cons] at hx

/- ACTUAL PROOF OF List.next_ne_head_ne_getLast -/

example (h : x ∈ l) (y : α) (h : x ∈ y :: l) (hy : x ≠ y)
    (hx : x ≠ getLast (y :: l) (cons_ne_nil _ _)) :
    next (y :: l) x h = next l x (by simpa [hy] using h) := by
  rw [next, next, nextOr_cons_of_ne _ _ _ _ hy, nextOr_eq_nextOr_of_mem_of_ne]
  · rwa [getLast_cons] at hx
    exact ne_nil_of_mem (by assumption)
  · rwa [getLast_cons] at hx