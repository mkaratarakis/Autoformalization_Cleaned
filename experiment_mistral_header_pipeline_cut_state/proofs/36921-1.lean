import Mathlib.Data.Fintype.List
import Mathlib.Data.List.Cycle

open List
variable {α : Type*} [DecidableEq α]
variable (l : List α) (x : α)

example (y : α) (hxy : x ∈ y :: l) (hx : x = y) :
    prev (y :: l) x hxy = getLast (y :: l) (cons_ne_nil _ _) := by
  cases l with
  | nil =>
    simp
    rw [hx]
  | head :: tail =>
    simp
    rw [hx, prev, getLast, getLast_cons]
    exact (prev_aux_last _ _ _ _).symm

/- ACTUAL PROOF OF List.prev_getLast_cons' -/

example (y : α) (hxy : x ∈ y :: l) (hx : x = y) :
    prev (y :: l) x hxy = getLast (y :: l) (cons_ne_nil _ _) := by
  cases l <;> simp [prev, hx]