import Mathlib.Data.Fintype.List
import Mathlib.Data.List.Cycle

open List
variable {α : Type*} [DecidableEq α]
variable (l : List α) (x : α)

example (y : α) (hxy : x ∈ y :: l) (hx : x = y) :
    prev (y :: l) x hxy = getLast (y :: l) (cons_ne_nil _ _) := by
  cases l
  · simp
  · rw [hx] at hxy
    simp [prev, if_pos rfl]
    rfl

/- ACTUAL PROOF OF List.prev_getLast_cons' -/

example (y : α) (hxy : x ∈ y :: l) (hx : x = y) :
    prev (y :: l) x hxy = getLast (y :: l) (cons_ne_nil _ _) := by
  cases l <;> simp [prev, hx]