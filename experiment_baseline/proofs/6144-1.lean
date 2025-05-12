import Mathlib.Data.Ordering.Basic
import Mathlib.Order.Synonym
import Mathlib.Order.Compare

open Ordering
variable {α β : Type*}

example {o o' : Ordering} : o.swap = o' ↔ o = o'.swap := by
  constructor
  · intro h
    rw [h]
    exact swap_swap o'
  · intro h
    rw [← h]
    exact swap_swap o

/- ACTUAL PROOF OF Ordering.swap_eq_iff_eq_swap -/

example {o o' : Ordering} : o.swap = o' ↔ o = o'.swap := by
  rw [← swap_inj, swap_swap]