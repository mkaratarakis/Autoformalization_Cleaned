import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]


example (a : α) (l : List α) : l.erase a = l.eraseP (· == a) := by
  induction l
  · simp
  · next b t ih =>
    rw [erase_cons, eraseP_cons, ih]
    if h : b == a then simp [h] else simp [h]