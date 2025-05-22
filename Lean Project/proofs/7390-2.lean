import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example (l : List α) (n : Nat) :
    (l.drop n).head? = l[n]? := by
  rw [← get?_eq_nth]
  rw [get?_drop]
  rw [zero_add]

/- ACTUAL PROOF OF List.head?_drop -/

example (l : List α) (n : Nat) :
    (l.drop n).head? = l[n]? := by
  rw [head?_eq_getElem?, getElem?_drop, Nat.add_zero]