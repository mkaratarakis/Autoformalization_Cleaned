import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat


example {l : List α} {n : Nat} (h : l.drop n ≠ []) :
    (l.drop n).head h = l[n]'(by simp_all) := by
  have w : n < l.length := length_lt_of_drop_ne_nil h
  simpa [head?_eq_head, getElem?_eq_getElem, h, w] using head?_drop l n