import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {l : List α} {n : Nat} (h : l.drop n ≠ []) :
    (l.drop n).head h = l[n]'(by simp_all) := by
  have hn : n < l.length := by
    contrapose! h
    apply drop_eq_nil_iff.2
    simp
  have : n < l.length := by exact hn
  rw [head_cons, get?_eq_get, drop_append_of_le]
  exact this

/- ACTUAL PROOF OF List.head_drop -/

example {l : List α} {n : Nat} (h : l.drop n ≠ []) :
    (l.drop n).head h = l[n]'(by simp_all) := by
  have w : n < l.length := length_lt_of_drop_ne_nil h
  simpa [head?_eq_head, getElem?_eq_getElem, h, w] using head?_drop l n