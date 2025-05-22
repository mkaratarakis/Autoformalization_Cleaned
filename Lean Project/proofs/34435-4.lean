import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l : List α} {n m : Nat} (h : m < n) : (l.take n)[m]? = l[m]? := by
  cases h' : l.take n with
  | nil =>
    simp
  | cons hd tl =>
    simp
    apply Nat.lt_of_succ_lt_succ
    exact h

/- ACTUAL PROOF OF List.get?_take -/

example {l : List α} {n m : Nat} (h : m < n) : (l.take n).get? m = l.get? m := by
  simp [getElem?_take, h]