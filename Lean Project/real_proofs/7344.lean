import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat


example {l : List α} {n m : Nat} (h : n ≤ m) :
    (l.take n).get? m = none := by
  simp [getElem?_take_eq_none h]