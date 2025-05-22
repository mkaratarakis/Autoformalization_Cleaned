import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example {l : List α} {n m : Nat} (h : m < n) : (l.take n).get? m = l.get? m := by
  simp [getElem?_take, h]