import Init.Data.List.Lemmas
import Init.Data.List.MinMax

open List
open Nat


example [Max α] {n : Nat} {a : α} (w : max a a = a) (h : 0 < n) :
    (replicate n a).maximum? = some a := by
  simp [maximum?_replicate, Nat.ne_of_gt h, w]