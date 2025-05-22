import Init.Data.List.Lemmas
import Init.Data.List.MinMax

open List
open Nat


example [Min α] {n : Nat} {a : α} (w : min a a = a) (h : 0 < n) :
    (replicate n a).minimum? = some a := by
  simp [minimum?_replicate, Nat.ne_of_gt h, w]