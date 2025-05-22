import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat


example (h : 0 < n) : findSome? f (replicate n a) = f a := by
  simp [findSome?_replicate, Nat.ne_of_gt h]