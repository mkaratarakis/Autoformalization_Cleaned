import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat


example (h : 0 < n) : find? p (replicate n a) = if p a then some a else none := by
  simp [find?_replicate, Nat.ne_of_gt h]