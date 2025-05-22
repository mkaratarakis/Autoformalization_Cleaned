import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat


example (h : p a) : find? p (replicate n a) = if n = 0 then none else some a := by
  simp [find?_replicate, h]