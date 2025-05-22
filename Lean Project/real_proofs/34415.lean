import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat


example {a b : α} : Pairwise R [a, b] ↔ R a b := by
  simp