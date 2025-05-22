import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {a b : α} : Pairwise R [a, b] ↔ R a b := by
  constructor
  · intro h
    exact Pairwise.nil.2 h
  · intro h
    exact Pairwise.cons.2 (Pairwise.nil.2 h)

/- ACTUAL PROOF OF List.pairwise_pair -/

example {a b : α} : Pairwise R [a, b] ↔ R a b := by
  simp