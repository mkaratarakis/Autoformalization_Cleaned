import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {a b : α} : Pairwise R [a, b] ↔ R a b := by
  constructor
  · intro h
    apply Pairwise.rel
    exact h
  · intro h
    apply Pairwise.single
    exact h

/- ACTUAL PROOF OF List.pairwise_pair -/

example {a b : α} : Pairwise R [a, b] ↔ R a b := by
  simp