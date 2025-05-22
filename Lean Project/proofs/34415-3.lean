import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {a b : α} : Pairwise R [a, b] ↔ R a b := by
  constructor
  · intro h
    exact h _ _ (by simp)
  · intro h
    apply Pairwise.cons
    · intro c _
      exact h.elim

/- ACTUAL PROOF OF List.pairwise_pair -/

example {a b : α} : Pairwise R [a, b] ↔ R a b := by
  simp