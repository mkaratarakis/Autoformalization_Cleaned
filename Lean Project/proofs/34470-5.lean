import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {l : List α} :
    l.reverse.Pairwise R ↔ l.Pairwise (fun a b => R b a) := by
  induction l with
  | nil =>
    simp
  | cons hd tl ih =>
    simp [reverse, Pairwise]
    constructor
    · intro h
      exact And.intro (ih.mp h.1) h.2
    · intro h
      exact And.intro (ih.mpr h.1) h.2

/- ACTUAL PROOF OF List.pairwise_reverse -/

example {l : List α} :
    l.reverse.Pairwise R ↔ l.Pairwise (fun a b => R b a) := by
  induction l <;> simp [*, pairwise_append, and_comm]