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
    simp [Pairwise, reverse] at *
    constructor
    · intro h
      apply And.intro
      · apply ih.mp
        exact h.left
      · exact h.right
    · intro h
      apply And.intro
      · apply ih.mpr
        exact h.left
      · exact h.right

/- ACTUAL PROOF OF List.pairwise_reverse -/

example {l : List α} :
    l.reverse.Pairwise R ↔ l.Pairwise (fun a b => R b a) := by
  induction l <;> simp [*, pairwise_append, and_comm]