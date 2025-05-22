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
    simp [reverse] at *
    constructor
    · intro h
      apply And.intro
      · apply ih.mp
        simp
        intro h'
        apply h.left
        simp [Pairwise] at h'
        exact h'
      · simp
        exact h.right
    · intro h
      apply And.intro
      · apply ih.mpr
        simp
        intro h'
        apply h.left
        simp [Pairwise] at h'
        exact h'
      · simp
        exact h.right

/- ACTUAL PROOF OF List.pairwise_reverse -/

example {l : List α} :
    l.reverse.Pairwise R ↔ l.Pairwise (fun a b => R b a) := by
  induction l <;> simp [*, pairwise_append, and_comm]