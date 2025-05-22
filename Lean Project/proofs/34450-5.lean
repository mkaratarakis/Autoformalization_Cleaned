import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Pairwise
open Nat

example (hR : Pairwise R l) (hS : Pairwise S l) :
    l.Pairwise fun a b => R a b ∧ S a b := by
  induction l
  case nil =>
    exact Pairwise.nil
  case cons x xs ih =>
    apply Pairwise.cons
    · intro y hy
      have h1 : R x y := by
        apply Pairwise.rel hR
        · exact Mem.head _
        · exact hy
      have h2 : S x y := by
        apply Pairwise.rel hS
        · exact Mem.head _
        · exact hy
      exact And.intro h1 h2
    · exact ih (Pairwise.tail hR) (Pairwise.tail hS)

/- ACTUAL PROOF OF List.Pairwise.and -/

example (hR : Pairwise R l) (hS : Pairwise S l) :
    l.Pairwise fun a b => R a b ∧ S a b := by
  induction hR with
  | nil => simp only [Pairwise.nil]
  | cons R1 _ IH =>
    simp only [Pairwise.nil, pairwise_cons] at hS ⊢
    exact ⟨fun b bl => ⟨R1 b bl, hS.1 b bl⟩, IH hS.2⟩