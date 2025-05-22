import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Pairwise
open Nat

example (hR : Pairwise R l) (hS : Pairwise S l) :
    l.Pairwise fun a b => R a b ∧ S a b := by
  induction l generalizing a b
  case nil =>
    apply Pairwise.nil
  case cons a l ih =>
    apply Pairwise.cons
    . intro b hb
      apply And.intro
      . apply hR.out
        . exact hb
      . apply hS.out
        . exact hb
    . apply ih
      . constructor
        . exact hR.tail
        . exact hS.tail

/- ACTUAL PROOF OF List.Pairwise.and -/

example (hR : Pairwise R l) (hS : Pairwise S l) :
    l.Pairwise fun a b => R a b ∧ S a b := by
  induction hR with
  | nil => simp only [Pairwise.nil]
  | cons R1 _ IH =>
    simp only [Pairwise.nil, pairwise_cons] at hS ⊢
    exact ⟨fun b bl => ⟨R1 b bl, hS.1 b bl⟩, IH hS.2⟩