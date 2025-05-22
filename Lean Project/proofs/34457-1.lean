import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Pairwise
open Nat

example {S : α → α → Prop}
    (H : ∀ {a b}, a ∈ l → b ∈ l → R a b → S a b) (p : Pairwise R l) : Pairwise S l := by
  induction l with
  | nil => exact pairwise.nil
  | cons hd tl ih =>
    apply pairwise.cons
    · intros a ha
      apply H
      · exact mem_cons_self _ _
      · exact ha
      · apply p.left
        exact ha
    · apply ih
      intros m hm m' hm' hmm'
      apply H
      · exact hm
      · exact hm'
      · apply p.right
        exact hmm'

/- ACTUAL PROOF OF List.Pairwise.imp_of_mem -/

example {S : α → α → Prop}
    (H : ∀ {a b}, a ∈ l → b ∈ l → R a b → S a b) (p : Pairwise R l) : Pairwise S l := by
  induction p with
  | nil => constructor
  | @cons a l r _ ih =>
    constructor
    · exact fun x h => H (mem_cons_self ..) (mem_cons_of_mem _ h) <| r x h
    · exact ih fun m m' => H (mem_cons_of_mem _ m) (mem_cons_of_mem _ m')