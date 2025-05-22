import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {l : List α} (H : ∀ x y, R x y) : Pairwise R l := by
  induction l with
  | nil =>
    apply Pairwise.nil
  | cons hd tl ih =>
    apply Pairwise.cons
    · exact H
    · exact ih

/- ACTUAL PROOF OF List.pairwise_of_forall -/

example {l : List α} (H : ∀ x y, R x y) : Pairwise R l := by
  induction l <;> simp [*]