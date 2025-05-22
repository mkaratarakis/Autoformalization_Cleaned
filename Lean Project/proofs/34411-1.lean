import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example (R) (a : α) : Pairwise R [a] := by
  unfold Pairwise
  simp
  intros x h1 _ h2
  exfalso
  apply h2
  simp at h1
  assumption

/- ACTUAL PROOF OF List.pairwise_singleton -/

example (R) (a : α) : Pairwise R [a] := by
  simp