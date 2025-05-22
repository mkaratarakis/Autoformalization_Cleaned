import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example (R) (a : α) : Pairwise R [a] := by
  apply Pairwise.single

/- ACTUAL PROOF OF List.pairwise_singleton -/

example (R) (a : α) : Pairwise R [a] := by
  simp