import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]
variable [LawfulBEq α]

example (a : α) (l : List α) :
    count a (concat l a) = (count a l) + 1 := by
  rw [concat.eq_def]
  exact count_append_right a l [a]

/- ACTUAL PROOF OF List.count_concat_self -/

example (a : α) (l : List α) :
    count a (concat l a) = (count a l) + 1 := by
  simp