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
  rw [count_append]
  simp
  simp [count]

/- ACTUAL PROOF OF List.count_concat_self -/

example (a : α) (l : List α) :
    count a (concat l a) = (count a l) + 1 := by
  simp