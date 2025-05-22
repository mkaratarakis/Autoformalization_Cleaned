import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]
variable [LawfulBEq α]

example (a : α) (l : List α) :
    count a (List.erase l a) = count a l - 1 := by
  rw [erase_count_eq a l a]
  rw [if_pos rfl]
  rfl

/- ACTUAL PROOF OF List.count_erase_self -/

example (a : α) (l : List α) :
    count a (List.erase l a) = count a l - 1 := by
  rw [count_erase, if_pos (by simp)]