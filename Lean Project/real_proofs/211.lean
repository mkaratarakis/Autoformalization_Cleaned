import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]


example [LawfulBEq α] {a : α} {l : List α} (h : a ∈ l) :
    length (l.erase a) = length l - 1 := by
  rw [erase_eq_eraseP]; exact length_eraseP_of_mem h (beq_self_eq_true a)