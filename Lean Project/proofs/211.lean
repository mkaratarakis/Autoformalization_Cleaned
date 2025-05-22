import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example [LawfulBEq α] {a : α} {l : List α} (h : a ∈ l) :
    length (l.erase a) = length l - 1 := by
  rw [erase_eq_eraseP]
  apply length_eraseP_of_mem
  · exact h
  · apply beq_of_eq
    rfl

/- ACTUAL PROOF OF List.length_erase_of_mem -/

example [LawfulBEq α] {a : α} {l : List α} (h : a ∈ l) :
    length (l.erase a) = length l - 1 := by
  rw [erase_eq_eraseP]; exact length_eraseP_of_mem h (beq_self_eq_true a)