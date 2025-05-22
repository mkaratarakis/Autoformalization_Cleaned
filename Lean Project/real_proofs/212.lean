import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]


example [LawfulBEq α] (a : α) (l : List α) :
    length (l.erase a) = if a ∈ l then length l - 1 else length l := by
  rw [erase_eq_eraseP, length_eraseP]
  split <;> split <;> simp_all