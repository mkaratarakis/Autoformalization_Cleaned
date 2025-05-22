import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example [LawfulBEq α] (a : α) (l : List α) :
    length (l.erase a) = if a ∈ l then length l - 1 else length l := by
  cases l with
  | nil =>
    simp only [List.erase, List.length, if_t_t]
  | cons h t =>
    cases hbeq : BEq.beq a h with
    | isTrue hbeq =>
      simp only [List.erase, hbeq, List.length, if_t, List.length]
    | isFalse hbeq =>
      simp only [List.erase, hbeq, List.length, if_f]
      apply erase_ne_head
      simp only [List.length, List.erase]
      exact length_erase_of_ne hbeq

/- ACTUAL PROOF OF List.length_erase -/

example [LawfulBEq α] (a : α) (l : List α) :
    length (l.erase a) = if a ∈ l then length l - 1 else length l := by
  rw [erase_eq_eraseP, length_eraseP]
  split <;> split <;> simp_all