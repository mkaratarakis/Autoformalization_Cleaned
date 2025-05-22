import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example [LawfulBEq α] (a : α) (l : List α) :
    length (l.erase a) = if a ∈ l then length l - 1 else length l := by
  cases l with
  | nil =>
    simp only [erase, length, List.length, List.mem, Bool.cond_false, Sub.sub_zero]
  | cons h t =>
    by_cases hbeq : a = h
    · simp only [hbeq, erase, length]
      rw [Bool.cond_true]
      rw [Nat.sub_self]
      rw [Nat.zero_add]
    · simp only [hbeq, erase, length, erase_ne_head hbeq]
      rw [Bool.cond_false]
      apply length_erase_of_ne
      exact hbeq

/- ACTUAL PROOF OF List.length_erase -/

example [LawfulBEq α] (a : α) (l : List α) :
    length (l.erase a) = if a ∈ l then length l - 1 else length l := by
  rw [erase_eq_eraseP, length_eraseP]
  split <;> split <;> simp_all