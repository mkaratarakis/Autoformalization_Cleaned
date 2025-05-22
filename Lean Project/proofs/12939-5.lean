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
  induction l generalizing a
  · simp
  · by_cases h : head = a
    · simp [h]
      rfl
    · simp [h]
      rw [erase_ne (Ne.symm h)]
      rw [count_cons_ne (Ne.symm h)]
      rw [count_cons_ne (Ne.symm h)]
      exact Nat.succ_inj (tail_ih a)

/- ACTUAL PROOF OF List.count_erase_self -/

example (a : α) (l : List α) :
    count a (List.erase l a) = count a l - 1 := by
  rw [count_erase, if_pos (by simp)]