import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nodup
open Nat
variable [BEq α]

example [LawfulBEq α] {l} (d : Nodup l) (a : α) : l.erase a = l.filter (· != a) := by
  induction l generalizing a
  · simp
  · simp
    split
    · have : a ≠ x := by
        intro h
        apply d.2
        simp [h]
      simp [this]
    · cases decide (x == a)
      · simp
        apply Nodup.tail _ d
      · simp
        apply Nodup.tail _ d

/- ACTUAL PROOF OF List.Nodup.erase_eq_filter -/

example [LawfulBEq α] {l} (d : Nodup l) (a : α) : l.erase a = l.filter (· != a) := by
  induction d with
  | nil => rfl
  | cons m _n ih =>
    rename_i b l
    by_cases h : b = a
    · subst h
      rw [erase_cons_head, filter_cons_of_neg (by simp)]
      apply Eq.symm
      rw [filter_eq_self]
      simpa [@eq_comm α] using m
    · simp [beq_false_of_ne h, ih, h]