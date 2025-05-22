import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example [LawfulBEq α] {a : α} {l₁ : List α} (l₂ : List α) (h : a ∉ l₁) :
    (l₁ ++ l₂).erase a = (l₁ ++ l₂.erase a) := by
  rw [erase_eq_eraseP]
  rw [eraseP_append_of_notMem]
  · intro b hb
    rw [not_iff_not]
    apply not_iff_of_ne
    intro contra
    apply h
    exact Mem.tail _ _ _ hb contra
  · rw [erase_eq_eraseP]

/- ACTUAL PROOF OF List.erase_append_right -/

example [LawfulBEq α] {a : α} {l₁ : List α} (l₂ : List α) (h : a ∉ l₁) :
    (l₁ ++ l₂).erase a = (l₁ ++ l₂.erase a) := by
  rw [erase_eq_eraseP, erase_eq_eraseP, eraseP_append_right]
  intros b h' h''; rw [eq_of_beq h''] at h; exact h h'