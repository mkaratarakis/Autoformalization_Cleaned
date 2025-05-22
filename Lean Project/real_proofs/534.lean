import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]


example [LawfulBEq α] {a : α} {l₁ : List α} (l₂ : List α) (h : a ∉ l₁) :
    (l₁ ++ l₂).erase a = (l₁ ++ l₂.erase a) := by
  rw [erase_eq_eraseP, erase_eq_eraseP, eraseP_append_right]
  intros b h' h''; rw [eq_of_beq h''] at h; exact h h'