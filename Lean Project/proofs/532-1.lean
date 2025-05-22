import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example [LawfulBEq α] {a : α} {l₁ l₂ : List α} :
    (l₁ ++ l₂).erase a = if a ∈ l₁ then l₁.erase a ++ l₂ else l₁ ++ l₂.erase a := by
  rw [erase_eq_eraseP]
  rw [eraseP_append]
  split
  · intro h
    rw [h]
    exact if_pos rfl
  · intro h
    rw [h]
    exact if_neg rfl

/- ACTUAL PROOF OF List.erase_append -/

example [LawfulBEq α] {a : α} {l₁ l₂ : List α} :
    (l₁ ++ l₂).erase a = if a ∈ l₁ then l₁.erase a ++ l₂ else l₁ ++ l₂.erase a := by
  simp [erase_eq_eraseP, eraseP_append]