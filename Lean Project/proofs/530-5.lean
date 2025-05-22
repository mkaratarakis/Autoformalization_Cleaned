import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example [LawfulBEq α] {l₁ : List α} (l₂) (h : a ∈ l₁) :
    (l₁ ++ l₂).erase a = l₁.erase a ++ l₂ := by
  induction l₁ generalizing l₂
  case nil =>
    simp
  case cons x l₁ ih =>
    by_cases h' : a = x
    · simp [h']
    · simp [h']
      exact ih _ h

/- ACTUAL PROOF OF List.erase_append_left -/

example [LawfulBEq α] {l₁ : List α} (l₂) (h : a ∈ l₁) :
    (l₁ ++ l₂).erase a = l₁.erase a ++ l₂ := by
  simp [erase_eq_eraseP]; exact eraseP_append_left (beq_self_eq_true a) l₂ h