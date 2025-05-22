import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open IsInfix
open Nat
variable [BEq α]
variable [BEq α]

example (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) :
    l₁.filter p <:+: l₂.filter p := by
  rw [Sublist.contiguousSublist] at h
  rcases h with ⟨xs, ys, rfl⟩
  rw [List.filter_append_append p xs l₁ ys]
  exact IsInfix.isInfix (List.filter p l₁) ((List.filter p xs) ++ List.filter p l₁) ((List.filter p ys))

/- ACTUAL PROOF OF List.IsInfix.filter -/

example (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) :
    l₁.filter p <:+: l₂.filter p := by
  obtain ⟨xs, ys, rfl⟩ := h
  rw [filter_append, filter_append]; apply infix_append _