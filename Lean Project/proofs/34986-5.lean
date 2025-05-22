import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open IsInfix
open Nat
variable [BEq α]
variable [BEq α]

example (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) :
    l₁.filter p <:+: l₂.filter p := by
  obtain ⟨s, t, rfl⟩ := h
  simp only [filter, append, Bool.bind, forM]
  exact IsInfix.isInfix (filter p l₁) ((filter p s) ++ filter p l₁ ++ filter p t)

/- ACTUAL PROOF OF List.IsInfix.filter -/

example (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) :
    l₁.filter p <:+: l₂.filter p := by
  obtain ⟨xs, ys, rfl⟩ := h
  rw [filter_append, filter_append]; apply infix_append _