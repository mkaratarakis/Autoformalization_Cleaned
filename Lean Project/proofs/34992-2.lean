import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open IsPrefix
open Nat
variable [BEq α]
variable [BEq α]

example (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    l₁.filter p <+: l₂.filter p := by

  have h₁ : ∃ xs, l₂ = l₁ ++ xs := by
    exact h
  rcases h₁ with ⟨xs, rfl⟩
  rw [filter_append]
  exact isPrefix.append_right

/- ACTUAL PROOF OF List.IsPrefix.filter -/

example (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    l₁.filter p <+: l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]; apply prefix_append