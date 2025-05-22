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
    obtain ⟨xs, hxs⟩ := h
    use xs
    exact hxs
  rcases h₁ with ⟨xs, rfl⟩
  rw [filter_append]
  have : l₁.filter p <+: l₁.filter p ++ xs.filter p := by
    use xs.filter p

  rw [this]
  exact List.isPrefix.refl _

/- ACTUAL PROOF OF List.IsPrefix.filter -/

example (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    l₁.filter p <+: l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]; apply prefix_append