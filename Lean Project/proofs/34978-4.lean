import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isSuffixOf l₂ ↔ l₁ <:+ l₂ := by
  constructor
  · intro h
    rw [isSuffixOf] at h
    obtain ⟨t, rfl⟩ := h
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    rw [isSuffixOf]
    exact ⟨t, rfl⟩

/- ACTUAL PROOF OF List.isSuffixOf_iff_suffix -/

example [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isSuffixOf l₂ ↔ l₁ <:+ l₂ := by
  simp [isSuffixOf]