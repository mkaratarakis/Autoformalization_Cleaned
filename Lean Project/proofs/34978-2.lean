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
    obtain ⟨t, rfl⟩ := isSuffixOf.eq_append.mp h
    exact ⟨t, by rfl⟩
  · rintro ⟨t, rfl⟩
    exact isSuffixOf.eq_append.mpr ⟨t, rfl⟩

/- ACTUAL PROOF OF List.isSuffixOf_iff_suffix -/

example [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isSuffixOf l₂ ↔ l₁ <:+ l₂ := by
  simp [isSuffixOf]