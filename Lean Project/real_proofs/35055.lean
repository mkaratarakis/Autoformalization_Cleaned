import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]


example : l₁ <+: a :: l₂ ↔ l₁ = [] ∨ ∃ t, l₁ = a :: t ∧ t <+: l₂ := by
  cases l₁ with
  | nil => simp
  | cons a' l₁ =>
    constructor
    · rintro ⟨t, h⟩
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨l₁, rfl, prefix_append l₁ t⟩
    · rintro (h | ⟨t, w, ⟨s, h'⟩⟩)
      · simp [h]
      · simp only [w]
        refine ⟨s, by simp [h']⟩