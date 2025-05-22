import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example : l₁ <+: a :: l₂ ↔ l₁ = [] ∨ ∃ t, l₁ = a :: t ∧ t <+: l₂ := by
  constructor
  · intro h
    by_cases hl₁ : l₁ = []
    · left
      exact hl₁
    · right
      exists l₁.tail
      constructor
      · rfl
      · apply Sublist.append_right
        use l₁.tail
        rw [← h]
        exact Sublist.refl _
  · intro h
    cases h
    · left
      rfl
    · right
      rcases h with ⟨t, rfl, ht⟩
      rw [← ht]
      exact Sublist.refl _

/- ACTUAL PROOF OF List.prefix_cons_iff -/

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