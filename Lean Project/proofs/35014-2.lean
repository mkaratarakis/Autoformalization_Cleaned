import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example : l₁ <:+ a :: l₂ ↔ l₁ = a :: l₂ ∨ l₁ <:+ l₂ := by
  constructor
  · intro h
    cases h with
    | inl h =>
      simp only [List.cons_append, List.cons_inj] at h
      obtain rfl | h := h
      · exact Or.inl rfl
      · exact Or.inr h
    | inr h =>
      exact Or.inr h
  · rintro (rfl | h)
    · exact Sublist.refl _
    · exact Sublist.cons_sublist _ h

/- ACTUAL PROOF OF List.suffix_cons_iff -/

example : l₁ <:+ a :: l₂ ↔ l₁ = a :: l₂ ∨ l₁ <:+ l₂ := by
  constructor
  · rintro ⟨⟨hd, tl⟩, hl₃⟩
    · exact Or.inl hl₃
    · simp only [cons_append] at hl₃
      injection hl₃ with _ hl₄
      exact Or.inr ⟨_, hl₄⟩
  · rintro (rfl | hl₁)
    · exact (a :: l₂).suffix_refl
    · exact hl₁.trans (l₂.suffix_cons _)