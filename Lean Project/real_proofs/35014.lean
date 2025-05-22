import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]


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