import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {l₁ : List α} {p : α → Bool} :
    l₁ <+ l₂.filter p ↔ ∃ l', l' <+ l₂ ∧ l₁ = l'.filter p := by
  constructor
  · intro h
    exists (l₂.filter p)
    exact ⟨Sublist.refl _, h⟩
  · rintro ⟨l', hl', rfl⟩
    exact hl'

/- ACTUAL PROOF OF List.sublist_filter_iff -/

example {l₁ : List α} {p : α → Bool} :
    l₁ <+ l₂.filter p ↔ ∃ l', l' <+ l₂ ∧ l₁ = l'.filter p := by
  simp only [← filterMap_eq_filter, sublist_filterMap_iff]