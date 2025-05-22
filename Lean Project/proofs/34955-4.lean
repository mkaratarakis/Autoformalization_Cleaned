import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {l₁ : List β} {f : α → β} :
    l₁ <+ l₂.map f ↔ ∃ l', l' <+ l₂ ∧ l₁ = l'.map f := by
  constructor
  · intro h
    obtain ⟨l', hl'⟩ := Sublist.map_left_iff.1 h
    use l'
    exact hl'
  · rintro ⟨l', hl', rfl⟩
    exact Sublist.map_left_iff.2 ⟨l', hl'⟩

/- ACTUAL PROOF OF List.sublist_map_iff -/

example {l₁ : List β} {f : α → β} :
    l₁ <+ l₂.map f ↔ ∃ l', l' <+ l₂ ∧ l₁ = l'.map f := by
  simp only [← filterMap_eq_map, sublist_filterMap_iff]