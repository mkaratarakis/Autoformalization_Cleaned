import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]


example {l₁ : List β} {f : α → β} :
    l₁ <+ l₂.map f ↔ ∃ l', l' <+ l₂ ∧ l₁ = l'.map f := by
  simp only [← filterMap_eq_map, sublist_filterMap_iff]