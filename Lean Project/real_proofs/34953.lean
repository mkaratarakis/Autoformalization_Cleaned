import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]


example {l₁ : List α} {p : α → Bool} :
    l₁ <+ l₂.filter p ↔ ∃ l', l' <+ l₂ ∧ l₁ = l'.filter p := by
  simp only [← filterMap_eq_filter, sublist_filterMap_iff]