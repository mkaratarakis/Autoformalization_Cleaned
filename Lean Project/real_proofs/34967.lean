import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]


example {l₁ l₂ : List α} (f : α → Option β) (H : l₁ ⊆ l₂) :
    filterMap f l₁ ⊆ filterMap f l₂ := by
  intro x
  simp only [mem_filterMap]
  rintro ⟨a, h, w⟩
  exact ⟨a, H h, w⟩