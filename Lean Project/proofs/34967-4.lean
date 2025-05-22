import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {l₁ l₂ : List α} (f : α → Option β) (H : l₁ ⊆ l₂) :
    filterMap f l₁ ⊆ filterMap f l₂ := by
  intro x hx
  rw [List.mem_filterMap] at hx ⊢
  rcases hx with ⟨a, ha, (rfl : f a = some x)⟩
  exact ⟨a, H ha, rfl⟩

/- ACTUAL PROOF OF List.filterMap_subset -/

example {l₁ l₂ : List α} (f : α → Option β) (H : l₁ ⊆ l₂) :
    filterMap f l₁ ⊆ filterMap f l₂ := by
  intro x
  simp only [mem_filterMap]
  rintro ⟨a, h, w⟩
  exact ⟨a, H h, w⟩