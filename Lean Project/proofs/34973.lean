import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {l₁ l₂ : List α} : l₁ ⊆ reverse l₂ ↔ l₁ ⊆ l₂ := by
  constructor
  · intro h x hx
    apply List.subset_reverse.mp h
    exact hx
  · intro h x hx
    apply List.subset_reverse.mpr h
    exact hx

/- ACTUAL PROOF OF List.subset_reverse -/

example {l₁ l₂ : List α} : l₁ ⊆ reverse l₂ ↔ l₁ ⊆ l₂ := by
  simp [subset_def]