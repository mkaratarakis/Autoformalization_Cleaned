import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {l₁ l₂ : List α} : l₁ ⊆ reverse l₂ ↔ l₁ ⊆ l₂ := by
  constructor
  · intro h x hx
    exact (List.mem_reverse.mpr h) hx
  · intro h x hx
    exact (List.mem_reverse.mp h) hx

/- ACTUAL PROOF OF List.subset_reverse -/

example {l₁ l₂ : List α} : l₁ ⊆ reverse l₂ ↔ l₁ ⊆ l₂ := by
  simp [subset_def]