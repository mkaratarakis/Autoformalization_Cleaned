import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {l₁ l₂ : List α} : reverse l₁ ⊆ l₂ ↔ l₁ ⊆ l₂ := by
  constructor
  case mp =>
    intro h
    apply Sublist.trans
    apply Sublist.reverse_sublist
    assumption
  case mpr =>
    intro h
    apply Sublist.trans
    apply Sublist.reverse_sublist
    assumption

/- ACTUAL PROOF OF List.reverse_subset -/

example {l₁ l₂ : List α} : reverse l₁ ⊆ l₂ ↔ l₁ ⊆ l₂ := by
  simp [subset_def]