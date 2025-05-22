import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {l₁ l₂ l : List α} :
    l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l := by
  constructor
  · intros h
    constructor
    · intros x hx
      apply h
      exact mem_append_left _ _ hx
    · intros x hx
      apply h
      exact mem_append_right _ _ hx
  · intros h
    intros x hx
    cases hx
    · apply h.1
      assumption
    · apply h.2
      assumption

/- ACTUAL PROOF OF List.append_subset -/

example {l₁ l₂ l : List α} :
    l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l := by
  simp [subset_def, or_imp, forall_and]