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
      exact Or.inl hx
    · intros x hx
      apply h
      exact Or.inr hx
  · intros h
    intros x hx
    cases h
    · cases hx
      apply h_left
    · cases hx
      apply h_right

/- ACTUAL PROOF OF List.append_subset -/

example {l₁ l₂ l : List α} :
    l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l := by
  simp [subset_def, or_imp, forall_and]