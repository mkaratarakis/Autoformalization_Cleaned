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
    induction l₁ with
    | nil => simp [Sublist.subset]
    | cons x xs ih =>
      simp [Sublist.subset]
      apply And.intro
      · apply h
        simp [reverse, append]
        exact Or.inr (Sublist.subset.1 h)
      · apply ih
        apply Sublist.of_mem_reverse
        simp [reverse]
        apply Sublist.cons
        apply h
        apply Sublist.tail_subset
        apply h
  case mpr =>
    intro h
    induction l₁ with
    | nil => simp [Sublist.subset]
    | cons x xs ih =>
      simp [Sublist.subset]
      apply And.intro
      · apply h
      · apply ih
        apply Sublist.of_mem_reverse
        simp [reverse]
        apply Sublist.cons
        apply h
        apply Sublist.tail_subset
        apply h

/- ACTUAL PROOF OF List.reverse_subset -/

example {l₁ l₂ : List α} : reverse l₁ ⊆ l₂ ↔ l₁ ⊆ l₂ := by
  simp [subset_def]