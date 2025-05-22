import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example (l₁ : List α) (l₂ : List β) (f : β → β') (g : Option α → Option β' → γ) :
    zipWithAll g l₁ (l₂.map f) = zipWithAll (fun a b => g a (f <$> b)) l₁ l₂ := by
  induction l₁ generalizing l₂
  · -- Base case: l₁ is empty
    cases l₂
    · -- Subcase 1: l₂ is empty
      simp
    · -- Subcase 2: l₂ is non-empty
      simp
  · -- Inductive step: l₁ is non-empty
    cases l₂
    · -- Subcase 1: l₂ is empty
      simp
    · -- Subcase 2: l₂ is non-empty
      simp [zipWithAll, map]
      apply l₁_ih

/- ACTUAL PROOF OF List.zipWithAll_map_right -/

example (l₁ : List α) (l₂ : List β) (f : β → β') (g : Option α → Option β' → γ) :
    zipWithAll g l₁ (l₂.map f) = zipWithAll (fun a b => g a (f <$> b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all