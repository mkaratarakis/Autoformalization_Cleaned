import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example (l₁ : List α) (l₂ : List β) (f : β → β') (g : α → β' → γ) :
    zipWith g l₁ (l₂.map f) = zipWith (fun a b => g a (f b)) l₁ l₂ := by
  induction l₁ generalizing l₂
  · simp
  · cases l₂
    · simp
    · simp [zipWith]
      rw [ih]
      rfl

/- ACTUAL PROOF OF List.zipWith_map_right -/

example (l₁ : List α) (l₂ : List β) (f : β → β') (g : α → β' → γ) :
    zipWith g l₁ (l₂.map f) = zipWith (fun a b => g a (f b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all