import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example (f : β → γ) (l₁ : List α) (l₂ : List β) :
    zip l₁ (l₂.map f) = (zip l₁ l₂).map (Prod.map id f) := by
  induction l₁ generalizing l₂
  · simp
  · simp [zip]
    cases h : l₂
    · simp
    · simp [h]

/- ACTUAL PROOF OF List.zip_map_right -/

example (f : β → γ) (l₁ : List α) (l₂ : List β) :
    zip l₁ (l₂.map f) = (zip l₁ l₂).map (Prod.map id f) := by
  rw [← zip_map, map_id]