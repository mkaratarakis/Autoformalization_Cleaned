import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example (l₁ : List α) (l₂ : List β) (f : β → β') (g : Option α → Option β' → γ) :
    zipWithAll g l₁ (l₂.map f) = zipWithAll (fun a b => g a (f <$> b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all