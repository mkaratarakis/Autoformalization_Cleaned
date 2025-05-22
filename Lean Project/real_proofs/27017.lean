import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example (l₁ : List α) (l₂ : List β) (f : α → α') (g : Option α' → Option β → γ) :
    zipWithAll g (l₁.map f) l₂ = zipWithAll (fun a b => g (f <$> a) b) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all