import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example (l₁ : List α) (l₂ : List β) (f : α → α') (g : α' → β → γ) :
    zipWith g (l₁.map f) l₂ = zipWith (fun a b => g (f a) b) l₁ l₂ := by
  induction l₁ generalizing l₂
  case nil =>
    cases l₂
    case nil => rfl
    case cons => rfl
  case cons x xs ih =>
    cases l₂
    case nil => rfl
    case cons y ys =>
      simp only [map, zipWith]
      rw [ih]

/- ACTUAL PROOF OF List.zipWith_map_left -/

example (l₁ : List α) (l₂ : List β) (f : α → α') (g : α' → β → γ) :
    zipWith g (l₁.map f) l₂ = zipWith (fun a b => g (f a) b) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all