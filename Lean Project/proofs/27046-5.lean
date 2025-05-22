import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {μ} (f : Option γ → Option δ → μ) (g : α → γ) (h : β → δ) (l₁ : List α) (l₂ : List β) :
    zipWithAll f (l₁.map g) (l₂.map h) = zipWithAll (fun a b => f (g <$> a) (h <$> b)) l₁ l₂ := by
  induction l₁ generalizing l₂
  · cases l₂
    · simp
    · simp
  · cases l₂
    · simp
    · simp [List.map, zipWithAll]
      apply ih

/- ACTUAL PROOF OF List.zipWithAll_map -/

example {μ} (f : Option γ → Option δ → μ) (g : α → γ) (h : β → δ) (l₁ : List α) (l₂ : List β) :
    zipWithAll f (l₁.map g) (l₂.map h) = zipWithAll (fun a b => f (g <$> a) (h <$> b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all