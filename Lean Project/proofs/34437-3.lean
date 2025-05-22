import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {R : α → α → Prop} (s : ∀ {x y}, R x y → R y x) {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ l₂) ↔ Pairwise R (l₂ ++ l₁) := by
  constructor
  · intro h
    apply Pairwise.append_iff.mpr
    apply And.intro
    · exact Pairwise.subset h (Sublist.append_left l₁ l₂)
    · exact fun x hx y hy => s (h (List.mem_append.mp (Or.inr hx)) (List.mem_append.mp (Or.inl hy)))
  · intro h
    apply Pairwise.append_iff.mpr
    apply And.intro
    · exact Pairwise.subset h (Sublist.append_left l₂ l₁)
    · exact fun x hx y hy => s (h (List.mem_append.mp (Or.inr hx)) (List.mem_append.mp (Or.inl hy)))

/- ACTUAL PROOF OF List.pairwise_append_comm -/

example {R : α → α → Prop} (s : ∀ {x y}, R x y → R y x) {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ l₂) ↔ Pairwise R (l₂ ++ l₁) := by
  have (l₁ l₂ : List α) (H : ∀ x : α, x ∈ l₁ → ∀ y : α, y ∈ l₂ → R x y)
    (x : α) (xm : x ∈ l₂) (y : α) (ym : y ∈ l₁) : R x y := s (H y ym x xm)
  simp only [pairwise_append, and_left_comm]; rw [Iff.intro (this l₁ l₂) (this l₂ l₁)]