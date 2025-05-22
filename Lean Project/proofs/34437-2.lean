import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {R : α → α → Prop} (s : ∀ {x y}, R x y → R y x) {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ l₂) ↔ Pairwise R (l₂ ++ l₁) := by
  constructor
  · intro h
    apply Pairwise.append
    · exact Pairwise.subset (Pairwise.append h) (Sublist.append_right _ _)
    · intro x hx y hy
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      apply s
      apply h
      · exact List.get?_eq_of_lt ⟨i, nat.lt_of_succ_lt_succ (List.length_le_of_get? _ hx)⟩
      · exact List.get?_eq_of_lt ⟨j, nat.lt_of_succ_lt_succ (List.length_le_of_get? _ hy)⟩
  · intro h
    apply Pairwise.append
    · exact Pairwise.subset (Pairwise.append h) (Sublist.append_right _ _)
    · intro x hx y hy
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      apply s
      apply h
      · exact List.get?_eq_of_lt ⟨i, nat.lt_of_succ_lt_succ (List.length_le_of_get? _ hx)⟩
      · exact List.get?_eq_of_lt ⟨j, nat.lt_of_succ_lt_succ (List.length_le_of_get? _ hy)⟩

/- ACTUAL PROOF OF List.pairwise_append_comm -/

example {R : α → α → Prop} (s : ∀ {x y}, R x y → R y x) {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ l₂) ↔ Pairwise R (l₂ ++ l₁) := by
  have (l₁ l₂ : List α) (H : ∀ x : α, x ∈ l₁ → ∀ y : α, y ∈ l₂ → R x y)
    (x : α) (xm : x ∈ l₂) (y : α) (ym : y ∈ l₁) : R x y := s (H y ym x xm)
  simp only [pairwise_append, and_left_comm]; rw [Iff.intro (this l₁ l₂) (this l₂ l₁)]