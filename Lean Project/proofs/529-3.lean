import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat

example (l₁ l₂ : List α) :
    (l₁ ++ l₂).eraseP p = if l₁.any p then l₁.eraseP p ++ l₂ else l₁ ++ l₂.eraseP p := by
  by_cases h : l₁.any p
  · have hp : ∃ x, x ∈ l₁ ∧ p x := by
      simpa only [List.any] using h
    rcases hp with ⟨x, hx, hp⟩
    rw [eraseP_append_of_mem _ hx hp]
    rfl
  · push_neg at h
    apply eraseP_append_of_not_mem
    exact h

/- ACTUAL PROOF OF List.eraseP_append -/

example (l₁ l₂ : List α) :
    (l₁ ++ l₂).eraseP p = if l₁.any p then l₁.eraseP p ++ l₂ else l₁ ++ l₂.eraseP p := by
  split <;> rename_i h
  · simp only [any_eq_true] at h
    obtain ⟨x, m, h⟩ := h
    rw [eraseP_append_left h _ m]
  · simp only [any_eq_true] at h
    rw [eraseP_append_right _]
    simp_all