import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open IsPrefix
open Nat
variable [BEq α]
variable [BEq α]

example (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    l₁.filter p <+: l₂.filter p := by

  have h₁ : ∃ xs, l₂ = l₁ ++ xs := by
    exact h
  rcases h₁ with ⟨xs, rfl⟩
  rw [filter_append]
  apply isPrefix.append_right

lemma filter_append {α} (p : α → Bool) (l₁ l₂ : List α) :
  (l₁ ++ l₂).filter p = (l₁.filter p) ++ (l₂.filter p) := by
    induction l₁
    case nil =>
      simp [filter]
      simp [filter]
    case cons =>
      simp [filter, ih]
      simp [filter, ih]

lemma isPrefix.append_right {α} [BEq α] {p₁ p₂ : List α} :
  p₁ <+: p₁ ++ p₂ := by
    use p₂
    rfl

lemma isPrefix.trans {α} [BEq α] ⦃p₁ p₂ p₃ : List α⦄
  (h₁ : p₁ <+: p₂) (h₂ : p₂ <+: p₃) : p₁ <+: p₃ := by
    rcases h₁ with ⟨l₁, h₁⟩
    rcases h₂ with ⟨l₂, h₂⟩
    have h₃ : p₂ = p₁ ++ l₁ := by
      rw [h₁]
    have h₄ : p₃ = p₂ ++ l₂ := by
      rw [h₂]
    have h₅ : p₃ = (p₁ ++ l₁) ++ l₂ := by
      rw [h₃, h₄]
    have h₆ : p₃ = p₁ ++ (l₁ ++ l₂) := by
      rw [List.append_assoc] at h₅
      exact h₅
    use l₁ ++ l₂
    exact h₆

/- ACTUAL PROOF OF List.IsPrefix.filter -/

example (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    l₁.filter p <+: l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]; apply prefix_append