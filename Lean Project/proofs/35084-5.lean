import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {l₁ l₂ : List α} :
    l₁ ++ l₂ <+ r ↔ ∃ r₁ r₂, r = r₁ ++ r₂ ∧ l₁ <+ r₁ ∧ l₂ <+ r₂ := by
  induction l₁ with
  | nil =>
    simp only [nil_append, Sublist.nil, and_true, exists_prop]
    constructor
    · intro h
      exists [], r
      constructor
      · rfl
      · exact Sublist.refl _
      · exact h
    · rintro ⟨r₁, r₂, rfl, _, h₂⟩
      exact h₂
  | cons a l₁ ih =>
    simp only [cons_append, Sublist.cons]
    constructor
    · intro h
      rcases h with ⟨r₁, r₂, rfl, h₂⟩
      rcases ih h₂ with ⟨r₁', r₂', rfl, h₁', h₂'⟩
      exists a :: r₁', r₂'
      constructor
      · rfl
      · exact Sublist.cons _ r₁' h₁'
      · exact h₂'
    · rintro ⟨r₁, r₂, rfl, h₁, h₂⟩
      rcases h₁ with ⟨h₁', r₁', rfl, h₁'', h₂'⟩
      exists r₁', a :: r₂
      constructor
      · rfl
      · exact Sublist.cons _ _ h₂'
      · exact ih.mpr ⟨r₁', a :: r₂, rfl, h₁'', h₂⟩

/- ACTUAL PROOF OF List.append_sublist_iff -/

example {l₁ l₂ : List α} :
    l₁ ++ l₂ <+ r ↔ ∃ r₁ r₂, r = r₁ ++ r₂ ∧ l₁ <+ r₁ ∧ l₂ <+ r₂ := by
  induction l₁ generalizing r with
  | nil =>
    constructor
    · intro w
      refine ⟨[], r, by simp_all⟩
    · rintro ⟨r₁, r₂, rfl, -, w₂⟩
      simp only [nil_append]
      exact sublist_append_of_sublist_right w₂
  | cons a l₁ ih =>
    constructor
    · rw [cons_append, cons_sublist_iff]
      rintro ⟨r₁, r₂, rfl, h₁, h₂⟩
      obtain ⟨s₁, s₂, rfl, t₁, t₂⟩ := ih.1 h₂
      refine ⟨r₁ ++ s₁, s₂, by simp, ?_, t₂⟩
      rw [← singleton_append]
      exact Sublist.append (by simpa) t₁
    · rintro ⟨r₁, r₂, rfl, h₁, h₂⟩
      exact Sublist.append h₁ h₂