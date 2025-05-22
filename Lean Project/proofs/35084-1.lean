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
    simp only [nil_append, Sublist.nil]
    constructor
    · intro h
      exists []
      constructor <;> assumption
    · rintro ⟨r₁, r₂, rfl, h₁, h₂⟩
      exact h₂
  | cons a l₁ ih =>
    simp only [cons_append, Sublist.cons]
    constructor
    · intro h
      rcases h with ⟨r₁, r₂, h₁, h₂⟩
      rcases h₂ with ⟨r₁', r₂', rfl, h₁', h₂'⟩
      exists (r₁ ++ r₁')
      constructor <;> assumption
    · rintro ⟨r₁, r₂, rfl, h₁, h₂⟩
      rcases h₁ with ⟨r₁', r₂', rfl, h₁', h₂'⟩
      exists (r₁ ++ r₁')
      constructor <;> assumption

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