import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {l₁ l₂ : List α} :
    (l₁ ++ l₂).Pairwise R ↔ l₁.Pairwise R ∧ l₂.Pairwise R ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, R a b := by
  induction l₁ with
  | nil =>
    simp [Pairwise]
    constructor
    · intro h
      exact ⟨h, fun a => False.elim (not_mem_nil _ _)⟩
    · rintro ⟨h₁, h₂⟩
      exact h₁
  | cons hd tl ih =>
    simp [Pairwise, ih]
    constructor
    · intro h
      exact ⟨h.1, h.2.1, fun a => h.2.2 a⟩
    · rintro ⟨h₁, h₂, h₃⟩
      exact ⟨h₁, ⟨h₂, h₃⟩⟩

/- ACTUAL PROOF OF List.pairwise_append -/

example {l₁ l₂ : List α} :
    (l₁ ++ l₂).Pairwise R ↔ l₁.Pairwise R ∧ l₂.Pairwise R ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, R a b := by
  induction l₁ <;> simp [*, or_imp, forall_and, and_assoc, and_left_comm]