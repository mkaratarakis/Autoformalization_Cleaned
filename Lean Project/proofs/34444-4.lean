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
      exact ⟨h, fun a => False.elim (not_mem_nil _ _), h⟩
    · rintro ⟨h₁, h₂, h₃⟩
      exact h₁
  | cons hd tl ih =>
    simp [Pairwise, ih]
    constructor
    · intro h
      exact
        ⟨h.left, ⟨h.right.left, ⟨h.right.right.left, fun a => h.right.right.right a⟩⟩,
          fun a => by
            apply Or.elim (mem_append.mp a)
            · intro h
              exact h.right.right.right _ h
            · intro h
              exact h.right.right.right _ h⟩
    · rintro ⟨h₁, ⟨h₂, ⟨h₃, h₄⟩, h₅⟩, h₆⟩
      exact ⟨⟨h₁, ⟨h₂, ⟨h₃, fun a => by
            apply Or.elim (mem_append.mp a)
            · intro h
              exact h₄ _ h
            · intro h
              exact h₆ _ h⟩⟩⟩⟩

/- ACTUAL PROOF OF List.pairwise_append -/

example {l₁ l₂ : List α} :
    (l₁ ++ l₂).Pairwise R ↔ l₁.Pairwise R ∧ l₂.Pairwise R ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, R a b := by
  induction l₁ <;> simp [*, or_imp, forall_and, and_assoc, and_left_comm]