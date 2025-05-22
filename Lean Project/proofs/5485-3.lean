import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : (a ∨ b) ∨ c ∨ d ↔ (a ∨ c) ∨ b ∨ d := by
  apply Iff.intro
  · intro h
    apply Or.elim h
    · intro h₁
      apply Or.elim h₁
      · intro h₁₁
        apply Or.inl
        apply Or.inl
        exact h₁₁
      · intro h₁₂
        apply Or.inl
        apply Or.inr
        apply Or.inl
        exact h₁₂
    · intro h₂
      apply Or.elim h₂
      · intro h₂₁
        apply Or.inl
        apply Or.inr
        apply Or.inl
        exact h₂₁
      · intro h₂₂
        apply Or.inr
        exact h₂₂
  · intro h
    apply Or.elim h
    · intro h₁
      apply Or.elim h₁
      · intro h₁₁
        apply Or.inl
        apply Or.inl
        exact h₁₁
      · intro h₁₂
        apply Or.inl
        apply Or.inr
        exact h₁₂
    · intro h₂
      apply Or.elim h₂
      · intro h₂₁
        apply Or.inr
        apply Or.inl
        exact h₂₁
      · intro h₂₂
        apply Or.inr
        exact h₂₂

/- ACTUAL PROOF OF or_or_or_comm -/

example : (a ∨ b) ∨ c ∨ d ↔ (a ∨ c) ∨ b ∨ d := by
  rw [← or_assoc, @or_right_comm a, or_assoc]