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
      exact h₂
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
      exact h₂

/- ACTUAL PROOF OF or_or_or_comm -/

example : (a ∨ b) ∨ c ∨ d ↔ (a ∨ c) ∨ b ∨ d := by
  rw [← or_assoc, @or_right_comm a, or_assoc]