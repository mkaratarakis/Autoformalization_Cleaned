import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : a ∨ b ∨ c ↔ (a ∨ b) ∨ a ∨ c := by
  apply Iff.intro
  · intro h
    cases h
    · left
      exact Or.inl (Or.inl h)
    · left
      exact Or.inl (Or.inr h)
    · right
      exact Or.inr (Or.inl h)
  · intro h
    cases h
    · left
      apply Or.inl
      · exact h
      · exact Or.inl h
    · left
      exact Or.inr h
    · right
      exact Or.inr h

/- ACTUAL PROOF OF or_or_distrib_left -/

example : a ∨ b ∨ c ↔ (a ∨ b) ∨ a ∨ c := by
  rw [or_or_or_comm, or_self]