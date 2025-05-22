import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b ∨ c := by
  constructor
  · intro h
    cases h
    · left
      exact Or.inl h
    · right
      left
      exact Or.inr h
    · right
      right
      exact h
  · intro h
    cases h
    · left
      left
      exact h
    · right
      cases h
      · left
        right
        exact h
      · right
        exact h

/- ACTUAL PROOF OF or_or_distrib_right -/

example : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b ∨ c := by
  rw [or_or_or_comm, or_self]