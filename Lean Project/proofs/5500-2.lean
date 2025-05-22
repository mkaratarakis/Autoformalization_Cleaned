import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b ∨ c := by
  constructor
  · intro h
    cases h
    · left
      exact Or.inl (Or.inl h)
    · left
      exact Or.inr (Or.inl h)
    · right
      exact Or.inr h
  · intro h
    cases h
    · left
      exact Or.inl h
    · cases h
      · left
        exact Or.inr h
      · right
        exact h

/- ACTUAL PROOF OF or_or_distrib_right -/

example : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b ∨ c := by
  rw [or_or_or_comm, or_self]