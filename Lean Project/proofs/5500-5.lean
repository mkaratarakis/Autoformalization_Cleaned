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
      exact Or.inl (Or.inr h)
    · right
      exact h
  · intro h
    apply Or.elim h
    · intro h
      exact Or.inl (Or.inl h)
    · intro h
      apply Or.elim h
      · intro h
        exact Or.inl (Or.inr h)
      · intro h
        exact Or.inr h

/- ACTUAL PROOF OF or_or_distrib_right -/

example : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b ∨ c := by
  rw [or_or_or_comm, or_self]