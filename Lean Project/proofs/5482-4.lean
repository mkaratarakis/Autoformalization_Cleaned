import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : a ∨ b ∨ c ↔ (a ∨ b) ∨ a ∨ c := by
  apply Iff.intro
  · intro h
    cases h
    · left
      exact Or.inl (Or.inl h)
    · cases h
      · left
        exact Or.inl (Or.inr h)
      · right
        exact Or.inl h
  · intro h
    cases h
    · left
      exact h
    · cases h
      · left
        exact Or.inr h
      · right
        exact h

/- ACTUAL PROOF OF or_or_distrib_left -/

example : a ∨ b ∨ c ↔ (a ∨ b) ∨ a ∨ c := by
  rw [or_or_or_comm, or_self]