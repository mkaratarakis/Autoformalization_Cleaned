import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b := by
  apply Iff.intro
  · intro h
    cases h with
    | inl h => exact Or.inl (Or.inl h)
    | inr h =>
      cases h with
      | inl h => exact Or.inl (Or.inr h)
      | inr h => exact Or.inr h
  · intro h
    cases h with
    | inl h =>
      cases h with
      | inl h => exact Or.inl (Or.inl h)
      | inr h => exact Or.inl (Or.inr h)
    | inr h => exact Or.inr h

/- ACTUAL PROOF OF or_right_comm -/

example : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b := by
  rw [or_assoc, or_assoc, @or_comm b]