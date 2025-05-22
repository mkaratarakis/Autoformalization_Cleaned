import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : a ∨ b ∨ c ↔ b ∨ c ∨ a := by
  apply Iff.intro
  · intro h
    cases h with
    | inl h => exact Or.inr (Or.inr h)
    | inr h =>
      cases h with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (Or.inl h)
  · intro h
    cases h with
    | inl h => exact Or.inr (Or.inl h)
    | inr h =>
      cases h with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (Or.inr h)

/- ACTUAL PROOF OF or_rotate -/

example : a ∨ b ∨ c ↔ b ∨ c ∨ a := by
  simp only [or_left_comm, Or.comm]