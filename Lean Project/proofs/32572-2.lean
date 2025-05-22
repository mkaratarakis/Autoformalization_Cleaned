import Init.Core
import Init.SimpLemmas




example : a ∨ (a ∨ b) ↔ a ∨ b := by
  rw [← or_assoc]
  apply Iff.intro
  . intro h
    cases h with
    | inl h => exact Or.inl h
    | inr h => exact h
  . intro h
    cases h with
    | inl h => exact Or.inl (Or.inl h)
    | inr h => exact Or.inr h

/- ACTUAL PROOF OF or_self_left -/

example : a ∨ (a ∨ b) ↔ a ∨ b := by
  rw [←propext or_assoc, or_self]