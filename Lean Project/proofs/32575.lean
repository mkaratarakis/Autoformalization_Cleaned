import Init.Core
import Init.SimpLemmas




example : (a ∨ b) ∨ b ↔ a ∨ b := by
  apply Iff.intro
  · intro h
    cases h
    case inl h =>
      cases h
      case inl h => exact Or.inl h
      case inr h => exact Or.inr h
    case inr h => exact Or.inr h
  · intro h
    cases h
    case inl h => exact Or.inl (Or.inl h)
    case inr h => exact Or.inr h

/- ACTUAL PROOF OF or_self_right -/

example : (a ∨ b) ∨ b ↔ a ∨ b := by
  rw [ propext or_assoc, or_self]