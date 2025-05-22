import Init.Core
import Init.SimpLemmas





example : a ∨ (a ∨ b) ↔ a ∨ b := by
  rw [←propext or_assoc, or_self]