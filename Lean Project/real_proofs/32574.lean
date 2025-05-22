import Init.Core
import Init.SimpLemmas





example : a ∧ (a ∧ b) ↔ a ∧ b := by
  rw [←propext and_assoc, and_self]