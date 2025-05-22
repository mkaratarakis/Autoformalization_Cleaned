import Init.Core
import Init.SimpLemmas




example : a ∧ (a ∧ b) ↔ a ∧ b := by
  rw [←and_assoc]
  rw [and_self]

/- ACTUAL PROOF OF and_self_left -/

example : a ∧ (a ∧ b) ↔ a ∧ b := by
  rw [←propext and_assoc, and_self]