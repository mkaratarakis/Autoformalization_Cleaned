import Init.Core
import Init.SimpLemmas




example : a ∨ (a ∨ b) ↔ a ∨ b := by
  rw [← or_assoc]
  rw [or_idem]
  rfl

/- ACTUAL PROOF OF or_self_left -/

example : a ∨ (a ∨ b) ↔ a ∨ b := by
  rw [←propext or_assoc, or_self]