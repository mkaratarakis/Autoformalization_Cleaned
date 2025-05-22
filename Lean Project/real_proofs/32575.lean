import Init.Core
import Init.SimpLemmas





example : (a ∨ b) ∨ b ↔ a ∨ b := by
  rw [ propext or_assoc, or_self]