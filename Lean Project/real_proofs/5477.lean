import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b := by
  rw [or_assoc, or_assoc, @or_comm b]