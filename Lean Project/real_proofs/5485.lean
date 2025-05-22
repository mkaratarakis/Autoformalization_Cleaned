import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example : (a ∨ b) ∨ c ∨ d ↔ (a ∨ c) ∨ b ∨ d := by
  rw [← or_assoc, @or_right_comm a, or_assoc]