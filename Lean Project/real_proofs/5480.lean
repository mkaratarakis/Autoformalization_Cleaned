import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by
  rw [← and_assoc, @and_right_comm a, and_assoc]