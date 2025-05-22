import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) := by
  rw [@and_comm (a ∨ b), and_or_left, @and_comm c, @and_comm c]