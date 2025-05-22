import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) := by
  rw [@or_comm (a ∧ b), or_and_left, @or_comm c, @or_comm c]