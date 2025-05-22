import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example : a ∧ b ∧ c ↔ b ∧ c ∧ a := by
  rw [and_left_comm, @and_comm a c]