import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example : a ∨ b ∨ c ↔ b ∨ c ∨ a := by
  simp only [or_left_comm, Or.comm]