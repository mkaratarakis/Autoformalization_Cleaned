import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ a ∧ c := by
  rw [and_and_and_comm, and_self]