import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example : a ∨ b ∨ c ↔ (a ∨ b) ∨ a ∨ c := by
  rw [or_or_or_comm, or_self]