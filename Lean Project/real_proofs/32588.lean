import Init.Core
import Init.SimpLemmas





example : (a ∨ b ↔ b) ↔ (a → b) := by
  rw [or_comm, or_iff_left_iff_imp]