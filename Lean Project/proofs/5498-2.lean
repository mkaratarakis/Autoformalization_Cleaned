import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ a ∧ c := by
  have h1 : ((a ∧ b) ∧ a) ∧ c ↔ (a ∧ a) ∧ (b ∧ c) := by
    rw [and_assoc, and_assoc, and_assoc]
  rw [and_assoc]
  rw [and_assoc]
  rw [and_assoc]
  rw [and_assoc]
  rw [h1]
  rw [and_idempotent]

/- ACTUAL PROOF OF and_and_left -/

example : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ a ∧ c := by
  rw [and_and_and_comm, and_self]