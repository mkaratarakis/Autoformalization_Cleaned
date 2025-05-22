import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ a ∧ c := by
  have h1 : ((a ∧ b) ∧ a) ∧ c ↔ (a ∧ a) ∧ (b ∧ c) := by
    apply and_congr_left
    apply and_congr
    apply and_congr_right
    apply and_congr_left
  rw [and_assoc]
  rw [and_assoc]
  rw [and_assoc]
  rw [and_assoc]
  rw [and_congr_left h1]
  rw [and_idempotent]

/- ACTUAL PROOF OF and_and_left -/

example : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ a ∧ c := by
  rw [and_and_and_comm, and_self]