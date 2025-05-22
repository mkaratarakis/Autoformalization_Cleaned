import Init.Core
import Init.SimpLemmas




example : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  apply Iff.intro
  · intro h
    intro hc
    apply Iff.intro
    · intro ha
      rw [← h]
      exact And.intro ha hc
    · intro hb
      rw [h]
      exact hb
  · intro h
    apply Iff.intro
    · intro hac
      rw [h hac.2]
      exact hac.1
    · intro hbc
      rw [← h hbc.2]
      exact hbc.1

/- ACTUAL PROOF OF and_congr_left_iff -/

example : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  rw [@and_comm _ c, @and_comm _ c, ← and_congr_right_iff]