import Init.Core
import Init.SimpLemmas




example : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  apply Iff.intro
  · intro h
    intro hc
    apply propext
    apply Iff.intro
    · intro ha
      rw [← h]
      exact And.intro ha hc
    · intro hb
      rw [h]
      exact hb.elim
  · intro h
    apply propext
    apply Iff.intro
    · intro hac
      apply And.intro
      · rw [← h hac.2]
        exact hac.1
      · exact hac.2
    · intro hbc
      apply And.intro
      · rw [h hbc.2]
        exact hbc.1
      · exact hbc.2

/- ACTUAL PROOF OF and_congr_left_iff -/

example : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  rw [@and_comm _ c, @and_comm _ c, ← and_congr_right_iff]