import Init.Core
import Init.SimpLemmas




example : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  apply Iff.intro
  · intro h
    intro hc
    apply Iff.intro
    · intro ha
      have hac : a ∧ c := And.intro ha hc
      rw [h] at hac
      exact hac.right
    · intro hb
      have hbc : b ∧ c := And.intro hb hc
      rw [← h] at hbc
      exact hbc.left
  · intro h
    apply Iff.intro
    · intro hac
      rw [h hac.right]
      exact hac.left
    · intro hbc
      rw [← h hbc.right]
      exact hbc.left

/- ACTUAL PROOF OF and_congr_left_iff -/

example : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  rw [@and_comm _ c, @and_comm _ c, ← and_congr_right_iff]