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
      exact hac.right.left
    · intro hb
      have hbc : b ∧ c := And.intro hb hc
      rw [← h] at hbc
      exact hbc.right.left
  · intro h
    apply Iff.intro
    · intro hac
      apply And.intro
      · apply h hac.right
        exact hac.left
      · exact hac.right
    · intro hbc
      apply And.intro
      · apply h hbc.right
        exact hbc.left
      · exact hbc.right

/- ACTUAL PROOF OF and_congr_left_iff -/

example : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  rw [@and_comm _ c, @and_comm _ c, ← and_congr_right_iff]