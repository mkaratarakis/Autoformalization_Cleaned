import Init.Core
import Init.SimpLemmas




example : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  apply Iff.intro
  · intro h
    apply imp_iff_not_or_imp
    · rintro ⟨⟩
    · intro hc
      rw [h]
  · intro h
    rw [imp_iff_not_or] at h
    cases h
    · rintro ⟨⟩
    · rw [h]

/- ACTUAL PROOF OF and_congr_left_iff -/

example : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  rw [@and_comm _ c, @and_comm _ c, ← and_congr_right_iff]