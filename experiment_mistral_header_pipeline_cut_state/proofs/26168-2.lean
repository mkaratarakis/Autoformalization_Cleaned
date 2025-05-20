import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example (a b : Nat) : max a b = max b a := by
  by_cases h : a ≤ b
  · by_cases h' : b ≤ a
    · have : a = b := le_antisymm h h'
      simp [this]
    · simp [h, max]
  · by_cases h' : b ≤ a
    · simp [h', max]
    · exfalso
      exact not_le_of_gt h' h

/- ACTUAL PROOF OF Nat.max_comm -/

example (a b : Nat) : max a b = max b a := by
  simp only [Nat.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Nat.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Nat.le_total ..