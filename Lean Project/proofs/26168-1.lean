import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example (a b : Nat) : max a b = max b a := by
  by_cases h₁ : a ≤ b
  · by_cases h₂ : b ≤ a
    · exact le_antisymm h₁ h₂
    · simp [max, h₁, h₂]
  · by_cases h₂ : b ≤ a
    · simp [max, h₁, h₂]
    · exfalso
      exact not_le_of_gt h₁ h₂

/- ACTUAL PROOF OF Nat.max_comm -/

example (a b : Nat) : max a b = max b a := by
  simp only [Nat.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Nat.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Nat.le_total ..