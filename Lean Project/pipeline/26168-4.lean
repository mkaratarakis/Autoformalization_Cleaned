import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example (a b : Nat) : max a b = max b a := by
  by_cases h₁ : a ≤ b
  · by_cases h₂ : b ≤ a
    · have : a = b := Nat.le_antisymm h₁ h₂
      simp [Nat.max_def, h₁, h₂, this]
    · simp [Nat.max_def, h₁, h₂]
  · by_cases h₂ : b ≤ a
    · simp [Nat.max_def, h₁, h₂]
    · exfalso
      exact Nat.not_le_of_lt (Nat.lt_of_not_ge h₂) h₁

/- ACTUAL PROOF OF Nat.max_comm -/

example (a b : Nat) : max a b = max b a := by
  simp only [Nat.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Nat.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Nat.le_total ..