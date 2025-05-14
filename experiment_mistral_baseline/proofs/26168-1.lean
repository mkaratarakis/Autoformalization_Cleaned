import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example (a b : Nat) : max a b = max b a := by
  by_cases h₁ : a ≤ b
  · by_cases h₂ : b ≤ a
    · have h₃ : a = b := le_antisymm h₁ h₂
      rw [h₃]
      rfl
    · rw [if_pos h₁]
      rw [if_neg h₂]
      rfl
  · by_cases h₂ : b ≤ a
    · rw [if_neg h₁]
      rw [if_pos h₂]
      rfl
    · exfalso
      exact not_le_of_lt (lt_of_le_of_lt (le_of_not_le h₁) (lt_of_not_le h₂))

/- ACTUAL PROOF OF Nat.max_comm -/

example (a b : Nat) : max a b = max b a := by
  simp only [Nat.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Nat.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Nat.le_total ..