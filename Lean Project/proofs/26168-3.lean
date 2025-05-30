import Init.ByCases
import Init.Data.Nat.MinMax

open Nat


example (a b : Nat) : max a b = max b a := by
  by_cases h₁ : a ≤ b
  · by_cases h₂ : b ≤ a
    · have : a = b := Nat.le_antisymm h₁ h₂
      simp [max, this]
    · rw [max_eq_right h₁]
      rw [max_of_lt (mt h₂ h₁)]
  · by_cases h₂ : b ≤ a
    · rw [max_eq_right h₂]
      rw [max_of_lt h₁]
    · exfalso
      exact (not_lt_of_ge h₁) h₂

/- ACTUAL PROOF OF Nat.max_comm -/

example (a b : Nat) : max a b = max b a := by
  simp only [Nat.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Nat.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Nat.le_total ..