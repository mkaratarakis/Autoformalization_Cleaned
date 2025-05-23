import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a b : Int) : min a b = min b a := by
  by_cases h₁ : a ≤ b
  · by_cases h₂ : b ≤ a
    · have h₃ : a = b := Int.le_antisymm h₁ h₂
      rw [h₃]
    · rw [min, h₁, if_neg h₂, min, if_pos h₂]
      rfl
  · rw [min, if_neg h₁, min, if_pos h₁]
    rfl

/- ACTUAL PROOF OF Int.min_comm -/

example (a b : Int) : min a b = min b a := by
  simp [Int.min_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Int.le_antisymm h₁ h₂
  · cases not_or_intro h₁ h₂ <| Int.le_total ..