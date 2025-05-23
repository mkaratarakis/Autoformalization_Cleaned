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
    · calc
        min a b = a := by rw [if_pos h₁]
        _ = min b a := by rw [if_neg h₂]
  · calc
        min a b = b := by rw [if_neg h₁]
        _ = min b a := by rw [if_pos (not_le_of_gt h₁).elim]

/- ACTUAL PROOF OF Int.min_comm -/

example (a b : Int) : min a b = min b a := by
  simp [Int.min_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Int.le_antisymm h₁ h₂
  · cases not_or_intro h₁ h₂ <| Int.le_total ..