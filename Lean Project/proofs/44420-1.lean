import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a b : Int) : min a b = min b a := by
  by_cases h₁ : a ≤ b
  · by_cases h₂ : b ≤ a
    · have h₃ : a = b := le_antisymm h₁ h₂
      rw [h₃]
      rfl
    · have h₄ : ¬ b ≤ a := h₂
      rw [min_def, h₁, if_neg h₄, min_def, if_neg h₄, h₄]
      rfl
  · by_cases h₂ : b ≤ a
    · rw [if_neg h₁, min_def, h₂, if_neg h₁]
      rfl
    · have h₃ : ¬ b ≤ a := h₂
      exfalso
      apply not_le_of_gt
      apply lt_of_not_ge
      apply h₁
      apply le_of_not_gt
      apply h₃
  rfl

/- ACTUAL PROOF OF Int.min_comm -/

example (a b : Int) : min a b = min b a := by
  simp [Int.min_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Int.le_antisymm h₁ h₂
  · cases not_or_intro h₁ h₂ <| Int.le_total ..