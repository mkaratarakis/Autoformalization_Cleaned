import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a b : Int) : max a b = max b a := by
  unfold max
  by_cases h : a ≤ b
  · simp [h]
    simp [le_of_not_le fun h' => h h']
  · simp [h]
    simp [not_le.mpr h]

/- ACTUAL PROOF OF Int.max_comm -/

example (a b : Int) : max a b = max b a := by
  simp only [Int.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Int.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Int.le_total ..