import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example (a b : Int) : min a b = min b a := by
  simp [Int.min_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Int.le_antisymm h₁ h₂
  · cases not_or_intro h₁ h₂ <| Int.le_total ..