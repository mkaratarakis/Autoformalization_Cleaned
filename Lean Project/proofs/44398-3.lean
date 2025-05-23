import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a b : Int) : max a b = max b a := by
  unfold max
  by_cases h : a ≤ b
  · rw [dif_pos h]
    rw [dif_pos (le_of_not_le (mt le_of_eq (not_congr (not_le.mpr h))))]
    exact Eq.refl b
  · rw [dif_neg h]
    rw [dif_neg (not_le.mpr h)]
    exact Eq.refl a

/- ACTUAL PROOF OF Int.max_comm -/

example (a b : Int) : max a b = max b a := by
  simp only [Int.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Int.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Int.le_total ..