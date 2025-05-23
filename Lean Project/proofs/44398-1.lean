import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a b : Int) : max a b = max b a := by
  unfold max
  split
  · intro h
    have h1 : b ≤ a := le_of_eq h
    rw [dif_pos h1]
    rw [dif_pos h]
    exact h.symm
  · intro h
    rw [dif_neg h]
    rw [dif_neg (not_le.mpr h)]
    exact Eq.refl a

/- ACTUAL PROOF OF Int.max_comm -/

example (a b : Int) : max a b = max b a := by
  simp only [Int.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Int.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Int.le_total ..