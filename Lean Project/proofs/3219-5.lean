import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (h₀ : a < b) : a / b = 0 := by
  rw [div_def]
  split_ifs with h₁
  · exact h₀.not_le h₁.right
  · rfl

/- ACTUAL PROOF OF Nat.div_eq_of_lt -/

example (h₀ : a < b) : a / b = 0 := by
  rw [div_eq a, if_neg]
  intro h₁
  apply Nat.not_le_of_gt h₀ h₁.right