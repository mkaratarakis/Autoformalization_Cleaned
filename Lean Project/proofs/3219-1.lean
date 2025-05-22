import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (h₀ : a < b) : a / b = 0 := by
  rw [Nat.div_eq_zero_of_lt]
  exact h₀

/- ACTUAL PROOF OF Nat.div_eq_of_lt -/

example (h₀ : a < b) : a / b = 0 := by
  rw [div_eq a, if_neg]
  intro h₁
  apply Nat.not_le_of_gt h₀ h₁.right