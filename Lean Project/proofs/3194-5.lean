import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = (a - b) / b + 1 := by
  unfold Nat.div
  simp [Nat.sub, Nat.add, Nat.mul, Nat.le, Nat.lt]
  rw [Nat.sub_add_cancel h₂]
  exact h₁

/- ACTUAL PROOF OF Nat.div_eq_sub_div -/

example (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = (a - b) / b + 1 := by
 rw [div_eq a, if_pos]; constructor <;> assumption