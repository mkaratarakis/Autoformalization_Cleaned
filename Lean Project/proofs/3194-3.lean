import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = (a - b) / b + 1 := by
unfold div
rw [dif_pos h₁]
rw [Nat.sub_add_cancel h₂]

/- ACTUAL PROOF OF Nat.div_eq_sub_div -/

example (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = (a - b) / b + 1 := by
 rw [div_eq a, if_pos]; constructor <;> assumption