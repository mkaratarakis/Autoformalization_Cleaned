import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (x : Nat) {z : Nat} (H : 0 < z) : (x + z) / z = (x / z) + 1 := by
  have h1 : x + z = z + x := by rfl
  rw [h1]
  apply Nat.div_add_one_of_lt
  exact Nat.le_add_right _ _
  exact H

/- ACTUAL PROOF OF Nat.add_div_right -/

example (x : Nat) {z : Nat} (H : 0 < z) : (x + z) / z = (x / z) + 1 := by
  rw [div_eq_sub_div H (Nat.le_add_left _ _), Nat.add_sub_cancel]