import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (x : Nat) {z : Nat} (H : 0 < z) : (x + z) / z = (x / z) + 1 := by
  rw [add_comm]
  have h1 : z ≤ x + z := Nat.le_add_right _ _
  have h2 : 0 < x + z := Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.add_lt_add_right H _))
  have h3 : x + z - z = x := by simp
  rw [Nat.div_eq_of_lt h2]
  rw [h3]
  simp

/- ACTUAL PROOF OF Nat.add_div_right -/

example (x : Nat) {z : Nat} (H : 0 < z) : (x + z) / z = (x / z) + 1 := by
  rw [div_eq_sub_div H (Nat.le_add_left _ _), Nat.add_sub_cancel]