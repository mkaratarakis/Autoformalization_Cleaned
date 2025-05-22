import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (x y : Nat) {z : Nat} (H : 0 < z) : (x + y * z) / z = x / z + y := by
  rw [mul_comm]
  rw [Nat.add_mul_div_right H]
  rfl

/- ACTUAL PROOF OF Nat.add_mul_div_right -/

example (x y : Nat) {z : Nat} (H : 0 < z) : (x + y * z) / z = x / z + y := by
  rw [Nat.mul_comm, add_mul_div_left _ _ H]