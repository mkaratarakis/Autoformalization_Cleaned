import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat



example (x : Nat) {z : Nat} (H : 0 < z) : (x + z) / z = (x / z) + 1 := by
  rw [div_eq_sub_div H (Nat.le_add_left _ _), Nat.add_sub_cancel]