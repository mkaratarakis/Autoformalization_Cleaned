import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat



example (x : Nat) {z : Nat} (H : 0 < z) : (z + x) / z = (x / z) + 1 := by
  rw [Nat.add_comm, add_div_right x H]