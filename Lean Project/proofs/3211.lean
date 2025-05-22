import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by
  rw [Nat.mul_div_cancel _ H]

/- ACTUAL PROOF OF Nat.mul_div_left -/

example (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by
  rw [Nat.mul_comm, mul_div_right _ H]