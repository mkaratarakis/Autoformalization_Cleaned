import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (m : Nat) {n : Nat} (H : 0 < n) : n * m / n = m := by
  rw [mul_comm]
  rw [Nat.div_mul_cancel _ H]

/- ACTUAL PROOF OF Nat.mul_div_cancel_left -/

example (m : Nat) {n : Nat} (H : 0 < n) : n * m / n = m := by
  rw [Nat.mul_comm, Nat.mul_div_cancel _ H]