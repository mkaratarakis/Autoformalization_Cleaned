import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by
  rw [mul_comm m n]
  rw [Nat.div_eq_of_lt (Nat.mul_pos_of_pos_left n H)]

/- ACTUAL PROOF OF Nat.mul_div_left -/

example (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by
  rw [Nat.mul_comm, mul_div_right _ H]