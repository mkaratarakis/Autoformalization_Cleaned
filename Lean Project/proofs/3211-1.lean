import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by
  rw [mul_comm]
  rw [Nat.div_eq_of_lt (mul_pos_iff_and_and.2 ⟨H, zero_le _⟩)]

/- ACTUAL PROOF OF Nat.mul_div_left -/

example (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by
  rw [Nat.mul_comm, mul_div_right _ H]