import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (m n : Nat) : (m * n) % n = 0 := by
  rw [mul_comm]
  exact mod_self n m

/- ACTUAL PROOF OF Nat.mul_mod_left -/

example (m n : Nat) : (m * n) % n = 0 := by
  rw [Nat.mul_comm, mul_mod_right]