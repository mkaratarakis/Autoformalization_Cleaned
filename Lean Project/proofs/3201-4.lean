import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (m n : Nat) : (m * n) % n = 0 := by
  rw [Nat.mul_comm]
  exact Nat.mod_eq_of_lt (Nat.mul_lt_mul_left (n:=n+1) (Nat.zero_lt_succ n))

/- ACTUAL PROOF OF Nat.mul_mod_left -/

example (m n : Nat) : (m * n) % n = 0 := by
  rw [Nat.mul_comm, mul_mod_right]