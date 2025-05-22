import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat



example (m n : Nat) : (m * n) % n = 0 := by
  rw [Nat.mul_comm, mul_mod_right]