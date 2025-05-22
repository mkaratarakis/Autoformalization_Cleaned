import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat



example (x y z : Nat) : (x + y * z) % z = x % z := by
  rw [Nat.mul_comm, add_mul_mod_self_left]