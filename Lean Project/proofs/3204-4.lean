import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat

example (x y z : Nat) : (x + y * z) % z = x % z := by
  rw [Nat.add_mul_mod_self_left]
  simp only [Nat.mul_mod_right_self]
  exact add_mod_right_eq_self

/- ACTUAL PROOF OF Nat.add_mul_mod_self_right -/

example (x y z : Nat) : (x + y * z) % z = x % z := by
  rw [Nat.mul_comm, add_mul_mod_self_left]