import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (m n : Nat) : (m * n) % m = 0 := by
  simp [Nat.mul_mod]

/- ACTUAL PROOF OF Nat.mul_mod_right -/

example (m n : Nat) : (m * n) % m = 0 := by
  rw [← Nat.zero_add (m * n), add_mul_mod_self_left, zero_mod]