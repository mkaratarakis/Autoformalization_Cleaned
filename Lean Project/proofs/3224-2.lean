import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (x y z : Nat) : (x + y * z) % y = x % y := by
  induction z with
  | zero =>
    simp
  | succ z' ih =>
    rw [Nat.mulSucc, Nat.add_assoc, Nat.add_comm (y * _), Nat.add_mod, ih]

/- ACTUAL PROOF OF Nat.add_mul_mod_self_left -/

example (x y z : Nat) : (x + y * z) % y = x % y := by
  match z with
  | 0 => rw [Nat.mul_zero, Nat.add_zero]
  | succ z => rw [mul_succ, ← Nat.add_assoc, add_mod_right, add_mul_mod_self_left (z := z)]