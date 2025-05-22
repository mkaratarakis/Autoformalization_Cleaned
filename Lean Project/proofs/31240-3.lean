import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m : Nat) : n * pred m = n * m - n := by
  rw [mul_succ, ←add_assoc, add_comm (n * m), add_tsub_cancel_right]
  rfl

/- ACTUAL PROOF OF Nat.mul_pred -/

example (n m : Nat) : n * pred m = n * m - n := by
  rw [Nat.mul_comm, pred_mul, Nat.mul_comm]