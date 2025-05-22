import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m : Nat) : n * pred m = n * m - n := by
  rw [mul_comm]
  rw [Nat.pred_mul]
  rw [mul_comm]

/- ACTUAL PROOF OF Nat.mul_pred -/

example (n m : Nat) : n * pred m = n * m - n := by
  rw [Nat.mul_comm, pred_mul, Nat.mul_comm]