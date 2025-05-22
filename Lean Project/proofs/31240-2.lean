import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m : Nat) : n * pred m = n * m - n := by
  rw [Nat.mul_succ, Nat.sub_eq_add_neg, add_comm]
  rfl

/- ACTUAL PROOF OF Nat.mul_pred -/

example (n m : Nat) : n * pred m = n * m - n := by
  rw [Nat.mul_comm, pred_mul, Nat.mul_comm]