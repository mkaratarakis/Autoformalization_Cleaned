import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m : Nat) : n * pred m = n * m - n := by
  rw [Nat.pred_eq_sub_one]
  rw [Nat.mul_sub_left_distrib]
  rw [Nat.one_mul]

/- ACTUAL PROOF OF Nat.mul_pred -/

example (n m : Nat) : n * pred m = n * m - n := by
  rw [Nat.mul_comm, pred_mul, Nat.mul_comm]