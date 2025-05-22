import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (n m : Nat) : n * pred m = n * m - n := by
  rw [Nat.mul_comm, pred_mul, Nat.mul_comm]