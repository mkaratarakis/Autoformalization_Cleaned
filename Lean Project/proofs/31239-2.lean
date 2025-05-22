import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m : Nat) : n * (m - 1) = n * m - n := by
  rw [mul_sub_right_distrib]
  rw [mul_comm m]

/- ACTUAL PROOF OF Nat.mul_sub_one -/

example (n m : Nat) : n * (m - 1) = n * m - n := by
  rw [Nat.mul_comm, Nat.sub_one_mul , Nat.mul_comm]