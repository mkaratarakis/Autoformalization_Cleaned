import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m : Nat) : n * (m - 1) = n * m - n := by
  rw [mul_comm]
  rw [Nat.leftDistrib]
  rw [mul_comm]

/- ACTUAL PROOF OF Nat.mul_sub_one -/

example (n m : Nat) : n * (m - 1) = n * m - n := by
  rw [Nat.mul_comm, Nat.sub_one_mul , Nat.mul_comm]