import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m : Nat) : n * (m - 1) = n * m - n := by
  rw [Nat.sub_eq_add_neg]
  rw [Nat.mul_add]
  rw [← Nat.add_sub_assoc]
  rw [Nat.sub_self]
  rw [Nat.zero_mul]
  rw [Nat.mul_comm]

/- ACTUAL PROOF OF Nat.mul_sub_one -/

example (n m : Nat) : n * (m - 1) = n * m - n := by
  rw [Nat.mul_comm, Nat.sub_one_mul , Nat.mul_comm]