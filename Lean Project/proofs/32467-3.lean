import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a m n : Nat) : a ^ (m * n) = (a ^ n) ^ m := by
  rw [← mul_comm n m]
  rw [← pow_mul]

/- ACTUAL PROOF OF Nat.pow_mul' -/

example (a m n : Nat) : a ^ (m * n) = (a ^ n) ^ m := by
  rw [← Nat.pow_mul, Nat.mul_comm]