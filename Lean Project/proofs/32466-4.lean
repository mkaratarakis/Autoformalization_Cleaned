import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a m n : Nat) : a ^ (m + n) = a ^ n * a ^ m := by
  rw [← pow_succ a n, mul_comm, ←pow_succ a m]
  rfl

/- ACTUAL PROOF OF Nat.pow_add' -/

example (a m n : Nat) : a ^ (m + n) = a ^ n * a ^ m := by
  rw [← Nat.pow_add, Nat.add_comm]