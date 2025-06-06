import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a m n : Nat) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [pow_pow]
  rw [pow_pow]
  rfl

/- ACTUAL PROOF OF Nat.pow_right_comm -/

example (a m n : Nat) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← Nat.pow_mul, Nat.pow_mul']