import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (n m k : Nat) : n * m * k = n * k * m := by
  rw [mul_left_comm n m k]
  rw [mul_left_comm n k m]

/- ACTUAL PROOF OF Nat.mul_right_comm -/

example (n m k : Nat) : n * m * k = n * k * m := by
  rw [Nat.mul_assoc, Nat.mul_comm m, ← Nat.mul_assoc]