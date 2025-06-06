import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [←mul_assoc (a * b) c d]
  rw [←mul_assoc a b (c * d)]
  rw [mul_left_comm (a * b) c]
  rw [mul_left_comm (a * c) b]
  rw [mul_assoc]

/- ACTUAL PROOF OF Nat.mul_mul_mul_comm -/

example (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm b]