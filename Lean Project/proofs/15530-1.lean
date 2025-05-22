import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (a0 : 0 < a) : b * a < c * a ↔ b < c := by
  rw [mul_comm b a, mul_comm c a]
  have key : a * b < a * c ↔ b < c := mul_lt_mul_left a0
  rw [key]
  rfl

/- ACTUAL PROOF OF Nat.mul_lt_mul_right -/

example (a0 : 0 < a) : b * a < c * a ↔ b < c := by
  rw [Nat.mul_comm b a, Nat.mul_comm c a, Nat.mul_lt_mul_left a0]