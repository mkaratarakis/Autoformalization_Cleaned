import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (a0 : 0 < a) : b * a < c * a ↔ b < c := by
  constructor
  · intro h
    exact Nat.mul_lt_mul_left a0 h
  · intro h
    exact Nat.mul_lt_mul_left a0 h

/- ACTUAL PROOF OF Nat.mul_lt_mul_right -/

example (a0 : 0 < a) : b * a < c * a ↔ b < c := by
  rw [Nat.mul_comm b a, Nat.mul_comm c a, Nat.mul_lt_mul_left a0]