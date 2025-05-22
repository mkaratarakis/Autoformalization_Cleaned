import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (z x y : Nat) : (x * z) % (y * z) = (x % y) * z := by
  rw [mul_comm z x, mul_comm z y]
  exact Nat.mul_mod' z x y

/- ACTUAL PROOF OF Nat.mul_mod_mul_right -/

example (z x y : Nat) : (x * z) % (y * z) = (x % y) * z := by
  rw [Nat.mul_comm x z, Nat.mul_comm y z, Nat.mul_comm (x % y) z]; apply mul_mod_mul_left