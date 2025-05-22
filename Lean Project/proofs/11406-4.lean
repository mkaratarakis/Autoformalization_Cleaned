import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat

example (m n : Nat) : gcd (n * m) n = n := by
  rw [gcd_comm]
  rw [gcd_mul_left]
  exact rfl

/- ACTUAL PROOF OF Nat.gcd_mul_right_left -/

example (m n : Nat) : gcd (n * m) n = n := by
  rw [Nat.mul_comm, gcd_mul_left_left]